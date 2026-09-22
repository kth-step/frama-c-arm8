open Cil_types
open Specification
(*
  To do a sound translation into ARMv8 we first translate it into an intermediate representation, simplfying it in the process.
*)

let node_to_term (ty : arm_type) (node : arm_term_node) : arm_term =
  { node; ty }

let type_to_signed (ty : arm_type) : bool =
  match ty with
  | AInt (signed, _) -> signed
  (* any* == uint64_t *)
  | APtr _ -> false
  (* We use infix operators here, so the same as signed *)
  | ABool -> true
  (* Void has no sign, and can not be used in operations *)
  | AVoid -> raise (ArmException "Void can not be used in binary operations")

(* Inner pointer type *)
let pointer_type (ptr : arm_type) : arm_type =
  match ptr with
  | APtr x -> x
  | _ -> raise (ArmException "This type is not a pointer")

let size_of (ty : arm_type) : arm_word_size =
  match ty with
  | APtr _ -> Word64
  | AInt (_, x) -> x
  | AVoid -> raise (ArmException "This type is void, and does not have a size")
  | ABool ->
      raise (ArmException "This type is a bool, and does not have a size")

let int_to_arm_node (x : int) : arm_term_node =
  AConst (AInteger (Int.to_string x))

let int_to_arm (x : int) : arm_term =
  node_to_term (AInt (x < 0, Word64)) (int_to_arm_node x)

let var_to_arm (x : string) = ALval (AVar x)

let ikind_to_arm (kind : ikind) : arm_type =
  match kind with
  | IBool | IUChar | IChar -> AInt (false, Word8)
  | ISChar -> AInt (true, Word8)
  | IUShort -> AInt (false, Word16)
  | IShort -> AInt (true, Word16)
  | IUInt -> AInt (false, Word32)
  | IInt -> AInt (true, Word32)
  | IULong | IULongLong -> AInt (false, Word64)
  | ILong | ILongLong -> AInt (true, Word64)
  | IUInt128 | IInt128 -> raise (ArmException "128-bit words are not supported by ARM")

let rec typ_to_arm (typ : typ) : arm_type =
  match typ.tnode with
  | TVoid -> AVoid
  | TPtr typ -> APtr (typ_to_arm typ)
  | TInt x -> ikind_to_arm x
  | TEnum enum -> ikind_to_arm enum.ekind
  | TNamed info -> typ_to_arm info.ttype
  | TFloat _ ->
      raise (ArmException "Floating point numbers are not supported by L3")
  | TFun _ -> raise (ArmException "Functions are not supported")
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown typ_to_arm %s" (pp_spec Printer.pp_typ typ)))

let logic_type_to_arm (logic_type : logic_type) : arm_type =
  match logic_type with
  | Ctype typ -> typ_to_arm typ
  | Lboolean -> ABool
  | Linteger -> AInt (true, Word64)
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown logic_type_to_arm in type '%s'"
              (pp_spec Printer.pp_logic_type logic_type)))

let typ_to_size (typ : typ) = typ |> typ_to_arm |> size_of

let logic_type_to_size (logic_type : logic_type) =
  match logic_type with
  | Ctype typ -> typ_to_size typ
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown logic_type_to_size in type '%s'"
              (pp_spec Printer.pp_logic_type logic_type)))

let word_to_bytes (size : arm_word_size) : int =
  match size with Word8 -> 1 | Word16 -> 2 | Word32 -> 4 | Word64 -> 8

let word_to_bits (size : arm_word_size) : int =
  size |> word_to_bytes |> fun x -> x * 8

let logic_type_to_bytes (logic_type : logic_type) : int =
  logic_type_to_size logic_type |> word_to_bytes

let typ_to_bytes (typ : typ) : int = typ_to_size typ |> word_to_bytes

let rec term_to_arm (env : arm_enviroment) (term : term) : arm_term =
  (* Keep the same type as the Frama-C AST *)
  (*print_string
    (Format.sprintf "term_to_arm (%s : %s) \n"
       (pp_spec Printer.pp_term term)
       (pp_spec pp_logic_type2 term.term_type));*)
  node_to_term
    (logic_type_to_arm term.term_type)
    (match term.term_node with
    | TConst logical -> logical_to_arm env logical
    | TBinOp (op, lhs, rhs) -> binop_to_arm env op lhs rhs
    | TUnOp (op, inner_term) ->
        (*print_string
          (Format.sprintf "unop (%s -> %s) %s\n"
             (pp_spec pp_logic_type2 t.term_type)
             (pp_spec pp_logic_type2 term.term_type)
             (pp_spec Printer.pp_term term));*)

        (* 
          Unexpected implcit cast? Is this a bug in Frama-C or are unops supposed to convert the type?
          This is treated as ~(Z)T instead of (Z)~T. It is very weird.
        *)
        AUnOp
          ( op,
            cast_to_arm_term env
              (logic_type_to_arm inner_term.term_type)
              (logic_type_to_arm term.term_type)
              (term_to_arm env inner_term) )
    | TLval (host, offset) -> l_value_to_arm env host offset
    | Tat (t, label) -> at_to_arm env t label
    | Tif (t1, t2, t3) ->
        Aif (term_to_arm env t1, term_to_arm env t2, term_to_arm env t3)
    (* Align and sizeof is the same on ARMv8 for primative types *)
    | TSizeOf typ | TAlignOf typ -> typ |> typ_to_bytes |> int_to_arm_node
    | TAddrOf (host, offset) -> address_of_l_value env host offset
    | Tlet (x, t) ->
        (let_term env x (fun local_env -> term_to_arm local_env t)).node
    (* a shortcut for (void ptr)0 *)
    | Tnull -> int_to_arm_node 0
    | TCast (is_implicit_conversion, convert_to_type, term) ->
        cast_to_arm env is_implicit_conversion convert_to_type term
    | Tapp (info, _logical_label_list, term_list) -> (
        (* Just eval *)
        match info.l_body with
        | LBterm t ->
            let mapped_terms =
              List.map (fun term -> term_to_arm env term) term_list
            in
            List.iter2
              (fun profile term ->
                Hashtbl.add env.variables profile.lv_name (env.at, term.node))
              info.l_profile mapped_terms;
            (* Add let bindings *)
            let eval = (term_to_arm env t).node in
            List.iter
              (fun profile -> Hashtbl.remove env.variables profile.lv_name)
              info.l_profile;
            (* Remove let bindings *)
            eval
        | LBnone ->
            let fn =
              match info.l_var_info.lv_name with
              | "\\abs" -> AAbs
              | "\\min" -> AMin
              | "\\max" -> AMax
              (*| "pow" -> APow *)
              | _ ->
                  raise
                    (ArmException
                       (Format.sprintf
                          "Unable to use built-in applications like %s"
                          info.l_var_info.lv_name))
            in
            let mapped_terms =
              List.map (fun term -> term_to_arm env term) term_list
            in
            ABuiltin (fn, mapped_terms)
        | _ ->
            raise
              (ArmException
                 (Format.sprintf "Unable to translate application %s"
                    (pp_spec Printer.pp_logic_info info))))
    | _ ->
        raise
          (ArmException
             (Format.sprintf "Unknown term_to_arm %s : %s"
                (pp_spec Printer.pp_term term)
                (pp_spec Printer.pp_logic_type term.term_type))))

and address_of_l_value (_env : arm_enviroment) (lhost : term_lhost)
    (offset : term_offset) : arm_term_node =
  if offset != TNoOffset then raise (ArmException "Unsupported index operation")
  else
    match lhost with
    | TMem term ->
        raise
          (ArmException
             (Format.sprintf "Unknown address_of_l_value %s"
                (pp_spec Printer.pp_term term)))
        (*term_to_arm env term*)
    | _ -> raise (ArmException "Unsupported address of lvalue")

and binop_to_arm (env : arm_enviroment) (op : binop) (lhs : term) (rhs : term) :
    arm_term_node =
  let lhs_t = term_to_arm env lhs in
  let rhs_t = term_to_arm env rhs in

  match op with
  | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr ->
      (* For basic ops we can just do the trivial operations *)
      let inner_op =
        match op with
        | Lt -> ALe
        | Gt -> AGt
        | Le -> ALe
        | Ge -> AGe
        | Eq -> AEq
        | Ne -> ANe
        | LAnd -> ALAnd
        | LOr -> ALOr
        | _ ->
            raise
              (ArmException
                 "binop_to_arm inner op does not exist, this should never \
                  happend")
      in
      ABinOp (inner_op, lhs_t, rhs_t)
  | Mod | Div | Mult | PlusA | MinusA | Shiftlt | Shiftrt | BAnd | BOr | BXor ->
      (* For basic ops we can just do the trivial operations *)
      let inner_op =
        match op with
        | Div -> ADiv
        | Mod -> AMod
        | Mult -> AMult
        | PlusA -> APlusA
        | MinusA -> AMinusA
        | Shiftlt -> AShiftlt
        | Shiftrt -> AShiftrt
        | BAnd -> ABAnd
        | BXor -> ABXor
        | BOr -> ABOr
        | _ ->
            raise
              (ArmException
                 "binop_to_arm inner op does not exist, this should never \
                  happend")
      in
      ABinOp (inner_op, lhs_t, rhs_t)
  (* Adding an integer to a pointer is the equavalent of (uint64_t)lhs + (int64_t)rhs*size_of( *lhs ) *)
  | PlusPI | MinusPI ->
      let inner_op =
        match op with
        | PlusPI -> APlusA
        | MinusPI -> AMinusA
        | _ ->
            raise
              (ArmException
                 "binop_to_arm inner op does not exist, this should never \
                  happend")
      in

      (* Keep the outer pointer type *)
      let ty = lhs.term_type |> logic_type_to_arm |> pointer_type in
      ABinOp
        ( inner_op,
          lhs_t,
          node_to_term ty
            (ABinOp
               ( AMult,
                 (* cast to int64 before the mul, as lhs and rhs must both be int64 *)
                 cast_to_arm_term env rhs_t.ty (AInt (true, Word64)) rhs_t,
                 ty |> size_of |> word_to_bytes |> int_to_arm )) )
  | MinusPP ->
      (* a - b means, how many items they are apart, not bytes. So we represent that with `((uint64_t)a-(uint64_t)b) / sizeof( *a )` *)
      let ty = pointer_type lhs_t.ty in

      ABinOp
        ( ADiv,
          node_to_term (AInt (false, Word64)) (ABinOp (AMinusA, lhs_t, rhs_t)),
          ty |> size_of |> word_to_bytes |> int_to_arm )
(*| _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown binary operator '%s'"
              (pp_spec Printer.pp_binop op)))*)

and at_to_arm (env : arm_enviroment) (term : term) (label : logic_label) :
    arm_term_node =
  match label with
  (* This allows old even in the "requires part", however wp will generate an error as "old undefined in this context" *)
  | BuiltinLabel Old -> env_old env term
  | _ -> raise (ArmException "Unknown label in at_to_arm")

and pp_logic_type2 (fmt : Format.formatter) (logic_type : logic_type) =
  match logic_type with
  (* We use this instead of pp_logic_type as it uses unicode characters, which is hard to read in exceptions*)
  | Linteger -> Format.pp_print_string fmt "integer"
  | Lboolean -> Format.pp_print_string fmt "boolean"
  | _ -> Printer.pp_logic_type fmt logic_type

and cast_to_arm (env : arm_enviroment) (_is_implicit_conversion : bool)
    (convert_to_type : logic_type) (term : term) : arm_term_node =
  let to_ty = logic_type_to_arm convert_to_type in
  let from_ty = logic_type_to_arm term.term_type in
  let arm_term = term_to_arm env term in
  (*print_string
    (Format.sprintf "cast (%s -> %s) %s implcit=%b\n"
       (pp_spec pp_logic_type2 term.term_type)
       (pp_spec pp_logic_type2 convert_to_type)
       (pp_spec Printer.pp_term term)
       _is_implicit_conversion);*)
  (cast_to_arm_term env from_ty to_ty arm_term).node

and cast_to_arm_term (_env : arm_enviroment) (from_ty : arm_type)
    (to_ty : arm_type) (arm_term : arm_term) : arm_term =
  let node =
    match (from_ty, to_ty) with
    | AVoid, _ | _, AVoid ->
        raise (ArmException "Unable to cast to of from a void type")
    (* No need to do any complicated math here when chaning the sign, as this is equivalent to transmute if the size is the same *)
    | AInt (_, Word32), AInt (_, Word32)
    | AInt (_, Word16), AInt (_, Word16)
    | AInt (_, Word8), AInt (_, Word8)
    | AInt (_, Word64), AInt (_, Word64)
    (* Same size so transmute *)
    | APtr _, APtr _
    | ABool, ABool
    | APtr _, AInt (_, Word64)
    | AInt (_, Word64), APtr _ ->
        arm_term.node
    (* Sign extend signed numbers *)
    | AInt (true, from_size), AInt (_, to_size) ->
        if word_to_bytes from_size < word_to_bytes to_size then
          ACast (ASignExtend, to_size, arm_term)
        else ACast (AExtract, to_size, arm_term)
    (* Zero extend unsigned numbers *)
    | AInt (false, from_size), AInt (_, to_size) ->
        if word_to_bytes from_size < word_to_bytes to_size then
          ACast (AZeroExtend, to_size, arm_term)
        else ACast (AExtract, to_size, arm_term)
    (* if b then 1 else 0 *)
    | ABool, AInt _ ->
        Aif
          ( arm_term,
            1 |> int_to_arm_node |> node_to_term to_ty,
            0 |> int_to_arm_node |> node_to_term to_ty )
    (* ptr -> int just extracts the lower bits *)
    | APtr _, AInt (_, to_size) -> ACast (AExtract, to_size, arm_term)
    (* Sign extend signed numbers to a pointer, this is the C semantics *)
    | AInt (true, _), APtr _ -> ACast (ASignExtend, Word64, arm_term)
    (* Zero extend unsigned numbers to a pointer, this is the C semantics *)
    | AInt (false, _), APtr _ -> ACast (AZeroExtend, Word64, arm_term)
    (* This is done by frama-c, but we detail the semantics here as well *)
    | AInt _, ABool | APtr _, ABool ->
        (* ptr/int != nullptr/0 *)
        ABinOp (ANe, arm_term, 0 |> int_to_arm_node |> node_to_term from_ty)
    (* It makes no sense to cast a boolean to a pointer, frama-c errors on this *)
    | ABool, APtr _ ->
        raise
          (ArmException
             "A cast from a boolean to a ptr is not allowed, and does not make \
              sense")
  in
  node_to_term to_ty node
(*| _ ->
      raise
        (ArmException
           (Format.sprintf "Unable to cast %s to %s"
              (pp_spec pp_logic_type2 term.term_type)
              (pp_spec pp_logic_type2 convert_to_type)))*)

and logic_var_to_arm (env : arm_enviroment) (lvar : logic_var) : arm_term_node =
  match Hashtbl.find_opt env.variables lvar.lv_name with
  | None ->
      raise
        (ArmException
           (Printf.sprintf
              "Variable %s not found, global variables are unsupported. Use \
               -arm8-global to generate a scaffold"
              lvar.lv_name))
  | Some (location, out) -> (
      (* *&x can smuggle variables into the post-state, we need to check that we are in an \old state to do this! *)
      match (env.at, location) with
      | Post, Pre ->
          raise
            (ArmException
               "Unable to refer to variables declared in the pre-condition \
                when in the post-condition")
      (* The other way around is fine, as \let x; \old(x + 1) is fine. *)
      | _ -> out)

and l_value_to_arm (env : arm_enviroment) (lhost : term_lhost)
    (offset : term_offset) : arm_term_node =
  if offset != TNoOffset then raise (ArmException "Unsupported index operation")
  else
    match lhost with
    | TVar logical_var -> logic_var_to_arm env logical_var
    | TMem term ->
        ALval
          (AMemory
             ( term_to_arm env term,
               term.term_type |> logic_type_to_arm |> pointer_type |> size_of ))
    (* We can be sure this is only in a post-context as otherwise you will get "\result meaningless" error from wp *)
    | TResult typ -> ALval (ARegister (0, typ_to_size typ))

(* Puts the term into enviroment old, and returns the bound variable *)
and env_old (env : arm_enviroment) (term : term) : arm_term_node =
  let old_env = env.at in
  env.at <- Pre;
  let t = term_to_arm env term in
  env.at <- old_env;

  (*
    We dedup on terms, so we do not fill it up with the same argument all the time, 
    as frama-c automaticlly transforms `x` to `\old(x)` if x is an argument. 
    We can assume that the eval to the same type if the have the same AST.

    If we need perf then just make this into a hashmap.
  *)
  match
    List.find_opt
      (fun (name, term) -> term.node = t.node || t.node = ALval (AVar name))
      env.old
  with
  | Some (name, _) -> var_to_arm name
  | None ->
      let length = List.length env.old in

      (* If this operation is just a single deref of an old variable, then label it as $_deref to make it more readable*)
      let name =
        match t.node with
        | ALval (AMemory (deref_term, _deref_size)) -> (
            match deref_term.node with
            | ALval (AVar inner_name) -> Printf.sprintf "%s_deref" inner_name
            | _ -> Printf.sprintf "old_%d" length)
        | _ -> Printf.sprintf "old_%d" length
      in

      env.old <- (name, t) :: env.old;
      var_to_arm name

and logical_to_arm (_ : arm_enviroment) (logical : logic_constant) :
    arm_term_node =
  match logical with
  | Boolean b -> AConst (ABoolean b)
  | Integer (i, _) -> AConst (AInteger (Z.to_string i))
  | LEnum item -> (
      match item.eival.enode with
      | Const (CInt64 (value, _, _)) -> AConst (AInteger (Z.to_string value))
      | _ -> raise (ArmException "Invalid enum value"))
  | _ -> raise (ArmException "Unknown logical_to_arm")

(* TODO support -absolute-valid-range for a range of supported values instead of HOL *)
(* TODO valid range as, "ACSL built-in predicate \valid (p) is now equivalent to \validrange (p,0,0)." *)
and valid_to_arm (env : arm_enviroment) (label : logic_label) (term : term) :
    arm_predicate =
  match label with
  | StmtLabel _ -> raise (ArmException "\\valid is not supported with C labels")
  | FormalLabel _ ->
      raise (ArmException "\\valid is not supported with global annotations")
  | BuiltinLabel Here -> (
      (* Hardcode a match for the very common \valid(p+(a..b)) *)
      match term.term_node with
      | TBinOp
          ( PlusPI,
            ptr,
            {
              term_node = Trange (Some range_start, Some range_end);
              term_loc = _;
              term_type = _;
              term_name = _;
            } ) ->
          let base_ptr = term_to_arm env ptr in
          let arm_range_start =
            binop_to_arm env PlusPI ptr range_start |> node_to_term base_ptr.ty
          in
          let arm_range_end =
            binop_to_arm env PlusPI ptr range_end |> node_to_term base_ptr.ty
          in

          (* 0x20000 <= (p+a) && (p+b) < 0x100000000 && p % size_of(p) == 0 *)
          Aand
            ( Aand
                ( Arel (Rle, int_to_arm 0x20000, arm_range_start),
                  Arel (Rlt, arm_range_end, int_to_arm 0x100000000) ),
              Arel
                ( Req,
                  (* Keep the type*)
                  node_to_term base_ptr.ty
                    (ABinOp
                       ( AMod,
                         base_ptr,
                         int_to_arm (base_ptr.ty |> size_of |> word_to_bytes) )),
                  int_to_arm 0 ) )
      | _ ->
          let arm_term = term_to_arm env term in

          (* The nullcheck is for "\valid{L}((char ptr)\null) and \valid_read{L}((char ptr)\null) are always false, forany logic label L"*)
          (* The mod check is for aligment for armv8, technically frama-c have the \aligned keyword, but for armv8 "safely dereferenced" means it must be aligned *)

          (*
        This is the same is HOL, but they check that the lower 3 bits are 0.

        adress bitwise-and 0b111 = 0
         ``^var_tm && 7w = 0w /\ ^prog_addr_max_tm <=+ ^var_tm /\ ^var_tm <+ ^mem_addr_bound_tm``

        where

        val prog_addr_max_tm = ``0x20000w:word64``;
        val mem_addr_bound_tm = ``0x100000000w:word64``;
      *)
          Aand
            ( Aand
                ( Arel (Rle, int_to_arm 0x20000, arm_term),
                  Arel (Rlt, arm_term, int_to_arm 0x100000000) ),
              Arel
                ( Req,
                  (* Keep the type*)
                  node_to_term arm_term.ty
                    (ABinOp
                       ( AMod,
                         arm_term,
                         int_to_arm (arm_term.ty |> size_of |> word_to_bytes) )),
                  int_to_arm 0 ) ))
  | BuiltinLabel _ ->
      raise
        (ArmException
           "\\valid is not supported with logic labels other than 'here'")

and predicate_to_arm (env : arm_enviroment) (predicate : predicate) :
    arm_predicate =
  match predicate.pred_content with
  | Pfalse -> Afalse
  | Ptrue -> Atrue
  | Piff (p1, p2) -> Aiff (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pand (p1, p2) -> Aand (predicate_to_arm env p1, predicate_to_arm env p2)
  | Por (p1, p2) -> Aor (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pimplies (p1, p2) ->
      Aimplies (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pxor (p1, p2) -> Axor (predicate_to_arm env p1, predicate_to_arm env p2)
  | Pnot p -> Anot (predicate_to_arm env p)
  | Pif (c, p1, p2) ->
      Aif (term_to_arm env c, predicate_to_arm env p1, predicate_to_arm env p2)
  | Plet (x, p) ->
      let_predicate env x (fun local_env -> predicate_to_arm local_env p)
  | Paligned (t1, t2) ->
      Arel
        ( Req,
          node_to_term
            (logic_type_to_arm t1.term_type)
            (ABinOp (AMod, term_to_arm env t1, term_to_arm env t2)),
          0 |> int_to_arm_node |> node_to_term (logic_type_to_arm t1.term_type)
        )
      (* Even if valid_read != valid, for our purposes it is equivalent as we have no restrictions on write/read *)
  | Pvalid (label, t) | Pvalid_read (label, t) -> valid_to_arm env label t
  | Prel (rel, t1, t2) -> (
      (*print_string
    (Format.sprintf "Arel (%s : %s) (%s : %s) \n"
       (pp_spec Printer.pp_term t1)
       (pp_spec pp_logic_type2 t1.term_type)
       (pp_spec Printer.pp_term t2)
       (pp_spec pp_logic_type2 t2.term_type));*)
      let t1_type = logic_type_to_arm t1.term_type in
      let t2_type = logic_type_to_arm t2.term_type in

      if t1_type = t2_type then
        Arel (rel, term_to_arm env t1, term_to_arm env t2)
      else
        (* I have no idea why, but frama-c *can* generate an ast where the lhs and rhs have different types, 
           aka not cast to Z? Is this a bug in frama-c? *)
        match (t1_type, t2_type) with
        | AInt _, AInt _ ->
            (* Cast both to int64_t *)
            Arel
              ( rel,
                term_to_arm env t1
                |> cast_to_arm_term env t1_type (AInt (true, Word64)),
                term_to_arm env t2
                |> cast_to_arm_term env t2_type (AInt (true, Word64)) )
        | _ ->
            raise
              (ArmException
                 (Format.sprintf
                    "Relation predicate with incomparable types (%s : %s) (%s \
                     : %s)"
                    (pp_spec Printer.pp_term t1)
                    (pp_spec pp_logic_type2 t1.term_type)
                    (pp_spec Printer.pp_term t2)
                    (pp_spec pp_logic_type2 t2.term_type))))
  | Papp (info, _logical_label_list, term_list) -> (
      match info.l_body with
      | LBpred t ->
          let mapped_terms =
            List.map (fun term -> term_to_arm env term) term_list
          in
          List.iter2
            (fun profile term ->
              Hashtbl.add env.variables profile.lv_name (env.at, term.node))
            info.l_profile mapped_terms;
          (* Add let bindings *)
          let eval = predicate_to_arm env t in
          List.iter
            (fun profile -> Hashtbl.remove env.variables profile.lv_name)
            info.l_profile;
          (* Remove let bindings *)
          eval
      | _ ->
          raise
            (ArmException
               (Format.sprintf "Unable to translate applications like %s"
                  (pp_spec Printer.pp_logic_info info))))
  | Pseparated term_list ->
      let arm_term_list = List.map (term_to_arm env) term_list in
      (* Triangle cross product, e.g. [a,b,c] * [a,b,c] = [(a,b),(a,c),(b,c)] *)
      let paris =
        List.mapi
          (fun index left ->
            List.drop (index + 1) arm_term_list
            |> List.map (fun right -> (left, right)))
          arm_term_list
        |> List.flatten
      in
      List.fold_left
        (fun acc (l, r) -> Aand (acc, Arel (Rneq, l, r)))
        Atrue paris
  | x ->
      raise
        (ArmException
           (Format.sprintf "Unknown predicate_to_arm_predicate %s"
              (pp_spec Printer.pp_predicate_node x)))

and let_predicate (env : arm_enviroment) (info : logic_info)
    (fn : arm_enviroment -> arm_predicate) : arm_predicate =
  match info.l_body with
  (* 
    Adds the let variable in the local enviroment, and then removes it. 
    Hashtbl automaticlly shadows the variable in case of duplicates 
  *)
  | LBpred predicate ->
      let arm_predicate = predicate_to_arm env predicate in
      Hashtbl.add env.predicates info.l_var_info.lv_name arm_predicate;
      let (result : 'a) = fn env in
      Hashtbl.remove env.predicates info.l_var_info.lv_name;
      result
  | LBterm term ->
      let arm_term = term_to_arm env term in
      Hashtbl.add env.variables info.l_var_info.lv_name (env.at, arm_term.node);
      let result = fn env in
      Hashtbl.remove env.variables info.l_var_info.lv_name;
      result
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown let_predicate %s"
              (pp_spec Printer.pp_logic_info info)))

(* Generics for higher order functions are weird, so I have to duplicate it *)
and let_term (env : arm_enviroment) (info : logic_info)
    (fn : arm_enviroment -> arm_term) : arm_term =
  match info.l_body with
  | LBterm term ->
      let arm_term = term_to_arm env term in
      Hashtbl.add env.variables info.l_var_info.lv_name (env.at, arm_term.node);
      let result = fn env in
      Hashtbl.remove env.variables info.l_var_info.lv_name;
      result
  | _ ->
      raise
        (ArmException
           (Format.sprintf "Unknown let_term %s"
              (pp_spec Printer.pp_logic_info info)))

(* Fold list acsl predicates into a single arm predicate using and *)
let identified_predicate_list_to_arm (env : arm_enviroment)
    (list : identified_predicate list) : arm_predicate =
  List.fold_left
    (fun acc_p item ->
      let item_p = predicate_to_arm env item.ip_content.tp_statement in
      Aand (acc_p, item_p))
    Atrue list

let behavior_to_arm (env : arm_enviroment) (fn : funbehavior) : arm_contract =
  env.at <- Post;
  let ensures =
    (* Only take the "Normal" termination_kind, as we only want \ensures on normal, not \exists  *)
    List.filter (fun (x, _) -> x == Normal) fn.b_post_cond
    |> List.map (fun (_term, item) -> item)
    |> identified_predicate_list_to_arm env
  in
  env.at <- Pre;
  let requires = identified_predicate_list_to_arm env fn.b_requires in

  {
    (* todo termination with termination_kind? *)
    ensures;
    requires;
    enviroment = env;
  }

let argument_to_arm (index : int) (size : arm_word_size) : arm_term_node =
  ALval
    (* First 8 are passed in the registers x0-x7 *)
    (if index < 8 then
       (* REG(s, i) *)
       ARegister (index, size)
     else
       (* MEM(s, SP + (i - 8), size) *)
       AMemory
         ( node_to_term
             (AInt (false, Word64))
             (ABinOp
                ( APlusA,
                  node_to_term (AInt (false, Word64)) SP,
                  int_to_arm ((index - 8) * 8) )),
           size ))

(* C-Name, Arm-Name, Arm-Term *)
let varinfo_to_old (index : int) (varinfo : varinfo) :
    string * arm_logic_var * arm_term =
  let size = typ_to_size varinfo.vtype in
  ( varinfo.vorig_name,
    Format.sprintf "pre_x%d" index,
    node_to_term (typ_to_arm varinfo.vtype) (argument_to_arm index size) )

let fn_vars_to_old (args : varinfo list) :
    (arm_logic_var * string * arm_term) list =
  List.rev (List.mapi varinfo_to_old args)

let sformals_to_env (source : arm_translation_source) : arm_enviroment =
  let arguments = fn_vars_to_old source.fn.sformals in
  let table = Hashtbl.create (List.length arguments) in

  (* Dirty hack where you have to manually add the global variables as a user define "variable" *)
  List.iter
    (fun (variable, _) ->
      Hashtbl.add table variable.vorig_name
        (Post, ALval (AVar (Format.sprintf "global_%s" variable.vorig_name))))
    source.globals;

  (* All variables are substituted like "Contract-Based Verification in TriCera" *)
  (* This maps c_name -> arm_name to make it easier to read than inserting the value directly, this is because we do arm_name = value with old *)
  List.iter
    (fun (c_name, arm_name, _value) ->
      Hashtbl.add table c_name (Pre, ALval (AVar arm_name)))
    arguments;

  {
    variables = table;
    predicates = Hashtbl.create 0;
    (* Maps all arm_name -> value to be inserted as top level bindings *)
    old =
      List.map (fun (_c_name, arm_name, value) -> (arm_name, value)) arguments;
    at = Pre;
  }

let fn_to_arm (source : arm_translation_source) : arm_contract =
  let kf = Globals.Functions.get source.fn.svar in
  (* By default this is complete as it merges every behavior *)
  let behaviors = Annotations.behaviors kf in
  let (env : arm_enviroment) = sformals_to_env source in

  behaviors
  |> List.filter (fun x -> x.b_assumes |> List.is_empty |> not)
  |> List.iter (fun x ->
      Kernel.warning
        "Unsupported assumes clause in function '%s', using 'assumes \\true' instead"
        x.b_name);

  let contract =
    List.fold_left
      (fun acc_contract item ->
        let contract = behavior_to_arm env item in
        {
          ensures = Aand (contract.ensures, acc_contract.ensures);
          requires = Aand (contract.requires, acc_contract.requires);
          enviroment = contract.enviroment;
        })
        (*
        Missing requires and ensures clauses default to \true
        Missing exits clauses default to \false.
        If no assigns clause is given, it remains unspecified
        *)
      { ensures = Atrue; requires = Atrue; enviroment = env }
      behaviors
  in
  {
    (* Simpliy away the Aand(predicate, Atrue) from folding *)
    ensures = simplify contract.ensures;
    requires = simplify contract.requires;
    enviroment = env;
  }
