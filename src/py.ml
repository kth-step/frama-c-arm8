open Specification
open Translation
open Cil_types

type contract_printer = { fmt : Format.formatter }
(*
  Intermediate representation -> python z3 code for testing
*)

(* Returns the predicate to check if a term contains overflow *)
(*let rec no_overflow_of_term (term : term) : arm_predicate =
  match term.term_node with
  | TConst _ -> Atrue
  | TLval (_, _) -> Atrue (* TODO FIX *)
  | Tat (term, _) -> no_overflow_of_term term (* TODO FIX OLD *)
  | TCast (_, _, term) -> no_overflow_of_term term
  | TBinOp (op, lhs, rhs) ->
      Aand
        ( Aand (no_overflow_of_term lhs, no_overflow_of_term rhs),
          match op with
          | PlusA -> Aoverflow (Oadd, lhs, rhs)
          | MinusA -> Aoverflow (Osub, lhs, rhs)
          | Mult -> Aoverflow (Omul, lhs, rhs)
          | Div -> Aoverflow (Odiv, lhs, rhs)
          | _ -> raise (ArmException "Unknown no_overflow_of_term") )
  | _ -> raise (ArmException "Unknown no_overflow_of_term")
*)

(*
  
  | TLval (host, offset) -> pp_arm_lvalue out host offset
  | Tat (term, label) -> pp_arm_at out old term label
  | TCast (_is_implicit_conversion, _convert_to_type, term) 
  *)

(* TODO overflow? *)
let pp_arm_logical_constant (out : contract_printer)
    (constant : arm_logic_constant) =
  match constant with
  | ABoolean true -> Format.fprintf out.fmt "True"
  | ABoolean false -> Format.fprintf out.fmt "False"
  | AInteger z -> Format.fprintf out.fmt "%s" z

let pp_logic_var (out : contract_printer) (var : arm_logic_var) =
  Format.fprintf out.fmt "%s" var

let rec pp_arm_lvalue (out : contract_printer) (host : arm_term_lhost) =
  match host with
  | AVar v -> pp_logic_var out v
  | ARegister (at, size) ->
      (* To simulate reading w0 or lower we extract the lower bits *)
      pp_arm_cast_fn out AExtract size Word64 (fun local_out ->
          Format.fprintf local_out.fmt "REG[%d]" at)
  | AMemory (at, size) ->
      (* To simulate a smaller read we extract the lower bits *)
      pp_arm_cast_fn out AExtract size Word64 (fun local_out ->
          Format.fprintf local_out.fmt "MEM[";
          pp_arm_term local_out at;
          Format.fprintf local_out.fmt "]")

and pp_arm_unop (out : contract_printer) (op : arm_unop) (term : arm_term) :
    unit =
  let prefix = match op with BNot -> "~" | LNot -> "!" | Neg -> "-" in
  Format.fprintf out.fmt "%s" prefix;
  pp_arm_term out term

and pp_arm_cast_fn (out : contract_printer) (cast : arm_cast)
    (to_size : arm_word_size) (from_size : arm_word_size)
    (printer : contract_printer -> unit) : unit =
  let to_bits = word_to_bits to_size in
  let from_bits = word_to_bits from_size in

  if from_bits = to_bits then printer out
  else
    let additional_bits = to_bits - from_bits in
    (match cast with
    | AExtract ->
        Format.fprintf out.fmt "Extract(%d, 0, " (to_bits - 1)
        (* Extract is inclusive *)
    | ASignExtend -> Format.fprintf out.fmt "SignExt(%d, " additional_bits
    | AZeroExtend -> Format.fprintf out.fmt "ZeroExt(%d, " additional_bits);
    printer out;
    Format.fprintf out.fmt ")"

and pp_arm_cast (out : contract_printer) (cast : arm_cast)
    (to_size : arm_word_size) (from_size : arm_word_size) (node : arm_term_node)
    : unit =
  pp_arm_cast_fn out cast to_size from_size (fun local_out ->
      pp_arm_term_node local_out node)

and pp_arm_binop (out : contract_printer) (op : arm_binop) (lhs : arm_term)
    (rhs : arm_term) : unit =
  let infix =
    match op with
    | APlusA -> "+"
    | AMinusA -> "-"
    | AMult -> "*"
    | ADiv -> "/"
    | AMod -> "%"
    | AEq -> "=="
    | ANe -> "!="
    | ALOr -> "or"
    | ALAnd -> "and"
    | ABAnd -> "&"
    | ABOr -> "|"
    | ABXor -> "^"
    | AShiftlt -> "<<"
    | AShiftrt -> ">>"
    (* Todo signed ? *)
    | ALt -> "<"
    | AGt -> ">"
    | AGe -> ">="
    | ALe -> "<="
  in

  Format.fprintf out.fmt "(";
  pp_arm_term out lhs;
  Format.fprintf out.fmt " %s " infix;
  pp_arm_term out rhs;
  Format.fprintf out.fmt ")"

and pp_arm_term_node (out : contract_printer) (node : arm_term_node) =
  match node with
  | AConst logical -> pp_arm_logical_constant out logical
  | ABinOp (op, lhs, rhs) -> pp_arm_binop out op lhs rhs
  | ALval host -> pp_arm_lvalue out host
  | SP -> Format.fprintf out.fmt "SP"
  | AUnOp (op, term) -> pp_arm_unop out op term
  | ABuiltin (_, _) ->
      raise
        (ArmException (Format.sprintf "Unable to translate builtin application"))
  | ACast (cast, size, term) ->
      pp_arm_cast out cast size (size_of term.ty) term.node
  | Aif (c, t1, t2) ->
      let fmt = out.fmt in
      Format.fprintf fmt "If(";
      pp_arm_predicate out c;
      Format.fprintf fmt ", ";
      pp_arm_term out t1;
      Format.fprintf fmt ", ";
      pp_arm_term out t2;
      Format.fprintf fmt ")"

and pp_arm_term (out : contract_printer) (term : arm_term) =
  pp_arm_term_node out term.node

(*| _ ->
      (*Format.fprintf out.fmt "<<<<";
      Printer.pp_term out.fmt term;
      Format.fprintf out.fmt
        ">>>>"*)
      raise (ArmException "Unknown pp_arm_term")*)

and pp_no_overflow (out : contract_printer) (o : no_overflow_type)
    (lhs : arm_term) (rhs : arm_term) =
  let prefix =
    match o with
    | Osub -> "BVSubNoOverflow"
    | Oadd -> "BVAddNoOverflow"
    | Omul -> "BVMulNoOverflow"
    | Odiv -> "BVSDivNoOverflow"
  in

  let suffix = match o with Osub | Oadd | Omul -> ", True" | Odiv -> "" in
  Format.fprintf out.fmt "%s(" prefix;
  pp_arm_term out lhs;
  Format.fprintf out.fmt ", ";
  pp_arm_term out rhs;
  Format.fprintf out.fmt "%s)" suffix

and pp_arm_predicate (out : contract_printer) (predicate : arm_predicate) =
  let fmt = out.fmt in
  match predicate with
  (*| Aunknown -> Format.fprintf fmt "FreshBool()"*)
  | Aiff (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " == ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aif (c, t1, t2) ->
      Format.fprintf fmt "If(";
      pp_arm_predicate out c;
      Format.fprintf fmt ", ";
      pp_arm_predicate out t1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out t2;
      Format.fprintf fmt ")"
  (*| Aoverflow (o, lhs, rhs) -> pp_no_overflow out o lhs rhs*)
  | Afalse -> Format.fprintf fmt "False"
  | Atrue -> Format.fprintf fmt "True"
  | Aand (p1, p2) ->
      Format.fprintf fmt "And(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aor (p1, p2) ->
      Format.fprintf fmt "Or(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aimplies (p1, p2) ->
      Format.fprintf fmt "Implies(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Axor (p1, p2) ->
      Format.fprintf fmt "Xor(";
      pp_arm_predicate out p1;
      Format.fprintf fmt ", ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Arel (rel, t1, t2) ->
      let signed = type_to_signed t1.ty in

      let op, infix =
        if signed then
          ( (match rel with
            | Rlt -> "<"
            | Rge -> ">="
            | Rle -> "<="
            | Rgt -> ">"
            | Rneq -> "!="
            | Req -> "=="),
            true )
        else
          match rel with
          | Rlt -> ("ULT", false)
          | Rge -> ("UGE", false)
          | Rle -> ("ULE", false)
          | Rgt -> ("UGT", false)
          | Rneq -> ("!=", true)
          | Req -> ("==", true)
      in

      if infix then (
        Format.fprintf fmt "(";
        pp_arm_term out t1;
        Format.fprintf fmt " %s " op;
        pp_arm_term out t2;
        Format.fprintf fmt ")")
      else (
        Format.fprintf fmt "%s(" op;
        pp_arm_term out t1;
        Format.fprintf fmt ", ";
        pp_arm_term out t2;
        Format.fprintf fmt ")")
  | _ -> raise (ArmException "Unknown pp_arm_predicate")

let add_variable (term : arm_term) (name : arm_logic_var)
    (predicate : arm_predicate) =
  Aand
    ( predicate,
      Arel (Req, node_to_term term.ty (Translation.var_to_arm name), term) )

let add_variables (variables : (arm_logic_var * arm_term) list)
    (predicate : arm_predicate) =
  List.fold_left
    (fun p (name, term) -> add_variable term name p)
    predicate variables

let print_contract (out : Format.formatter) (contract : arm_contract) =
  let (formatter : contract_printer) = { fmt = out } in

  Format.fprintf out "\n# Old Variables\n";
  List.iter
    (fun (name, term) ->
      Format.fprintf out "%s = BitVec('%s', %d)\n" name name
        (term.ty |> size_of |> word_to_bits))
    contract.enviroment.old;

  Format.fprintf out "\n# Pre State\n";
  Format.fprintf out "REG = Array('REG(s)', BitVecSort(64), BitVecSort(64))\n";
  Format.fprintf out "MEM = Array('MEM(s)', BitVecSort(64), BitVecSort(64))\n";
  Format.fprintf out "\n# Pre Contract\n";

  Format.fprintf out "OldVar = ";
  pp_arm_predicate formatter
    (add_variables contract.enviroment.old Atrue |> simplify);
  Format.fprintf out "\n";

  Format.fprintf out "Requires = ";
  pp_arm_predicate formatter contract.requires;
  Format.fprintf out "\n";

  Format.fprintf out "\n# Post State\n";
  Format.fprintf out
    "REG = Array('REG(s\\')', BitVecSort(64), BitVecSort(64))\n";
  Format.fprintf out
    "MEM = Array('MEM(s\\')', BitVecSort(64), BitVecSort(64))\n";

  Format.fprintf out "\n# Post Contract\n";

  Format.fprintf out "Ensures = ";
  pp_arm_predicate formatter contract.ensures;
  Format.fprintf out "\n";

  (* OldVar is included as it binds the variables *)
  Format.fprintf out "\n# Bindings\n";
  Format.fprintf out "P = And(OldVar, Requires)\n";
  Format.fprintf out "R = Ensures\n";
  Format.fprintf out "\n"

let print_arm_overflow (out : Format.formatter)
    (source : arm_translation_source) =
  let (formatter : contract_printer) = { fmt = out } in
  let contract = fn_to_arm source in

  (* Check if the contract implies is equal to itself, aka if overflow affects the result *)
  let check =
    Aiff
      ( Aand (contract.requires, contract.ensures),
        Aand (contract.requires, contract.ensures) )
  in
  pp_arm_predicate formatter check

let print_definition (out : Format.formatter) (source : arm_translation_source)
    =
  let contract = Translation.fn_to_arm source in
  print_contract out contract

(* Z3 fails to prove basic properties of Bit Vectors,

1. When conveting BV2Int
```py
a_bv = BitVec('a', 64)
b_bv = BitVec('b', 64)

a_int = BV2Int(a_bv, False)
b_int = BV2Int(b_bv, False)

p = Not(ULE(a_bv, b_bv) == (a_int <= b_int))
```

2. When converting Int2BV
```py
a_int = Int('a')
b_int = Int('b')
type_req = And(a_int >= 0, a_int <= 18446744073709551615, b_int >= 0, b_int <= 18446744073709551615)
a_bv = Int2BV(a_int, 64)
b_bv = Int2BV(b_int, 64)
p = And(type_req,Not(ULE(a_bv, b_bv) == (a_int <= b_int)))
```

Like ACSL, if we want any sort of check we must do the aritmatic in Int, or BitVec, but not both.
*)
