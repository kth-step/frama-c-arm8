open Specification
open Translation
open Cil_types

let pre_state = "st"
let post_state = "st"

type contract_printer = { fmt : Format.formatter; post : bool }
(* https://kth-step.github.io/itppv-course/ *)
(* https://github.com/kth-step/HolBA/tree/master/examples/arm8/max *)

let pp_arm_logical_constant (out : contract_printer)
    (constant : arm_logic_constant) (ty : arm_type) =
  match constant with
  | ABoolean true -> Format.fprintf out.fmt "T"
  | ABoolean false -> Format.fprintf out.fmt "F"
  | AInteger z ->
      Format.fprintf out.fmt "(%sw : word%d)" z (ty |> size_of |> word_to_bits)

let pp_logic_var (out : contract_printer) (var : arm_logic_var) =
  Format.fprintf out.fmt "%s" var

let rec pp_arm_lvalue (out : contract_printer) (host : arm_term_lhost) =
  match host with
  | AVar v -> pp_logic_var out v
  | ARegister (at, size) ->
      (* To simulate reading w0 or lower we extract the lower bits *)
      pp_arm_cast_fn out AExtract size Word64 (fun local_out ->
          Format.fprintf local_out.fmt "(%s.REG %dw)"
            (if out.post then post_state else pre_state)
            at)
  | AMemory (at, size) ->
      (* To simulate a smaller read we extract the lower bits *)
      pp_arm_cast_fn out AExtract size Word64 (fun local_out ->
          Format.fprintf local_out.fmt "(arm8_load_64 %s.MEM "
            (if out.post then post_state else pre_state);
          pp_arm_term local_out at;
          Format.fprintf local_out.fmt ")")

and pp_arm_unop (out : contract_printer) (op : arm_unop) (term : arm_term) :
    unit =
  let prefix = match op with BNot -> "~" | LNot -> "~" | Neg -> "-" in
  Format.fprintf out.fmt "(%s" prefix;
  pp_arm_term out term;
  Format.fprintf out.fmt ")"

and pp_arm_cast_fn (out : contract_printer) (cast : arm_cast)
    (to_size : arm_word_size) (from_size : arm_word_size)
    (printer : contract_printer -> unit) : unit =
  let to_bits = word_to_bits to_size in
  let from_bits = word_to_bits from_size in

  if from_bits = to_bits then printer out
  else
    (* https://github.com/HOL-Theorem-Prover/HOL/blob/49d055302c1a002be77ab39b156e838c525b2401/src/n-bit/selftest.sml#L646 *)
    match cast with
    | AExtract ->
        (* Extract is inclusive *)
        Format.fprintf out.fmt "(word_extract %d 0 " (to_bits - 1);
        printer out;
        Format.fprintf out.fmt " : word%d)" to_bits
    | ASignExtend ->
        Format.fprintf out.fmt "(sw2sw ";
        printer out;
        Format.fprintf out.fmt " : word%d)" to_bits
    | AZeroExtend ->
        Format.fprintf out.fmt "(w2w ";
        printer out;
        Format.fprintf out.fmt " : word%d)" to_bits

and pp_arm_cast (out : contract_printer) (cast : arm_cast)
    (to_size : arm_word_size) (from_size : arm_word_size) (term : arm_term) :
    unit =
  pp_arm_cast_fn out cast to_size from_size (fun local_out ->
      pp_arm_term local_out term)

and pp_arm_binop (out : contract_printer) (op : arm_binop) (lhs : arm_term)
    (rhs : arm_term) : unit =
  match op with
  | AMod | ADiv | AShiftlt | AShiftrt ->
      let signed, unsigned =
        match op with
        | ADiv -> ("word_sdiv", "word_div")
        | AMod -> ("word_smod", "word_mod")
        | AShiftrt -> ("word_lsr_bv", "word_lsr_bv")
        | AShiftlt -> ("word_lsl_bv", "word_lsl_bv")
        | _ -> raise (ArmException "Unreachable")
      in
      let fn = if type_to_signed lhs.ty then signed else unsigned in

      Format.fprintf out.fmt "(%s " fn;
      pp_arm_term out lhs;
      Format.fprintf out.fmt " ";
      pp_arm_term out rhs;
      Format.fprintf out.fmt ")"
  | _ ->
      let infix =
        match op with
        | APlusA -> "+"
        | AMinusA -> "-"
        | AMult -> "*"
        | AMod | ADiv | AShiftrt | AShiftlt ->
            raise (ArmException "Unreachable")
        | AEq -> "="
        | ANe -> "<>"
        | ALOr -> "\\/"
        | ALAnd -> "/\\"
        | ABAnd -> "&&"
        | ABOr -> "||"
        | ABXor -> "??"
        | ALt | AGt | AGe | ALe -> (
            let signed = type_to_signed lhs.ty in
            if signed then
              match op with
              | ALt -> "<"
              | AGe -> ">="
              | ALe -> "<="
              | AGt -> ">"
              | _ -> raise (ArmException "Unreachable")
            else
              match op with
              | ALt -> "<+"
              | AGe -> ">=+"
              | ALe -> "<=+"
              | AGt -> ">+"
              | _ -> raise (ArmException "Unreachable"))
      in

      Format.fprintf out.fmt "(";
      pp_arm_term out lhs;
      Format.fprintf out.fmt " %s " infix;
      pp_arm_term out rhs;
      Format.fprintf out.fmt ")"

and pp_arm_term (out : contract_printer) (term : arm_term) =
  match term.node with
  | AConst logical -> pp_arm_logical_constant out logical term.ty
  | ABinOp (op, lhs, rhs) -> pp_arm_binop out op lhs rhs
  | ALval host -> pp_arm_lvalue out host
  | SP -> Format.fprintf out.fmt "s.SP_EL0"
  | AUnOp (op, term) -> pp_arm_unop out op term
  | ACast (cast, size, term) -> pp_arm_cast out cast size (size_of term.ty) term
  | ABuiltin (name, args) ->
      (* We assume the builtin applications works on the same type *)
      let arg1 = args |> List.hd in
      let signed = type_to_signed arg1.ty in
      let application_name =
        match (signed, name) with
        | true, AMax -> "word_smax"
        | false, AMax -> "word_max"
        | true, AMin -> "word_smin"
        | false, AMin -> "word_min"
        | _, AAbs -> "word_abs"
        (*| true, APow -> "word_sexp"
        | false, APow -> "word_exp"*)
      in
      let fmt = out.fmt in
      Format.fprintf fmt "(%s " application_name;
      pp_arm_term out arg1;
      List.drop 1 args
      |> List.iter (fun x ->
          Format.fprintf fmt " ";
          pp_arm_term out x);
      Format.fprintf fmt " : word%d)" (arg1.ty |> size_of |> word_to_bits)
  | Aif (c, t1, t2) ->
      let fmt = out.fmt in
      Format.fprintf fmt "(if ";
      pp_arm_predicate out c;
      Format.fprintf fmt " then ";
      pp_arm_term out t1;
      Format.fprintf fmt " else ";
      pp_arm_term out t2;
      Format.fprintf fmt ")";

and unfold_and (predicate : arm_predicate) : arm_predicate list =
  match predicate with
  | Aand (p1, p2) -> p2 :: unfold_and p1
  | _ -> [ predicate ]

and pp_arm_predicate (out : contract_printer) (predicate : arm_predicate) =
  let fmt = out.fmt in
  match predicate with
  | Aiff (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " <=> ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aif (c, t1, t2) ->
      Format.fprintf fmt "if (";
      pp_arm_predicate out c;
      Format.fprintf fmt ") then (";
      pp_arm_predicate out t1;
      Format.fprintf fmt ") else (";
      pp_arm_predicate out t2;
      Format.fprintf fmt ")"
  (*| Aoverflow (o, lhs, rhs) -> pp_no_overflow out o lhs rhs*)
  | Afalse -> Format.fprintf fmt "F"
  | Atrue -> Format.fprintf fmt "T"
  | Aand (p1, p2) ->
      let list = unfold_and p1 in
      (* We unfold the and list and remove the extra paraenesis to make it easier to read *)
      list
      |> List.rev
         (* Rev as we are working with linked lists with filo ordering *)
      |> List.iter (fun x ->
          pp_arm_predicate out x;
          Format.fprintf fmt " /\\\n  ");
      pp_arm_predicate out p2
  | Aor (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " \\/ ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Aimplies (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " ==> ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Axor (p1, p2) ->
      Format.fprintf fmt "(";
      pp_arm_predicate out p1;
      Format.fprintf fmt " <> ";
      pp_arm_predicate out p2;
      Format.fprintf fmt ")"
  | Arel (rel, t1, t2) ->
      let signed = type_to_signed t1.ty in

      let op =
        if signed then
          match rel with
          | Rlt -> "<"
          | Rge -> ">="
          | Rle -> "<="
          | Rgt -> ">"
          | Rneq -> "<>"
          | Req -> "="
        else
          match rel with
          | Rlt -> "<+"
          | Rge -> ">=+"
          | Rle -> "<=+"
          | Rgt -> ">+"
          | Rneq -> "<>"
          | Req -> "="
      in

      Format.fprintf fmt "(";
      pp_arm_term out t1;
      Format.fprintf fmt " %s " op;
      pp_arm_term out t2;
      Format.fprintf fmt ")"
  | Anot p ->
      Format.fprintf fmt "~";
      pp_arm_predicate out p
  (*| _ -> raise (ArmException "Unknown pp_arm_predicate")*)

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

let print_list (out : Format.formatter) (prefix : string)
    (list : identified_predicate list) =
  List.iter
    (fun fn ->
      (* Double print, otherwise we get nested formatting logic *)
      Format.fprintf out "%s %s;\n" prefix
        (Format.asprintf "%a" Printer.pp_predicate_node
           fn.ip_content.tp_statement.pred_content))
    list

let print_header (out : Format.formatter)
    (globals : (varinfo * initinfo option) list) =
  if globals |> List.is_empty |> not then (
    Format.fprintf out "(* -------------- *)\n";
    Format.fprintf out "(* ARMv8 globals  *)\n";
    Format.fprintf out "(* -------------- *)\n\n");

  (* 
  Dirty hack to include globals by letting the user define the global themself ;)

  The main problem with globals is that they are pointers with an unknown address, so we can not reason with them
  *)
  globals |> List.rev
  |> List.iter (fun (variable, initalizer) ->
      Format.fprintf out "Definition global_%s_def:\n  global_%s = "
        variable.vorig_name variable.vorig_name;

      (match initalizer with
      | Some x ->
          Format.fprintf out "(* ";
          Printer.pp_initinfo out x;
          Format.fprintf out " *)"
      | None -> Format.fprintf out "...");
      Format.fprintf out "\nEnd\n\n");
  Format.fprintf out "(* -------------- *)\n";
  Format.fprintf out "(* ARMv8 contract *)\n";
  Format.fprintf out "(* -------------- *)\n"

let print_definition (out : Format.formatter) (print_ast : bool)
    (source : arm_translation_source) =
  let (fmt : contract_printer) = { fmt = out; post = false } in
  let fn = source.fn in
  let kf = Globals.Functions.get fn.svar in
  let behaviors = Annotations.behaviors kf in
  let contract = Translation.fn_to_arm source in
  Format.fprintf out "\n(* ------- Function %s -------*)\n" fn.svar.vname;
  if
    print_ast
    && List.exists (fun fn -> fn.b_requires |> List.is_empty |> not) behaviors
  then (
    Format.fprintf out "(* \n";
    List.iter
      (fun st ->
        if st.b_name <> "default!" then Format.fprintf out "%s: \n" st.b_name;
        print_list out "  requires" st.b_requires)
      behaviors;
    Format.fprintf out "*) \n");

  Format.fprintf out "Definition arm8_%s_pre_def:\n" fn.svar.vname;
  Format.fprintf out " arm8_%s_pre " fn.svar.vname;

  contract.enviroment.old |> List.rev
  |> List.iter (fun (name, term) ->
      Format.fprintf out "(%s:word%d) " name (term.ty |> size_of |> word_to_bits));
  Format.fprintf out "(%s:arm8_state) : bool =\n  (" pre_state;

  pp_arm_predicate fmt
    (add_variables contract.enviroment.old contract.requires |> simplify);

  Format.fprintf out ")\nEnd\n\n";
  if
    print_ast
    && List.exists (fun fn -> fn.b_post_cond |> List.is_empty |> not) behaviors
  then (
    Format.fprintf out "(* \n";
    List.iter
      (fun st ->
        if st.b_name <> "default!" then Format.fprintf out "%s: \n" st.b_name;
        print_list out "  ensures"
          (st.b_post_cond |> List.map (fun (_, item) -> item)))
      behaviors;
    Format.fprintf out "*) \n");
  Format.fprintf out "Definition arm8_%s_post_def:\n" fn.svar.vname;
  Format.fprintf out " arm8_%s_post " fn.svar.vname;

  contract.enviroment.old |> List.rev
  |> List.iter (fun (name, term) ->
      Format.fprintf out "(%s:word%d) " name (term.ty |> size_of |> word_to_bits));
  Format.fprintf out "(%s:arm8_state) : bool =\n  (" post_state;

  let (fmt : contract_printer) = { fmt = out; post = true } in
  pp_arm_predicate fmt contract.ensures;

  Format.fprintf out ")\nEnd";

  Format.fprintf out "\n"
