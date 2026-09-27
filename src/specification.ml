open Cil_types

(* 
  The intermediate representation for the contract logic
*)

exception ArmException of string

type no_overflow_type = Oadd | Osub | Omul | Odiv [@@deriving eq]

type arm_predicate =
  (* false *)
  | Afalse
  (* true *)
  | Atrue
  (* p1 ⇔ p2 *)
  | Aiff of arm_predicate * arm_predicate
  (* if c then p1 else p2 *)
  | Aif of arm_predicate * arm_predicate * arm_predicate
  (* p1 ∧ p2 *)
  | Aand of arm_predicate * arm_predicate
  (* p1 ∨ p2 *)
  | Aor of arm_predicate * arm_predicate
  (* p1 ⇒ p2 *)
  | Aimplies of arm_predicate * arm_predicate
  (* ¬p *)
  | Anot of arm_predicate
  (* p1 ^^ p2 *)
  | Axor of arm_predicate * arm_predicate
  (* t1 (<, >, ≤, ≥, =, ≠) t2 *)
  | Arel of relation * arm_term * arm_term
[@@deriving eq]

and arm_type =
  (* Machine integer of signed + size, corresponding to Ctype TInt *)
  | AInt of bool * arm_word_size
  (* A boolean value, corresponding to Lboolean *)
  | ABool
  (* A pointer value, corresponding to Ctype TPtr *)
  | APtr of arm_type
  (* A void type, should only be used behind a void ptr *)
  | AVoid
[@@deriving eq]

and arm_term = { node : arm_term_node; ty : arm_type } [@@deriving eq]
and arm_logic_var = string
and arm_word_size = Word8 | Word16 | Word32 | Word64 [@@deriving eq]

(** base address of an lvalue. *)
and arm_term_lhost =
  (* a variable. *)
  | AVar of arm_logic_var
  (* REG(s, register, size) *)
  | ARegister of int * arm_word_size
  (* MEM(s, pointer, size) *)
  | AMemory of arm_term * arm_word_size
[@@deriving eq]

and arm_term_lval = arm_term_lhost [@@deriving eq]
and arm_logic_constant = ABoolean of bool | AInteger of string

and arm_binop =
  | APlusA  (** arithmetic + *)
  | AMinusA  (** arithmetic - *)
  | AMult  (** * *)
  | ADiv
      (** /
          @see <https://frama-c.com/download/frama-c-plugin-development-guide.pdf>
      *)
  | AMod
      (** %
          @see <https://frama-c.com/download/frama-c-plugin-development-guide.pdf>
      *)
  | AShiftlt  (** shift left *)
  | AShiftrt  (** shift right *)
  | ALt  (** < (arithmetic comparison) *)
  | AGt  (** > (arithmetic comparison) *)
  | ALe  (** <= (arithmetic comparison) *)
  | AGe  (** >= (arithmetic comparison) *)
  | AEq  (** == (arithmetic comparison) *)
  | ANe  (** != (arithmetic comparison) *)
  | ABAnd  (** bitwise and *)
  | ABXor  (** exclusive-or *)
  | ABOr  (** inclusive-or *)
  | ALAnd
      (** logical and. Unlike other operators, this one does not always evaluate
          both operands. If you want to keep it during normalization, you must
          set {!Kernel.LogicalOperators}. You can know if the current machine
          support them via {!Machine.use_logical_operators}. *)
  | ALOr
      (** logical or. Like [LAnd] this operator is removed unless
          {!Kernel.LogicalOperators} is set. *)

and arm_unop = unop

and arm_cast =
  (* Extend a unsigned value to a higher bitwidth *)
  | AZeroExtend
  (* Extend a signed value to a higher bitwidth *)
  | ASignExtend
  (* Extract the lower bits of a higher bitwidth word *)
  | AExtract

and arm_term_node =
  (* a constant. *)
  | AConst of arm_logic_constant
  (* an L-value *)
  | ALval of arm_term_lval
  (* Stack pointer *)
  | SP
  (* lhs (+, -, *, /, %, <<, >>, <, >, <=, >=, ==, !=, &, ^, |) rhs *)
  | ABinOp of arm_binop * arm_term * arm_term
  (* (-, !, ~) term *)
  | AUnOp of arm_unop * arm_term
  (* (sx, zx, ex) size, term *)
  | ACast of arm_cast * arm_word_size * arm_term
  (* Also used for boolean casting *)
  (* if c then p1 else p2 *)
  | Aif of arm_predicate * arm_term * arm_term
  (* Applications like \min and \max *)
  | ABuiltin of arm_builtin * arm_term list
[@@deriving eq]

(* Builtin functions *)
and arm_builtin =
  (* integer \min(integer x, integer y) ; *)
  | AMin
  (* integer \max(integer x, integer y) ; *)
  | AMax
  (* integer \abs(integer x) ; *)
  | AAbs
(* integer pow(integer x, integer y) ; *)
(*| APow *)
(* It looks like the pow built-in is bugged, as it just uses the "real" number pow instead ?*)

type arm_overflow = arm_predicate option
type arm_location = Pre | Post

type arm_enviroment = {
  (* Used for arguments, and \let terms. V[name] -> location * term; 
  here location is used for arguments, as arguments can be in the Pre-State but only be accessed in the post state with a \old   *)
  mutable variables : (arm_logic_var, arm_location * arm_term_node) Hashtbl.t;
  (* Used for \let predicates *)
  mutable predicates : (arm_logic_var, arm_predicate) Hashtbl.t;
  (* Used for \old as we only want to calculate old in the pre context *)
  mutable old : (arm_logic_var * arm_term) list;
  (* This is used to keep track of what context we are currently in, 
  as it is possible to smuggle variables to the post-state with *&x circumventing the implicit \old*)
  mutable at : arm_location;
}

type arm_contract = {
  ensures : arm_predicate;
  requires : arm_predicate;
  enviroment : arm_enviroment;
}

type arm_translation_source = {
  (* function to translate *)
  fn : fundec;
  (* list of relevant global variables *)
  globals : (varinfo * initinfo option) list;
}

(*type contract_options = { overflow : bool }*)

(* If we can simplify it, then do it. This is just an ad hoc solution to simplify trivial expressions intoduced in folding *)
let rec simplify (predicate : arm_predicate) : arm_predicate =
  match predicate with
  | Aand (p1, p2) -> (
      match (simplify p1, simplify p2) with
      | Atrue, Atrue -> Atrue
      | Afalse, _ | _, Afalse -> Afalse
      | Atrue, sp2 -> sp2
      | sp1, Atrue -> sp1
      | sp1, sp2 -> Aand (sp1, sp2))
  | Aor (p1, p2) -> (
      match (simplify p1, simplify p2) with
      | Afalse, Afalse -> Afalse
      | Atrue, _ | _, Atrue -> Atrue
      | Afalse, sp2 -> sp2
      | sp1, Afalse -> sp1
      | sp1, sp2 -> Aor (sp1, sp2))
  | Anot p -> (
      match simplify p with
      | Afalse -> Atrue
      | Atrue -> Afalse
      | Anot x -> x
      | pattern -> Anot pattern)
  | Aiff (lhs, rhs) -> (
      match (simplify lhs, simplify rhs) with
      | Afalse, Afalse | Atrue, Atrue -> Atrue
      | Afalse, Atrue | Atrue, Afalse -> Afalse
      | Atrue, srhs -> srhs
      | slhs, Atrue -> slhs
      | Afalse, srhs -> Anot srhs
      | slhs, Afalse -> Anot slhs
      | slhs, srhs -> Aiff (slhs, srhs))
  | Aif (c, p1, p2) -> (
      match (simplify p1, simplify p2) with
      | Atrue, Atrue -> Atrue
      | Afalse, Afalse -> Afalse
      | sp1, sp2 -> Aif (c, sp1, sp2))
  | Aimplies (p1, p2) -> (
      match (simplify p1, simplify p2) with
      | Afalse, _ -> Atrue
      | Atrue, sp2 -> sp2
      | _, Atrue -> Atrue
      | sp1, Afalse -> Anot sp1
      | sp1, sp2 -> Aimplies (sp1, sp2))
  | Axor (p1, p2) -> (
      match (simplify p1, simplify p2) with
      | Atrue, Atrue | Afalse, Afalse -> Afalse
      | Atrue, Afalse | Afalse, Atrue -> Atrue
      | Atrue, p | p, Atrue -> Anot p
      | Afalse, p | p, Afalse -> p
      | sp1, sp2 -> Axor (sp1, sp2))
  | _ -> predicate

(* Helper to print with Printer for error messages*)
let pp_spec (f : Format.formatter -> 'a -> unit) (term : 'a) : string =
  let buf = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer buf in
  f fmt term;
  Format.pp_print_flush fmt ();
  Buffer.contents buf
