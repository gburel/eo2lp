type literal =
  | Numeral of int
  | Rational of (int * int)
  | Decimal of float
[@@deriving show]

type eo_term =
  | Literal of literal
  | Symbol of string
  | AppList of string * eo_term list
  | Define of eo_var list * eo_term
  | Match of eo_var list * eo_term * (eo_term * eo_term) list
  | Attributed of eo_term * req_attr list * attr list
and eo_var = string * eo_term * attr list
and attr = string * eo_term option
and req_attr = (eo_term * eo_term)
[@@deriving show]

(* context modifying commands. *)
type base_command =
| Assert of eo_term
| DeclareConst of string * eo_term * attr list
| DefineConst of string * eo_term
| DeclareFun of string * eo_term list * eo_term * attr list
| DefineFun of function_def
| DefineFunRec of function_def
| DefineFunsRec of fun_decl list * eo_term list (*check same length*)
| DeclareSort of sort_decl
| DefineSort of string * string list * eo_term
| DeclareDatatype of string * datatype_decl
| DeclareDatatypes of sort_decl list * datatype_decl list
| DeclareType of string * eo_term list (*SMT3*)
| DefineType of string * eo_term list * eo_term (*SMT3*)
and function_def = string * eo_var list * eo_term * eo_term
and datatype_decl = constructor_decl list
and fun_decl = string * eo_var list * eo_term
and sort_decl = string * int
and selector_decl  = string * eo_term
and constructor_decl = string * selector_decl list
[@@deriving show]

type exc_command =
| Define of string * eo_var list * eo_term
| DeclareRule of string * eo_var list * rule_spec
| DeclareConsts of lit_category * eo_term
| DeclareParamConst of string * eo_var list * eo_term * attr list
| DeclareOracleFun of string * eo_term list * eo_term * string
| Include of string
| Program of string * string option * eo_var list * eo_term list * eo_term * (eo_term * eo_term) list
| Reference of string * string option
and rule_spec = {
  assumes : eo_term option;
  prems : premises option;
  arguments : (eo_term list) option;
  requires : ((eo_term * eo_term) list) option;
  conclusion : eo_term;
  attrs : attr list }
and premises =
  | PremiseList of eo_term * eo_term (*this is wrong????*)
  | Premises of eo_term list
and lit_category =
  | STR | NUM | DEC | RAT | BIN | HEX
[@@deriving show]

(* Eunoia commands that produce props *)
type proof_command =
  | Assume of string * eo_term
  | AssumePush of string * eo_term
  | Step of string * eo_term option * string * premises option * eo_term list option
  | StepPop of string * eo_term option * string * premises option * eo_term list option
[@@deriving show]

type control_command =
  | CheckSatAssuming of eo_term list
  | Echo of string
  | Exit
  | GetAssertions
  | GetAssignment
  | GetInfo of string
  | GetModel
  | GetOption of string
  | GetProof
  | GetUnsatAssumptions
  | GetUnsatCore
  | GetValue of eo_term list
  | Pop of int
  | Push of int
  | Reset
  | ResetAssertions
  | SetInfo of attr
  | SetLogic of string
  | SetOption of string

[@@deriving show]

type eo_command =
  | Base of base_command
  | Ctrl of control_command
  | EO of exc_command
  | Prf of proof_command
[@@deriving show]

let get_eo_name = function
  | Base cmd -> (match cmd with
    | DeclareConst (name, _, _) -> Some name
    | DefineConst (name, _) -> Some name
    | DeclareFun (name, _, _, _) -> Some name
    | DefineFun (name, _, _, _) -> Some name
    | DefineFunRec (name, _, _, _) -> Some name
    | DefineFunsRec (funs, _) -> Some (List.hd funs |> fun (n,_,_) -> n)
    | DeclareSort (name, _) -> Some name
    | DefineSort (name, _, _) -> Some name
    | DeclareDatatype (name, _) -> Some name
    | DeclareType (name, _) -> Some name
    | DefineType (name, _, _) -> Some name
    | _ -> None)
  | EO cmd -> (match cmd with
    | Define (name, _, _) -> Some name
    | DeclareRule (name, _, _) -> Some name
    | DeclareParamConst (name, _, _, _) -> Some name
    | DeclareOracleFun (name, _, _, _) -> Some name
    | Program (name, _, _, _, _, _) -> Some name
    | _ -> None)
  | Prf cmd -> (match cmd with
    | Assume (name, _) -> Some name
    | AssumePush (name, _) -> Some name
    | Step (name, _, _, _, _) -> Some name
    | StepPop (name, _, _, _, _) -> Some name)
  | Ctrl _ -> None

type eo_sig = eo_command list
type eo_file = string * eo_sig
type eo_library = eo_file list

let is_implicit (atts : attr list) =
  Option.is_some (List.assoc_opt "implicit" atts)

let is_list (atts : attr list) =
  Option.is_some (List.assoc_opt "list" atts)

let mk_eo_var ty =
  match ty with
  | Attributed (ty', _, atts) ->
    begin match Option.join (List.assoc_opt "var" atts) with
    | None -> ("_", ty', atts)
    | Some (Symbol str) ->
      (str, ty', atts)
    end
  | _ -> ("_", ty, [])

(* in SMT3 but not Eunoia.
  | Import of string list
  | Open of string
-----------------------------
  | DefineSyntax of syntax_rule * syntax_rule list
  | DefineValues of eo_term * eo_term * eo_term
  | DefineModule of ...
  | DeclareInductiveTypes of  ...
  | DefineEnumerationType of  ...
*)

(* in Eunoia but not SMT3
  | DeclareRule of string * eo_var list * assm option * prems option * args option * reqs option * eo_term
  | DeclareConsts of lit_category * eo_term
  | DeclareParamConst of string * eo_var list * eo_term * attr list
  | DeclareOracleFun of string * eo_term list * eo_term * string
  | Include of string
  | Program of string * eo_var list * eo_term list * eo_term * (eo_term * eo_term) list
  | Reference of string * string option

*)
