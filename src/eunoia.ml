open Prelude

type eo_term =
  | Literal of literal
  | Symbol of string
  | AppList of string * eo_term list
  | Define of typed_param list * eo_term
  | Match of typed_param list * eo_term * (eo_term * eo_term) list
  | Attributed of eo_term * attr list
and typed_param = string * eo_term * attr list
and attr =
  | Attr of string * eo_term option
  | Requires of (eo_term * eo_term)
[@@deriving show]

type eo_rule = (eo_term * eo_term) list

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
and function_def = string * typed_param list * eo_term * eo_term
and datatype_decl = constructor_decl list
and fun_decl = string * typed_param list * eo_term
and sort_decl = string * int
and selector_decl  = string * eo_term
and constructor_decl = string * selector_decl list
[@@deriving show]

type eunoia_command =
| Define of string * typed_param list * eo_term
| DeclareRule of string * typed_param list * rule_spec
| DeclareConsts of lit_category * eo_term
| DeclareParamConst of string * typed_param list * eo_term * attr list
| DeclareOracleFun of string * eo_term list * eo_term * string
| Include of string
| Program of string * string option * typed_param list * eo_term list * eo_term * (eo_term * eo_term) list
| Reference of string * string option
and rule_spec = {
  assumes : eo_term option;
  prems : premises option;
  arguments : (eo_term list) option;
  requires : ((eo_term * eo_term) list) option;
  conclusion : eo_term;
  attrs : attr list }
and premises =
  | PremiseList of eo_term * eo_term
  | Premises of eo_term list
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
  | EO of eunoia_command
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

(* -------- Basic utilities --------------- *)

let is_symbol (trm : eo_term) =
  match trm with
  | Symbol _ -> true
  | _ -> false

let simple_atts (atts : attr list) = List.filter_map
  (function Attr (str,tm_opt) -> Some (str,tm_opt) | _ -> None) atts

let req_atts (atts : attr list) = List.filter_map
  (function Attr _ -> None | Requires (tm1,tm2) -> Some (tm1,tm2)) atts



let find_att_opt (atts : attr list) (str : string) =
  Option.join (List.assoc_opt str (simple_atts atts))

let mem_att (atts : attr list) (str : string) =
  List.mem_assoc str (simple_atts atts)

(* deprecated. *)
let atts_has_list (atts : attr list) = mem_att atts "list"
let atts_has_implicit (atts : attr list) = mem_att atts "implicit"

let mk_typed_param ty =
  match ty with
  | Attributed (ty', atts) ->
    begin match find_att_opt atts "var" with
    | None -> ("_", ty', atts)
    | Some (Symbol str) -> (str, ty', atts)
    end
  | _ -> ("_", ty, [])


(* ------- hacky Eunoia program schemas ------- *)

let rec subst_trm (sub : eo_term StrMap.t) (trm : eo_term) =
  match trm with
  | Literal l -> Literal l
  | Symbol s ->
    begin match StrMap.find_opt s sub with
    | Some t -> t
    | None -> Symbol s
    end

  | AppList (s, ts) ->
    let ts' = List.map (subst_trm sub) ts in
    begin match StrMap.find_opt s sub with
    | Some (Symbol s') -> AppList (s', ts')
    | Some t -> AppList ("_", t :: ts')
    | None -> AppList (s, ts')
    end

  | Define (vs, trm) ->
    let vs' = List.map (fun (v,ty,atts) -> (v, subst_trm sub ty, atts)) vs in
    Define (vs', subst_trm sub trm)

  | Match (vs, t, rws) ->
    let vs' = List.map (fun (v,ty,atts) -> (v, subst_trm sub ty, atts)) vs in
    let t' = subst_trm sub t in
    let rws' = subst_rule sub rws in
    Match (vs', t', rws')

  | Attributed (t, atts) -> Attributed (subst_trm sub t, subst_atts sub atts)

and subst_atts sub atts =
  List.map (function
    | Attr (str, Some trm) -> Attr (str, Some (subst_trm sub trm))
    | Attr (str, None) -> Attr (str, None)
    | Requires (tm1, tm2) -> Requires (subst_trm sub tm1 , subst_trm sub tm2)
  ) atts

and subst_rule sub rws =
  List.map (fun (lhs, rhs) -> (subst_trm sub lhs, subst_trm sub rhs)) rws

let subst_prog (sub : eo_term StrMap.t) ((vs, rw) : typed_param list * eo_rule) =
  (* Remove domain of substituion from parameter list, apply substituion in types. *)
  let vs' =
    List.filter_map (fun (str, ty, atts) ->
      match StrMap.find_opt str sub with
      | Some _ -> None
      | None -> Some (str, subst_trm sub ty, atts)
    ) vs in
  (vs', subst_rule sub rw)

let rec eo_binop_tys typ =
  match typ with
  | AppList ("->", t1 :: t2 :: tys) ->
    begin match t1 with
    | Attributed (_,atts) when mem_att atts "implicit" ->
      Printf.printf "warning! binary operator with implicit argument.";
      eo_binop_tys (AppList ("->", t2 :: tys))
    | _ -> (t1,t2)
    end
  | _ -> failwith "Not the type of a binary operator."

module Prog = struct
  type t = typed_param list * (eo_term * eo_term) list
  let compare = compare
end

module ProgSet = Set.Make(Prog)

module EoSubst = struct
  type t = eo_term StrMap.t
  let compare = compare
end

module EoSubstSet = Set.Make(EoSubst)



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
  | DeclareRule of string * typed_param list * assm option * prems option * args option * reqs option * eo_term
  | DeclareConsts of lit_category * eo_term
  | DeclareParamConst of string * typed_param list * eo_term * attr list
  | DeclareOracleFun of string * eo_term list * eo_term * string
  | Include of string
  | Program of string * typed_param list * eo_term list * eo_term * (eo_term * eo_term) list
  | Reference of string * string option

*)
