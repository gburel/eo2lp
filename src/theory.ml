open Prelude
open Term
open Context
open Nary

type command =
  | Const of string * term
  | Defn of string * term * term
  | Prog of string * term
  | Rule of rw_rule
  | LitTy of lit_category * term
and rw_rule = Ctx.t * (term * term) list

module Theory = struct
  module StrMap = Map.Make(String)
  module StrSet = Set.Make(String)

  type t = {
    id : string;
    parents : StrSet.t;
    signature : Ctx.t;
    commands : command list;
    notation : attribute StrMap.t;
    rule_schema : (rw_rule list) StrMap.t
  }
end
