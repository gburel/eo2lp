open Prelude
open Term

module Ctx = struct
  module StrMap = Map.Make(String)
  type t = datum StrMap.t

  let is_list : t -> string -> bool =
    fun ctx str -> (StrMap.find str ctx).list

  let is_implicit : t -> string -> bool =
    fun ctx str -> (StrMap.find str ctx).implicit

  let get_typ : t -> string -> term =
    fun ctx str -> (StrMap.find str ctx).typ

  let add ((str_opt, dat) : param) (ctx : t) : t =
    Option.fold
      ~none:ctx
      ~some:(fun str -> StrMap.add str dat ctx)
      str_opt

  let join (c1 : t) (c2 : t) : t =
    StrMap.union (fun _ _ v2 -> Some v2) c1 c2

  let rec of_term (tm : term) : t =
    let rec aux (xs : param list) (trm : term) : t =
      match trm with
      | (Univ _ | Var _ | Meta _ | Literal _) -> StrMap.empty
      | Explicit t -> aux xs t
      | Bound i ->
        begin match List.nth_opt xs i with
        | Some x -> add x StrMap.empty
        | _ -> StrMap.empty
        end
      | App (e1, e2) -> join (aux xs e1) (aux xs e2)
      | Bind (_, x, t) ->
        join (aux xs ((snd x).typ)) (aux (x::xs) t)
    in
      aux [] tm

  let of_terms : term list -> t =
    List.fold_left (fun acc tm -> join acc (of_term tm)) StrMap.empty

  (* given a context `ctx` and term `tm`, return the context that binds `<k,v>`
    iff `k` is in the domain of `ctx` and appears as a variable in `tm`. *)
  let rec filter (ctx : t) : term -> t = function
  | Var x ->
    begin match StrMap.find_opt x ctx with
    | Some dat -> StrMap.singleton x dat
    | None -> StrMap.empty
    end
  | (Univ _| Meta _| Bound _|Literal _) -> StrMap.empty
  | App (e1, e2) -> join (filter ctx e1) (filter ctx e2)
  | Bind (_, (_,dat), tm) -> join (filter ctx dat.typ) (filter ctx tm)
end


module LocalTheory = struct
  module IntMap = Map.Make(Int)
  type t = {
    bvs : string IntMap.t
  }
end


(* struct
  type t = datum StrMap.t
  include StrMap

  let empty : t = StrMap.empty


  let join : t -> t -> t =
    StrMap.union (fun _ _ v2 -> Some v2)

  (* given a term, create a context for its binding structure *)
  let rec of_term (tm : term) : t =
    let rec aux (xs : binding list) (trm : term) : t =
      match trm with
      | (Univ _ | Var _ | Meta _ | Literal _) -> StrMap.empty
      | Explicit t -> aux xs t
      | Bound i ->
        begin match List.nth_opt xs i with
        | Some (Some str, dat) -> StrMap.singleton str dat
        | _ -> StrMap.empty
        end
      | App (e1, e2) ->
        join (aux xs e1) (aux xs e2)
      | Bind (_, (x, dat), t) ->
        join (aux xs dat.typ) (aux ((x, dat) :: xs) t)
    in
    aux [] tm

  let of_terms : term list -> t =
    List.fold_left (fun acc tm -> join acc (of_term tm)) empty



end *)

(* given a term `tm` and a context `ctx`, return the map given by the set
  `{ <x,dat> in ctx | x is a variable in tm }`.
*)
