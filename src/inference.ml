open Ast_cc
open Ast

let debug_inference = ref false

(* mutable reference for generating fresh metavariable names. *)
let mvar_count = ref 0

(* For a term `trm`, return the list of params for the metavariables taken
  whilst descending on the outermost implicit Pi-binders.  *)
let rec mk_mvars (trm : cc_term) : param list =
  match trm with
  | Bind (Pi, (_, ty, {implicit=true;_}), t') ->
    let idx_str = string_of_int !mvar_count in
    mvar_count := !mvar_count + 1;
    (Some idx_str, ty, {implicit = false; list = false}) :: mk_mvars t'
  | _ -> []

(*
  Implicit variables only come from applications of (free) variables whose types
  have implicit Pi-bindings. Hence, we elaborate terms by finding each variable `x`
  with this property, generating fresh metavariables `?a1 .. ?an` with types
  `t1 .. tn`, and replacing `x` with `x ?a1 .. ?an. We also return the list of
  all of the metavariables generated paired with their types.
  *)
(* TODO. only add implicit 'holes' at the very end when subsituting metavariables.*)
let add_metavars x ty =
  if is_binder Pi ty then
    let ys = mk_mvars ty in
    let mvs = List.map (fun (Some str, _, _) -> Meta str) ys in
    (appvar x mvs, ys)
  else (Var x, [])

let elaborate_var sigg ctx str =
  add_metavars str (lookup_typ_global sigg ctx str)

let rec elaborate_term
  (cmds : cc_command list) (ctx : cc_context) (bvs : cc_context)
  (trm : cc_term) : (cc_term * cc_context) =
  match trm with
  | (Univ _|Meta _|Literal _) -> (trm, [])
  | Bound i -> (lookup_bvar ctx i, [])
  | Var str -> elaborate_var cmds ctx str
  | App (e1,e2) ->
    let (e1', c1) = elaborate_term cmds ctx bvs e1 in
    let (e2', c2) = elaborate_term cmds ctx bvs e2 in
    (App (e1',e2'), c1 @ c2)
  | Bind (bb, (x, ty, att), trm') ->
    let (ty', c1) = elaborate_term cmds ctx bvs ty in
    let ctx' = (x, ty', att) :: ctx in
    let (trm'', c2) = elaborate_term cmds ctx' ((x,ty',att)::bvs) trm' in
    (Bind (bb, (x, ty', att), trm''), c1 @ c2)

(* TODO. reimplement using sets rather than lists to avoid constraint duplication*)
module Equation = struct
  type t = (cc_term * cc_term)
  let compare = compare
end

module EqSet = Set.Make(Equation)
type eq_set = EqSet.t

let string_of_equations (eqs : eq_set) =
  begin let eq_str : Equation.t -> string =
    (fun (t1,t2) ->
      Printf.sprintf "%s ≡ %s"
      (string_of_term t1) (string_of_term t2)
    )
  in
    Printf.sprintf "⦃ %s ⦄"
      (String.concat "; " (List.map eq_str (EqSet.to_list eqs)))
  end

let rec infer_type
    (sigg : cc_signature) (ctx : cc_context) (t : cc_term)
  : (cc_term * eq_set) =
  if (not (is_var t)) && !debug_inference then
    Printf.printf "⊢ %s : ??\n" (string_of_term t);

  begin match t with
  | Univ KIND -> failwith "Cannot infer type of KIND."
  | Univ TYPE -> (Univ KIND, EqSet.empty)
  | Literal l ->
    begin match l with
    | Numeral _ ->  (Option.get (lookup_lit sigg NUM), EqSet.empty)
    | Rational _ -> (Option.get (lookup_lit sigg RAT), EqSet.empty)
    | Decimal _ ->  (Option.get (lookup_lit sigg DEC), EqSet.empty)
    end

  | Implicit t -> infer_type sigg ctx t
  | Bound _ -> failwith "Encountered bound variable during type inference!"

  | (Var x|Meta x) ->
    let ty = lookup_typ_global sigg ctx x in
    if !debug_inference then
      Printf.printf "⊢ %s : %s\n"
      (string_of_term t) (string_of_term ty);
    (ty, EqSet.empty)

  | App(f, arg) ->
    let (f_ty, es) = infer_type sigg ctx f in
    begin match f_ty with
    | Bind (Pi, (_, ty, _), body) ->
        let (arg_ty, fs) = infer_type sigg ctx arg in
        let c' = if ty = arg_ty
          then EqSet.empty
          else EqSet.singleton (ty, arg_ty) in
        let body' = subst arg 0 body in
        (body', EqSet.union c' (EqSet.union es fs))
    | _ -> failwith "Applied function doesn't have a Pi-type."
    end

  | Bind(Lambda, (x,ty,att), body) ->
    let body' = Option.fold ~none:body ~some:(fun x -> (subst (Var x) 0 body)) x in
    let (body_type, es) = infer_type sigg ((x,ty,att)::ctx) body' in
    let lam_typ = mk_pi [(x,ty,att)] body_type in
    (lam_typ, es)

  | Bind(Pi, (x,ty,att), body) ->
    let (u1, es) = infer_type sigg ctx ty in
    if is_univ u1 then
      let ctx' = ((x,ty,att)::ctx) in
      let body' = Option.fold ~none:body ~some:(fun x -> (subst (Var x) 0 body)) x in
      let (u2, fs) = infer_type sigg ctx' body' in
      if is_univ u2 then (u2, EqSet.union es fs)
      else failwith "Type of Π-body not a universe."
    else failwith "Type of Π-parameter type not a universe."

  | Bind(Let, (x,def,att), body) ->
    let (def_ty, es) = infer_type sigg ctx def in
    let body' = Option.fold ~none:body ~some:(fun x -> (subst (Var x) 0 body)) x in
    let (ty, fs) = infer_type sigg ((x,def_ty,att)::ctx) body' in
    let ty' = subst def 0 ty in
    (ty', EqSet.union es fs)

end
(*substitution using de Brujin indices*)
and subst (trm : cc_term) (idx : int) (body : cc_term) : cc_term =
  match body with
  | Univ _ -> body
  | Var _  -> body
  | Meta _ -> body
  | Implicit t -> Implicit (subst trm idx t)
  | Bound j ->
    if j = idx then trm
    else if j > idx then Bound (j-1)
    else Bound j
  | App(t1, t2) ->
    App(subst trm idx t1, subst trm idx t2)
  | Bind(bb, (x,ty,att), exp) ->
      (* substitution under a binder: increment indices *)
      let ty' = subst trm idx ty in
      let exp' = subst trm (idx + 1) exp in
      Bind(bb, (x,ty',att), exp')
(* Normalization via beta-reduction.*)
and whnf (ctx : cc_context) (trm : cc_term) : cc_term =
  match trm with
  | App (Bind (Lambda,_,body), arg) ->
    whnf ctx (subst arg 0 body)
  | App(e1,e2) ->
    let (e1',e2') = (whnf ctx e1, whnf ctx e2) in
    begin match e1' with
    | Bind( Lambda,_,body) -> whnf ctx (subst e2' 0 body)
    | _ -> App (e1', e2')
    end
  | Bind(bb,(x,ty,att),body) ->
    let ty' = whnf ctx ty in
    let body' = whnf ctx body in
    Bind(bb, (x,ty',att), body')
  | _ -> trm

type msubst = (string * cc_term) list

let string_of_meta_subst (msub : msubst) =
  let fs = List.map (fun (v,t) ->
    string_of_term (Meta v) ^ " ↦ " ^ string_of_term t) in
  let s = String.concat "; " (fs msub) in
  Printf.sprintf "⦃ %s ⦄" s

let rec app_msubst (msub : msubst) (trm : cc_term) (imp : bool) : cc_term =
  match trm with
  | Univ u  -> Univ u
  | Var x   -> Var x
  | Bound i -> Bound i
  | Implicit t -> Implicit (app_msubst msub t imp)
  | Meta s ->
    begin match List.assoc_opt s msub with
    | Some t -> if imp then Implicit t else t
    | None -> Meta s
    end
  | App (e1,e2) -> App (app_msubst msub e1 imp, app_msubst msub e2 imp)
  | Bind (bb, (x, ty, att), body) ->
      Bind (bb,
        (x, app_msubst msub ty imp, att),
        app_msubst msub body imp
      )

let rec unify (ctx : cc_context) (cs : Equation.t list) (msub : msubst) : msubst =
  match cs with
  | [] -> msub
  | (t,u) :: js ->
    (* 1. Apply current substitution & whnf. *)
    let t' = whnf ctx (app_msubst msub t false) in
    let u' = whnf ctx (app_msubst msub u false) in
    let msub_cs f = List.map (fun (m, t) -> (m, app_msubst f t false)) in
    match (t', u') with
    | (Meta m, Meta m') when m = m' -> unify ctx js msub

    | (Meta m, _) ->
        if occurs_check m u' then
          failwith "Occurs check failure"
        else
          let msub' = (m, u') :: msub in
          unify ctx (msub_cs msub' js) msub'

    | (_, Meta m) ->
        if occurs_check m t' then
          failwith "Occurs check failure"
        else
          let msub' = (m, t') :: msub in
          unify ctx (msub_cs msub' js) msub'

    | (App(f1, a1), App(f2, a2)) ->
        (* unify the heads, unify the arguments *)
        unify ctx ((f1, f2) :: (a1, a2) :: js) msub

    | (Implicit t, _) ->
        unify ctx ((t, u') :: js) msub

    | (_, Implicit u) ->
        unify ctx ((t', u) :: js) msub

    | (Bind(bb1, (_, tA1, att1), b1), Bind(bb2,(_, tA2, att2), b2))
      when bb1 = bb2 && att1 = att2 ->
        unify ctx ((tA1, tA2) :: (b1,b2) :: js) msub

    | (Univ u1, Univ u2) when u1 = u2 ->
        unify ctx js msub

    | (Var x, Var y) when x = y ->
        unify ctx js msub

    | _ ->
        failwith "Unification failure"

(* Does meta variable `m` occur in `term`? If so, return true; else false. *)
and occurs_check (m : string) (term : cc_term) : bool =
  match term with
  | Implicit t -> occurs_check m t
  | Univ _ -> false
  | Var _ -> false
  | Meta x -> (x = m)
  | Bound _ -> false
  | App (t1, t2) -> occurs_check m t1 || occurs_check m t2
  | Bind (_, (_, x_typ, _), body) ->
    occurs_check m x_typ || occurs_check m body

let infer sigg ctx bvs trm =
  if !debug_inference then
    Printf.printf "Begin inferring type of %s\n" (string_of_term trm);
  mvar_count := 0;
  let (trm', mvar_typs) = elaborate_term sigg ctx bvs trm in
  if !debug_inference && trm' <> trm then
    Printf.printf "Elaborated term to %s\n" (string_of_term trm');

  let (typ, eqs) = infer_type sigg (mvar_typs @ ctx) trm' in
  if !debug_inference then
    Printf.printf "Found type %s with constraints %s\n"
    (string_of_term typ) (string_of_equations eqs);

  let msub = unify ctx (List.rev (EqSet.to_list eqs)) [] in
  if !debug_inference then
    Printf.printf "Found unifier %s\n" (string_of_meta_subst msub);

  app_msubst msub typ false

let rec expand_defs (defs : (string * cc_term) list) (trm : cc_term) : cc_term =
  map_cc_term (fun _ str ->
    match List.assoc_opt str defs with
    | Some trm -> expand_defs defs trm
    | None -> Var str
  ) [] trm

let infer_term sigg ctx defs trm =
  mvar_count := 0;
  if !debug_inference then
    Printf.printf "Begin elaboration of %s via type inference.\n"
      (string_of_term trm);

  let (trm', mvar_typs) = elaborate_term sigg ctx [] trm in
  if !debug_inference && trm' <> trm then
    Printf.printf "Elaborated term to %s\n" (string_of_term trm');

  let (typ, eqs) = infer_type sigg (mvar_typs @ ctx) trm' in
  let eqs' = EqSet.map (fun (t,t') -> (expand_defs defs t, expand_defs defs t')) eqs in

  if !debug_inference then
    Printf.printf "Found type %s with constraints %s\n"
    (string_of_term typ) (string_of_equations eqs');

  let msub = unify ctx (List.rev (EqSet.to_list eqs')) [] in
  if !debug_inference then
    Printf.printf "Found unifier %s\n" (string_of_meta_subst msub);

  app_msubst msub trm' true
