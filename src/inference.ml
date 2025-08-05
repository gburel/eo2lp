open Ast_cc
open Ast

let debug_inference = ref false

module IntMap = Map.Make(Int)
type mvar_context = cc_term IntMap.t

(*
  Implicit variables only come from applications of (free) variables whose types
  have implicit Pi-bindings. Hence, we elaborate terms by finding each variable `x`
  with this property, generating fresh metavariables `?a1 .. ?an` with types
  `t1 .. tn`, and replacing `x` with `x ?a1 .. ?an. We also return the list of
  all of the metavariables generated paired with their types.
  *)
let elaborate_term (ctx : cc_context) (trm : cc_term) : (cc_term * mvar_context) =
  let mctx = ref IntMap.empty in

  let rec gen_mvars (trm : cc_term) : (int * cc_term) list =
    match trm with
    | Bind (Pi, (_, ty, atts), trm') when atts.implicit ->
      let idx = IntMap.cardinal !mctx in
      mctx := IntMap.add idx ty !mctx;
      (idx,ty) :: (gen_mvars trm')
    | _ -> []
  in

  let rec elab_vars ctx bvs (trm : cc_term) =
    match trm with
    | (Univ _|Meta _|Literal _) -> trm
    | Explicit t -> Explicit (elab_vars ctx bvs t)
    (* Elaborate bound variable by looking up index. Maybe don't do this here.*)
    | Bound i -> lookup_bvar bvs i
    (* Elaborate free variable by possibly generating metavariables. *)
    | Var str ->
        let mvars = gen_mvars (lookup_type ctx str) in
        appvar str (List.map (fun (idx,_) -> Meta idx) mvars)
    | App (e1,e2) -> App (
        elab_vars ctx bvs e1,
        elab_vars ctx bvs e2
      )
    | Bind (bb, (x, ty, att), trm') ->
      let ty'   = elab_vars ctx bvs ty in
      let trm'' = elab_vars ctx ((x,ty',att)::bvs) trm' in
      Bind (bb, (x, ty', att), trm'')
  in

  let trm' = elab_vars ctx [] trm in
  (trm', !mctx)

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

let string_of_lcat (lcat : lit_category) =
  match lcat with
  | NUM -> "NUM"
  | RAT -> "RAT"
  | DEC -> "DEC"

let infer_lcat (lit : literal) =
  match lit with
  | Numeral _  -> NUM
  | Rational _ -> RAT
  | Decimal _  -> DEC

let rec subst (trm : cc_term) (idx : int) (body : cc_term) : cc_term =
  match body with
  | Univ _ -> body
  | Var _  -> body
  | Meta _ -> body
  | Explicit t -> Explicit (subst trm idx t)
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

let strip_binder ctx trm : (cc_context * cc_term) =
  match trm with
  | Bind (_,(str_opt, ty, att), body) ->
    Option.fold
      ~none:(ctx,body)
      ~some:(fun str -> (
          StrMap.add str (Some str, ty, att) ctx,
          subst (Var str) 0 body )
        ) str_opt
  | _ -> (ctx, trm)


let rec infer_type (ctx : cc_context) (mctx : mvar_context) (trm : cc_term)
  : (cc_term * eq_set) =

  if (not (is_var trm)) && !debug_inference then
    Printf.printf "⊢ %s : ??\n" (string_of_term trm);

  begin match trm with
  | Univ KIND -> failwith "Cannot infer type of KIND."
  | Univ TYPE -> (Univ KIND, EqSet.empty)
  | Literal lit ->
      let lcat = infer_lcat lit in
      begin match lookup_lit ctx lcat with
      | Some (_,ty,_) -> (ty, EqSet.empty)
      | None -> failwith (
          Printf.sprintf "Literal category %s not bound to a type."
          (string_of_lcat lcat)
        )
      end
  | Explicit t -> infer_type ctx mctx t
  | Bound _ -> failwith "Encountered bound variable during type inference!"

  | Var str ->
    let ty = lookup_type ctx str in
    if !debug_inference then
      Printf.printf "⊢ %s : %s\n" (string_of_term trm) (string_of_term ty);
    (ty, EqSet.empty)

  | Meta idx ->
      begin match IntMap.find_opt idx mctx with
      | Some ty -> (ty, EqSet.empty)
      | None -> failwith (Printf.sprintf "Metavariable ?%d not found in context." idx)
      end

  | App(f, arg) ->
      let (f_ty, es) = infer_type ctx mctx f in
      begin match f_ty with
      | Bind (Pi, (_, ty, _), body) ->
          let (arg_ty, fs) = infer_type ctx mctx arg in
          let c' = if ty = arg_ty
            then EqSet.empty
            else EqSet.singleton (ty, arg_ty) in
          let body' = subst arg 0 body in
          (body', EqSet.union c' (EqSet.union es fs))
      | _ -> failwith "Applied function doesn't have a Pi-type."
      end

  | Bind(Lambda, x, _) ->
    let (ctx', body') = strip_binder ctx trm in
    let (body_ty, es) = infer_type ctx' mctx body' in
    let lam_typ = mk_pi [x] body_ty in
    (lam_typ, es)

  | Bind(Pi, (_,ty,_), _) ->
    let (u1, es) = infer_type ctx mctx ty in
    if is_univ u1 then
      let (ctx', body') = strip_binder ctx trm in
      let (u2, fs) = infer_type ctx' mctx body' in
        if is_univ u2 then (u2, EqSet.union es fs)
        else failwith "Type of Π-body not a universe."
    else failwith "Type of Π-parameter type not a universe."

  | Bind(Let, (str_opt,def,att), body) ->
    let (def_ty, es) = infer_type ctx mctx def in
    (* strip binder, but use inferred type of letvar *)
    let (ctx', body') = Option.fold
      ~none:(ctx,body)
      ~some:(fun str -> (
          StrMap.add str (Some str, def_ty, att) ctx,
          subst (Var str) 0 body
        )
      ) str_opt
    in
    let (ty, fs) = infer_type ctx' mctx body' in
    let ty' = subst def 0 ty in
    (ty', EqSet.union es fs)
end

(* Normalization via beta-reduction.*)
and whnf (ctx : cc_context) (trm : cc_term) : cc_term =
  match trm with
  | App (Bind (Lambda,_,body), arg) -> whnf ctx (subst arg 0 body)
  | App(e1,e2) ->
    let (e1',e2') = (whnf ctx e1, whnf ctx e2) in
    begin match e1' with
    | Bind(Lambda,_,body) -> whnf ctx (subst e2' 0 body)
    | _ -> App (e1', e2')
    end
  | Bind(bb,(x,ty,att),body) ->
    let ty' = whnf ctx ty in
    let body' = whnf ctx body in
    Bind(bb, (x,ty',att), body')
  | _ -> trm

let string_of_mctx (mctx : mvar_context) =
  let to_str = (fun (idx,t) ->
    Printf.sprintf "?%d ↦ %s" idx (string_of_term t)) in
  let s = String.concat "; " (List.map to_str (IntMap.to_list mctx)) in
    Printf.sprintf "⦃ %s ⦄" s

let rec app_mctx (mctx : mvar_context) (trm : cc_term) (imp : bool) : cc_term =
  match trm with
  | Univ u  -> Univ u
  | Var x   -> Var x
  | Bound i -> Bound i
  | Explicit t -> Explicit (app_mctx mctx t imp)
  | Meta idx ->
    begin match IntMap.find_opt idx mctx with
    | Some t -> if imp then Explicit t else t
    | None -> Meta idx
    end
  | App (e1,e2) -> App (app_mctx mctx e1 imp, app_mctx mctx e2 imp)
  | Bind (bb, (x, ty, att), body) ->
      Bind (
        bb, (x, app_mctx mctx ty imp, att),
        app_mctx mctx body imp
      )

let rec unify (ctx : cc_context) (eqs : Equation.t list)
  (mctx : mvar_context) (defs : cc_term StrMap.t)
  : mvar_context =
  match eqs with
  | [] -> mctx
  | (t,u) :: js ->
    (* 1. Apply current substitution & whnf. *)
    let t' = whnf ctx (app_mctx mctx t false) in
    let u' = whnf ctx (app_mctx mctx u false) in
    let mctx_cs f = List.map (fun (m, t) -> (m, app_mctx f t false)) in
    match (t', u') with
    | (Meta m, Meta m') when m = m' -> unify ctx js mctx defs

    | (Meta m, _) ->
        if occurs_check m u' then
          failwith "Occurs check failure"
        else
          let mctx' =  IntMap.map (fun trm ->
            app_mctx (IntMap.singleton m u') trm false
            ) mctx
          in
          let mctx' = IntMap.add m u' mctx' in
          unify ctx (mctx_cs mctx' js) mctx' defs

    | (_, Meta m) ->
        if occurs_check m t' then
          failwith "Occurs check failure"
        else
          let mctx' =  IntMap.map (fun trm ->
            app_mctx (IntMap.singleton m t') trm false
            ) mctx
          in
          let mctx' = IntMap.add m t' mctx' in
          unify ctx (mctx_cs mctx' js) mctx' defs

    | (App(f1, a1), App(f2, a2)) ->
        (* unify the heads, unify the arguments *)
        unify ctx ((f1, f2) :: (a1, a2) :: js) mctx defs

    | (Explicit t, _) ->
        unify ctx ((t, u') :: js) mctx defs

    | (_, Explicit u) ->
        unify ctx ((t', u) :: js) mctx defs

    | (Bind(bb1, (_, tA1, att1), b1), Bind(bb2,(_, tA2, att2), b2))
      when bb1 = bb2 && att1 = att2 ->
        unify ctx ((tA1, tA2) :: (b1,b2) :: js) mctx defs

    | (Univ u1, Univ u2) when u1 = u2 ->
        unify ctx js mctx defs

    | (Var x, Var y) when x = y ->
        unify ctx js mctx defs

    | (_, Var str) ->
      begin match StrMap.find_opt str defs with
      | Some def -> unify ctx ((t', def) :: js) mctx defs
      | None -> failwith "Unification failure!"
      end

    | (Var str, _) ->
      begin match StrMap.find_opt str defs with
      | Some def -> unify ctx ((def, t') :: js) mctx defs
      | None -> failwith "Unification failure!"
      end

    | _ ->
        failwith "Unification failure"

(* Does meta variable `m` occur in `term`? If so, return true; else false. *)
and occurs_check (m : int) (term : cc_term) : bool =
  match term with
  | Explicit t -> occurs_check m t
  | Univ _ -> false
  | Var _ -> false
  | Meta x -> (x = m)
  | Bound _ -> false
  | App (t1, t2) -> occurs_check m t1 || occurs_check m t2
  | Bind (_, (_, x_typ, _), body) ->
    occurs_check m x_typ || occurs_check m body

let infer ctx trm =
  if !debug_inference then
    Printf.printf "\nBegin inferring type of %s\n" (string_of_term trm);

  let (trm', mctx) = elaborate_term ctx trm in
  if !debug_inference && trm' <> trm then
    Printf.printf "Elaborated term to %s\n" (string_of_term trm');

  let (typ, eqs) = infer_type ctx mctx trm' in
  if !debug_inference then
    Printf.printf "Found type %s with constraints %s\n"
    (string_of_term typ) (string_of_equations eqs);

  let mctx = unify ctx (EqSet.to_list eqs) IntMap.empty StrMap.empty in
  if !debug_inference then
    Printf.printf "Found unifier %s\n" (string_of_mctx mctx);

  app_mctx mctx typ false

let infer_term ctx defs trm =
  if !debug_inference then
    Printf.printf "\nBegin elaboration of %s via type inference.\n"
      (string_of_term trm);

  let (trm', mctx) = elaborate_term ctx trm in
  if !debug_inference && trm' <> trm then
    Printf.printf "Elaborated term to %s\n" (string_of_term trm');

  let (typ, eqs) = infer_type ctx mctx trm' in
  (* let eqs' = EqSet.map (fun (t,t') ->
    (expand_defs defs t, expand_defs defs t')) eqs in *)
  if !debug_inference then
    Printf.printf "Found type %s with constraints %s\n"
    (string_of_term typ) (string_of_equations eqs);

  let mctx = unify ctx (EqSet.to_list eqs) IntMap.empty defs in
  if !debug_inference then
    Printf.printf "Found unifier %s\n" (string_of_mctx mctx);

  app_mctx mctx trm' true
