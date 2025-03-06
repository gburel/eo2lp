open Ast
open Ast_cc
open Inference

(* open Prelude *)

type tdata = {
  asserts : int;
  rschema : (string * (cc_context * (cc_term * cc_term) list)) list;
  signature : cc_signature;
}

let tdata_init =
  let init =
    let typ = mk_pi
      [
        (Some "S", Univ TYPE, { implicit=true; list=false });
        (None, Var "S", { implicit=false; list=false })
      ]
        (Univ TYPE)
    in
      [
        Prog ("eo::typeof", typ);
        Const ("Bool", Univ TYPE, None);
        Const ("Proof", mk_pi_nameless [Var "Bool"] (Univ TYPE), None);
      ]
  in
  {
    asserts = 0;
    rschema = [];
    signature = init;
  }

let tdata_ref = ref tdata_init

(* during declaration translation, we (globally) track:
   name of current declaration, program declarations for encountered matches, and a context.*)
type ddata = {
  decl_name : string;
  matches : int;
  match_progs : cc_command list
}

let ddata_init = {
  decl_name = "";
  matches = 0;
  match_progs = []
}

let ddata_ref = ref ddata_init

let eo_decl_attr (attr : attr list) : param_attr =
  {
    implicit = List.mem_assoc "implicit" attr;
    list = List.mem_assoc "list" attr;
  }

let rec eo_cc_term (ctx : cc_context) (bvs : cc_context) (trm : eo_term) : cc_term =
  begin match trm with
  | Literal l -> Literal l
  | Symbol str ->
    if str = "Type" then
      Univ TYPE
    else (*TODO. implement Rish's hashmap trick. *)
      begin match List.find_index (fun (x,_,_) -> x = Some str) bvs with
        | Some n -> Bound n
        | None -> Var str
      end
  | Define (vs, body) -> eo_define_cc ctx bvs vs body
  | AppList (str, args) ->
    begin match str with
      | "->" -> eo_arrow_cc ctx bvs args
      | _ ->
        let args' = List.map (eo_cc_term ctx bvs) args in
        let att_opt = lookup_decl_attr !tdata_ref.signature str in
        (*The only attribute we care about in application is :list?
        But this isn't currently stored in the cc_context.
        Once again we need to refactor and store attributes in context. *)
        mk_app ctx (Var str) args' att_opt
    end
  | Attributed (trm, reqs, atts) ->
    begin match reqs with
    | [] -> eo_cc_term ctx bvs trm
    | rs -> eo_requires_cc ctx bvs rs (Attributed (trm, [], atts))
    end
  | Match (ps, trm, rs) -> eo_match_cc ctx bvs ps trm rs
  end

and eo_var_cc ctx bvs (str,ty,att) : param =
  let x = if str = "_" then None else Some str in
  (x, eo_cc_term ctx bvs ty, eo_decl_attr att)

and eo_define_cc ctx bvs vs trm =
  match vs with
  | [] -> eo_cc_term ctx bvs trm
  | v :: vs' ->
    let p = eo_var_cc ctx bvs v in
    let trm' = eo_define_cc ctx (p :: bvs) vs' trm in
    Bind (Let, p, trm')

and eo_requires_cc ctx bvs reqs trm =
  List.fold_left (fun acc (l,r) ->
    appvar "eo::requires"
      [
        eo_cc_term ctx bvs l;
        eo_cc_term ctx bvs r; acc
      ]
  ) (eo_cc_term ctx bvs trm) reqs

and eo_match_cc ctx bvs ps trm rs =
  begin
    let prog_name =
      Printf.sprintf "%s_match_%d"
      (!ddata_ref.decl_name) (!ddata_ref.matches) in

    let ps' = List.map (eo_var_cc ctx bvs) ps in
    let ctx' = ps' @ ctx in

    (* Infer types of lhs/rhs of first rule, wrt.
    locally-bound variables, and global constants. *)
    let rs' = List.map (eo_cc_rule ctx' bvs) rs in
    let (lhs,rhs) = List.hd rs' in
    let (ty_lhs, ty_rhs) =
      (infer !tdata_ref.signature ctx' bvs lhs,
       infer !tdata_ref.signature ctx' bvs rhs)
    in
    let prog_ty_raw = mk_pi_nameless [ty_lhs] ty_rhs in

    (* Collect all variables are bound (e.g., by a lambda or pi),
       or locally scoped (e.g., in a rule declaration. )    *)
    let rule_trms = List.concat_map (fun (l,r) -> [l;r]) rs' in
    let bound_params = map_bvars_list bvs rule_trms in
    let free_params = map_filter_vars_list ctx rule_trms in
    let prog_ty = mk_pi (bound_params @ free_params) prog_ty_raw in

    let bound_vars = List.map param_var bound_params in
    let free_vars = List.map param_var free_params in

    let prog_app = appvar prog_name (bound_vars @ free_vars)
 in
    let prog_rules = List.map
      (fun (l,r) -> (App (prog_app, l), r)) rs' in
    let prog_sig =
      [
        Prog (prog_name, prog_ty);
        Rule (ps' @ bound_params @ free_params, prog_rules)
      ]
    in

    (* Add match program declarations and increment counter in per-declaration ref. *)
    ddata_ref := { !ddata_ref with
      matches = !ddata_ref.matches + 1;
      match_progs = prog_sig @ !ddata_ref.match_progs;
    };

    (* Add program declarations to signature in global ref. *)
    Printf.printf "%s\n" (string_of_sig prog_sig);
    tdata_ref := { !tdata_ref with
      signature = prog_sig @ !tdata_ref.signature
    };

    (* Make correct indices for bound variables within match rules to be exported. *)
    let bounds = List.map (fun (x,_,_) ->
      match List.find_index (fun (y,_,_) -> x = y) bvs with
      | Some n -> Bound n
      | None -> Var (Option.get x)
    ) bound_params in

    (* Return application of auxillary program to matched term. *)
    App (
      appvar prog_name (bounds @ free_vars),
      eo_cc_term ctx bvs trm
    )
  end

and eo_arrow_cc ctx bvs args =
  match args with
  | []        -> failwith "Nothing applied to (->)."
  | [typ]     -> eo_cc_term ctx bvs typ
  | (typ::ts) ->
    let p = eo_var_cc ctx bvs (mk_eo_var typ) in
    Bind (Pi, p, eo_arrow_cc ctx (p::bvs) ts)

and eo_cc_rule ctx bvs (lhs,rhs) =
  (eo_cc_term ctx bvs lhs, eo_cc_term ctx bvs rhs)

let eo_decl_attr ctx bvs (att : attr) =
  match att with
  | ("right-assoc", None) -> RightAssoc
  | ("left-assoc", None)  -> LeftAssoc
  | ("right-assoc-nil", Some trm) -> RightAssocNil (eo_cc_term ctx bvs trm)
  | ("left-assoc-nil", Some trm) -> LeftAssocNil (eo_cc_term ctx bvs trm)
  | ("chainable", Some trm) -> Chainable (eo_cc_term ctx bvs trm)
  | ("pairwise",  Some trm) -> Pairwise (eo_cc_term ctx bvs trm)
  | ("binder",    Some trm) -> Binder (eo_cc_term ctx bvs trm)
  | _ -> failwith "Unknown declaration attribute."


let base_cmd_cc (cmd : base_command) : cc_command list =
  match cmd with
  | Assert trm ->
    let aname = "assert_" ^ string_of_int(!tdata_ref.asserts + 1) in
    ddata_ref := { !ddata_ref with decl_name = aname };
    tdata_ref := { !tdata_ref with asserts = !tdata_ref.asserts + 1 };
    let typ = appvar "Proof" [eo_cc_term [] [] trm] in

    [ Const (aname, typ, None) ]

  | DeclareConst (str, typ, atts) ->
    let
      typ' = eo_cc_term [] [] typ and
      att_opt =
        match atts with
        | [] -> None
        | att::[] -> Some (eo_decl_attr [] [] att)
        | _ -> failwith "More than one declaration attribute."
    in

    let assoc_rules =
      match att_opt with
      | Some (RightAssocNil nil) ->
        (* Gather all program-schema with right-assoc-nil attribute. *)
        let schema_cs = List.filter_map (fun (str, rs) ->
            if str = "right-assoc-nil" then Some rs else None
          ) !tdata_ref.rschema
        in
          List.map (fun (ctx, rs) ->
            mvar_count := 0;
            let (cons, mvar_ctx) =
              elaborate_var (!tdata_ref.signature) [mk_param str typ'] str
            in
              Rule (ctx @ mvar_ctx,
                inst_schema rs [("#cons", cons); ("#nil", nil)])
          ) schema_cs
      | _ -> []
    in
      [ Const (str, typ', att_opt) ] @ assoc_rules

  | DefineConst (str, trm) ->
    (* TODO. infer type here *)
    let trm' = eo_cc_term [] [] trm in
    [ Const (str, trm', None) ]

  | DeclareType (str, tys) ->
    let typ' = eo_arrow_cc [] [] (tys @ [Symbol "Type"]) in
    [ Const (str, typ', None) ]

  | DefineType _ -> failwith "DefineType"
  | DeclareFun _ -> failwith "DeclareFun"
  | DefineFun _ -> failwith "DefineFun"
  | DefineFunRec _ -> failwith "DefineFunRec"
  | DefineFunsRec _ -> failwith "DefineFunsRec"
  | DeclareSort _ -> failwith "DeclareSort"
  | DefineSort _ -> failwith "DefineSort"
  | DeclareDatatype _ -> failwith "DeclareDatatype"
  | DeclareDatatypes _ -> failwith "DeclareDatatypes"

let eunoia_cmd_cc (cmd : eunoia_command) =
  match cmd with
  (* TODO. check for :type attribute. *)
  | Define (str, vs, trm) ->
    let rec eo_lambda_cc ctx bvs (vs : eo_var list) body =
      match vs with
      | [] -> eo_cc_term ctx bvs body
      | v::vs' ->
        let v' = eo_var_cc ctx bvs v in
        Bind (Lambda, v', eo_lambda_cc ctx (v'::bvs) vs' body)
    in
    let trm' = eo_lambda_cc [] [] vs trm in
    (* infer type here *)
    [ Defn (str, infer (!tdata_ref.signature) [] [] trm', trm') ]

  | DeclareRule (str, ps, rspec) ->
    let ctx = List.map (eo_var_cc [] []) ps in
    let concl_bool = eo_cc_term ctx [] rspec.conclusion in
    let concl = appvar "Proof" [concl_bool] in

    let rule_typ_body =
      begin match rspec.prems with
      | Some (Premises ts) ->
        let prem_tys = List.map (fun t ->
          appvar "Proof" [eo_cc_term ctx [] t]) ts
        in
          mk_pi_nameless prem_tys concl
      | Some (PremiseList (trm,op)) ->
        let prem_trm = eo_cc_term ctx [] trm in
        let op_trm = eo_cc_term ctx [] op in
        appvar "If" [
          appvar "eo::is_list" [op_trm; prem_trm];
          mk_pi_nameless [appvar "Proof" [prem_trm]] concl
        ]
      | None -> concl
      end
    in

    (* TODO. do something meaningful on PremiseList *)
    let prem_ptrns =
      begin match rspec.prems with
      | Some (Premises ts) -> List.map (eo_cc_term ctx []) ts
      | Some (PremiseList (trm,_)) -> [ eo_cc_term ctx [] trm ]
      | None -> [ ]
      end
    in
    let prop_ptrns = prem_ptrns @ [eo_cc_term ctx [] rspec.conclusion] in
    let arg_ptrns = Option.fold
      ~none:[] ~some:(List.map (eo_cc_term ctx []))
      rspec.arguments
    in

    (* step 1. create type signature and rewrite rule for auxillary.*)
    (* calculate type of each pattern under current signature and context.*)
    let prop_tys = List.map
      (fun _ -> Var "Bool") prop_ptrns in
    let arg_tys = List.map
      (infer (!tdata_ref.signature) ctx []) arg_ptrns in

    let aux_params = ParamSet.to_list
      (ParamSet.diff
        (filter_vars ctx rule_typ_body)
        (map_filter_vars ctx arg_ptrns)
      )
    in
    let aux_str = str ^ "_aux" in
    let aux_typ_body =
      mk_pi_nameless arg_tys (
        mk_pi aux_params (Var "Bool")
      )
    in
    let aux_typ = close_term ctx aux_typ_body in

    let aux_param_vars = List.map param_var aux_params in
    (* elaborate lhs/rhs with explicits where needed.*)
    let ctx' = (mk_param aux_str aux_typ) :: ctx in
    let rw_rules = map_cc_rule
      (infer_term (!tdata_ref.signature) ctx' [])
      [(appvar aux_str (arg_ptrns @ aux_param_vars), concl_bool)]
    in
    let aux_decl = [ Prog (aux_str, aux_typ); Rule (ctx, rw_rules) ] in
    (* step 2. create signature for main inference rule. *)
      (* create parameters for each arg-pattern *)
    let arg_params = List.mapi (fun i ty ->
      mk_param ("x" ^ string_of_int i) ty
    ) arg_tys
    in
      (* let str =
        if i < List.length arg_tys then
          "x" ^ string_of_int i
        else if i < List.length arg_tys + List.length prop_tys - 1 then
          "p" ^ string_of_int (i - List.length arg_tys)
        else
          "q"
      in *)

    (* eta-expand auxillary function.*)
    let aux_vars = List.map param_var (arg_params @ aux_params) in
    let aux_app =  appvar "Proof" [appvar aux_str aux_vars] in
    let rule_typ_raw = mk_pi_implicit aux_params
      (
        mk_pi_nameless
          (List.map (fun prop -> appvar "Proof" [prop]) prem_ptrns)
          (mk_pi arg_params aux_app)
      )
    in
    let rule_typ = close_term ctx rule_typ_raw in

    aux_decl @ [ Const (str, rule_typ, None) ]

  | DeclareConsts (lcat, eo_typ) ->
    [ LitTy (lcat, eo_cc_term [] [] eo_typ)]

  | DeclareParamConst _ -> failwith "undefined"
  | DeclareOracleFun _ -> failwith "undefined"
  | Include _ -> []
  | Program (str, att_str_opt, eo_ps, dom_tys, ran_ty, eo_rs) ->
    let params = List.map (eo_var_cc [] []) eo_ps in
    let ty_raw = eo_arrow_cc params [] (dom_tys @ [ran_ty]) in
    let ty_binds = List.map (fun (x,ty,p) ->
      (x, ty, {implicit = true; list = p.list}))
      (filter_vars_list params ty_raw) in

    let ty = mk_pi ty_binds ty_raw in
    let rs = List.map (eo_cc_rule params []) eo_rs in
    let ctx' = (mk_param str ty) :: params in
    let rs' = map_cc_rule (infer_term !tdata_ref.signature ctx' []) rs in

    begin match att_str_opt with
    | Some att_str ->
      tdata_ref := { !tdata_ref with
        rschema = (att_str, (params, rs)) :: !tdata_ref.rschema
      };

      let assocs = sig_assocs !tdata_ref.signature Right in
      let rule_insts = List.map (fun (Var cons_str, nil) ->
        mvar_count := 0;
        let (cons, mvar_ctx) =
          elaborate_var (!tdata_ref.signature)
          [mk_param cons_str ty] cons_str
        in
          Rule (
            params @ mvar_ctx,
            inst_schema rs [("#cons", cons); ("#nil", nil)]
          )
      ) assocs
      in
        Prog (str,ty) :: rule_insts

    | None -> [ Prog (str,ty); Rule (params, rs') ]
    end

  | Reference _ -> failwith "undefined"

let proof_prop (trm : cc_term) : cc_term =
  match trm with
  | Var str ->
    let typ = lookup_typ_global !tdata_ref.signature [] str in
    begin match typ with
    | App (Var "Proof", prop) -> prop
    | _ -> failwith (Printf.sprintf
        "Not a proof term: (%s : %s)"
        (string_of_term trm)(string_of_term typ)
      )
    end
  | _ -> failwith (Printf.sprintf "Not a variable: %s" (string_of_term trm))


let proof_cmd_cc (cmd : proof_command) : cc_command list =
  match cmd with
  | Assume (str, trm) ->
    let trm' = eo_cc_term [] [] trm in
    let typ = appvar "Proof" [trm'] in
    [ Const (str, typ, None) ]

  | Step (str, trm_opt, rule, prem_opt, arg_opt) ->
    (* make type of proof term *)
    let concl_prop = eo_cc_term [] [] (Option.get trm_opt) in
    let concl = appvar "Proof" [concl_prop] in
    (* now make definition/body *)

    let prems = match prem_opt with
      | Some (Premises ts) -> List.map (eo_cc_term [] []) ts
      | _ -> []
    in
    (* let prem_props = List.map proof_prop prems in *)
    let args = match arg_opt with
      | Some ts -> List.map (eo_cc_term [] []) ts
      | None -> []
    in
    let def = appvar rule (prems @ args) in
    let tdefs = List.filter_map (fun cmd ->
      match cmd with
      | Defn (str, _, trm) ->
          if String.starts_with ~prefix:"@t" str
          then Some (str, trm) else None
      | _ -> None
    ) !tdata_ref.signature in
    let def' = infer_term !tdata_ref.signature [] tdefs def in
    [ Defn (str, concl, def') ]

  | AssumePush _ -> failwith "undefined"
  | StepPop _ -> failwith "undefined"

let eo_cc (cmd : eo_command) =
  let () = match get_eo_name cmd with
  | Some str -> ddata_ref := { !ddata_ref with decl_name = str };
  | None -> (); in
  match cmd with
  | Base cmd -> base_cmd_cc cmd
  | EO cmd -> eunoia_cmd_cc cmd
  | Prf cmd -> proof_cmd_cc cmd
  | Ctrl _ -> []
