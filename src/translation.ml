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
  let eo_typeof =
    let typ = mk_pi
      [
        (Some "S", Univ TYPE, { implicit=true; list=false });
        (None, Var "S", { implicit=false; list=false })
      ]
        (Univ TYPE)
    in
      Decl ("eo::typeof", Some typ, None, None)
  in
  {
    asserts = 0;
    rschema = [];
    signature = { cmds = [eo_typeof]; ltyps = [] };
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
        let att_opt = lookup_decl_attr_opt !tdata_ref.signature str in
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
  (Some str, eo_cc_term ctx bvs ty, eo_decl_attr att)

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

    (* Create parameters for all bound variables appearing in rules. *)
    let bound_params = map_bvars_list bvs (List.map (fun (l,r) -> App (l,r)) rs') in
    let prog_ty = mk_pi bound_params prog_ty_raw in

    let prog_hd = appvar prog_name (List.map
        (fun (x,_,_) ->
          match List.find_index (fun (y,_,_) -> x = y) bvs with
          | Some n -> Bound n
          | None -> Var (Option.get x)
        ) bound_params) in
    let prog_rs = List.map (fun (l,r) -> (App (prog_hd, l), r)) rs' in
    let prog_sig =
      [
        Decl (prog_name, Some prog_ty, None, Some Sequential);
        Rule (ps', prog_rs)
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
      signature = { !tdata_ref.signature with
        cmds = prog_sig @ !tdata_ref.signature.cmds }
    };

    (* Return application of auxillary program to matched term. *)
    App (prog_hd, eo_cc_term ctx bvs trm)
  end

and eo_arrow_cc ctx bvs args =
  match args with
  | []        -> failwith "Nothing applied to (->)."
  | [typ]     -> eo_cc_term ctx bvs typ
  | (typ::ts) ->
    let p = eo_var_cc ctx bvs (mk_eo_var typ) in
    Bind (Pi, p, eo_arrow_cc ctx (p::bvs) ts)

and eo_cc_rule ctx bvs (lhs,rhs) = (eo_cc_term ctx bvs lhs, eo_cc_term ctx bvs rhs)

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
    [
      Decl (
        aname,
        Some (appvar "Proof" [eo_cc_term [] [] trm]),
        None,
        None
      )
    ]

  | DeclareConst (str, typ, atts) ->
    let typ' = eo_cc_term [] [] typ
    and att_opt = match atts with
      | [] -> None
      | att::[] -> Some (eo_decl_attr [] [] att)
      | _ -> failwith "More than one declaration attribute." in
    let rules = match att_opt with
      | Some (RightAssocNil nil) ->
        let schema_cs = List.filter_map (fun (str, rs) ->
            if str = "right-assoc-nil" then Some rs else None
          ) !tdata_ref.rschema
        in
          List.map (fun (ctx, rs) ->
            mvar_count := 0;
            let (cons, mvar_ctx) =
              elaborate_var true (!tdata_ref.signature)
                [(Some str, typ', {implicit = false; list = false})] str
            in
              Rule (ctx @ mvar_ctx,
                inst_schema rs [("#cons", cons); ("#nil", nil)])
          ) schema_cs
      | _ -> [] in
    [ Decl (str, Some typ', None, att_opt) ] @ rules

  | DefineConst (str, trm) ->
    let trm' = eo_cc_term [] [] trm in
    [ Decl (str, None, Some trm', None) ]

  | DeclareType (str, tys) ->
    let typ' = eo_arrow_cc [] [] (tys @ [Symbol "Type"]) in
    [ Decl (str, Some typ', None, None) ]

  | DefineType _ -> failwith "DefineType"
  | DeclareFun _ -> failwith "DeclareFun"
  | DefineFun _ -> failwith "DefineFun"
  | DefineFunRec _ -> failwith "DefineFunRec"
  | DefineFunsRec _ -> failwith "DefineFunsRec"
  | DeclareSort _ -> failwith "DeclareSort"
  | DefineSort _ -> failwith "DefineSort"
  | DeclareDatatype _ -> failwith "DeclareDatatype"
  | DeclareDatatypes _ -> failwith "DeclareDatatypes"

let exc_cmd_cc (cmd : exc_command) =
  match cmd with
  | Define (str, vs, trm) ->
    let rec eo_lambda_cc ctx bvs (vs : eo_var list) body =
      match vs with
      | [] -> eo_cc_term ctx bvs body
      | v::vs' ->
        let v' = eo_var_cc ctx bvs v in
        Bind (Lambda, v', eo_lambda_cc ctx (v'::bvs) vs' body)
    in
    let trm' = eo_lambda_cc [] [] vs trm in
    let typ = infer (!tdata_ref.signature) [] [] trm' in
    [
      Decl (str, Some typ, Some trm', None)
    ]

  | DeclareRule (str, ps, rspec) ->
    let prf_of = fun t -> appvar "Proof" [t] in
    let ctx = List.map (eo_var_cc [] []) ps in
    let concl_ty = prf_of (eo_cc_term ctx [] rspec.conclusion) in

    let rule_typ_raw =
      begin match rspec.prems with
      | Some (Premises ts) ->
          let prem_tys = List.map (fun t ->
            appvar "Proof" [eo_cc_term ctx [] t]) ts in
          mk_pi_nameless prem_tys concl_ty
      | Some (PremiseList (trm,op)) ->
          let prem_trm = eo_cc_term ctx [] trm in
          let op_trm = eo_cc_term ctx [] op in
          appvar "If" [
            appvar "eo::is_list" [op_trm; prem_trm];
            mk_pi_nameless [prf_of prem_trm] concl_ty
          ]
      | None -> concl_ty
      end
    in

    (* Get all parameters appearing in rules. *)
    let rule_params = filter_vars ctx rule_typ_raw in
    let rule_cmds =
      begin match rspec.arguments with
      (* If we have argument patterns, then we make a seperate symbol for the conclusion formula
      and define rules such that it evaluates iff its arguments match the patterns.  *)
      | Some eo_pts ->

        (*translate all argument patterns, get free variables.*)
        let pts = List.map (eo_cc_term ctx []) eo_pts in
        let pts_tys = List.map (infer (!tdata_ref.signature) ctx []) pts in
        let pt_params = map_filter_vars ctx pts in

        (* construct the rewrite rule for the auxillary function. *)
        let aux_explicits = ParamSet.to_list (ParamSet.diff rule_params pt_params) in
        let lhs = appvar (str ^ "_aux") (List.map param_var (aux_explicits) @ pts) in

        (* construct type for auxillary function. *)
        let aux_params = aux_explicits @ ParamSet.to_list pt_params in
        let aux_typ_raw = mk_pi aux_params (Univ TYPE) in
        let aux_implicits = List.map (fun (x,ty,p) ->
          (x, ty, {implicit = true; list = p.list})
          ) (filter_vars_list ctx aux_typ_raw) in
        let aux_typ = mk_pi aux_implicits aux_typ_raw in

        let arg_vars = List.mapi (fun i ty ->
            (Some ("_arg" ^ string_of_int (i+1)), ty,
            {implicit = false; list = false})
          ) pts_tys in

        let rule_typ_body = appvar (str ^ "_aux") (
          List.map param_var (aux_explicits @ arg_vars))
        in
        (* bind variables in type body. *)
        let rule_typ = mk_pi
          (aux_implicits @ aux_explicits @ arg_vars) rule_typ_body
        in

        [
          Decl (str ^ "_aux", Some aux_typ, None, None);
          Rule (ctx, [(lhs, rule_typ_raw)]);
          Decl (str, Some rule_typ, None, None)
        ]

      | None ->
        let rule_typ_binds = List.map (fun (x,ty,att) ->
            (x,ty,{implicit = true; list = att.list})
        ) (ParamSet.to_list rule_params)
        in

        let rule_typ = mk_pi rule_typ_binds rule_typ_raw in
          [ Decl (str, Some rule_typ, None, None) ]
      end
    in
      rule_cmds

  | DeclareConsts (lit_cat, eo_typ) ->
    let typ = eo_cc_term [] [] eo_typ in
    tdata_ref := { !tdata_ref with signature =
      { !tdata_ref.signature with ltyps =
          (lit_cat, typ) :: !tdata_ref.signature.ltyps
      }
    }; []

  | DeclareParamConst _ -> failwith "undefined"
  | DeclareOracleFun _ -> failwith "undefined"
  | Include _ -> []
  | Program (str, att_str_opt, eo_ps, dom_tys, ran_ty, eo_rs) ->
    let ctx = List.map (eo_var_cc [] []) eo_ps in
    let ty_raw = eo_arrow_cc ctx [] (dom_tys @ [ran_ty]) in
    let ty_binds = List.map (fun (x,ty,p) ->
      (x, ty, {implicit = true; list = p.list})
      ) (filter_vars_list ctx ty_raw) in
    let ty = mk_pi ty_binds ty_raw in
    let prog_decl = Decl (str, Some ty, None, Some Sequential) in

    let rs = List.map (eo_cc_rule ctx []) eo_rs in
    let rs' = map_cc_rule (infer_term (
      {!tdata_ref.signature with cmds = prog_decl :: !tdata_ref.signature.cmds }) ctx) rs in

    begin match att_str_opt with
      | Some str ->
        tdata_ref := { !tdata_ref with
          rschema = (str, (ctx, rs)) :: !tdata_ref.rschema
        };

        let att_cmds = sig_filter_attr (!tdata_ref.signature.cmds) str in
        let rule_insts = List.filter_map (fun cmd ->
          begin match cmd with
            | Decl (str, Some typ, _, Some (RightAssocNil nil)) ->
              mvar_count := 0;
              let (cons,mvar_ctx) = elaborate_var true
                (!tdata_ref.signature)
                [(Some str, typ, {implicit=false; list=false})] str in
              let sub = [("#cons", cons); ("#nil", nil)] in
              Some (Rule (ctx @ mvar_ctx, inst_schema rs sub))
            | _ -> None
          end
        ) att_cmds
        in
          [ prog_decl ] @ rule_insts

      | None -> [prog_decl; Rule (ctx, rs') ]
    end

  | Reference _ -> failwith "undefined"

let eo_cc (cmd : eo_command) =
  let () = match get_eo_name cmd with
  | Some str -> ddata_ref := { !ddata_ref with decl_name = str };
  | None -> (); in
  match cmd with
  | Base cmd -> base_cmd_cc cmd
  | EO cmd -> exc_cmd_cc cmd
  | Ctrl _ -> []
  | Prf _ -> []
