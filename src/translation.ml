open Ast
open Ast_cc
open Inference

type translation_data = {
  mutable asserts : int;
  mutable rschema : (string * (param list * (cc_term * cc_term) list)) list;
  mutable context : cc_context;
  mutable signature : cc_signature;
  mutable filepath : string;
  mutable deps : StrSet.t StrMap.t;
}

let normalize_path (ipath : string) (fpath : string) =
  let fpath' = Filename.dirname fpath in
  let delim = Filename.dir_sep in
  let dirs = String.split_on_char (delim.[0])
    (Filename.chop_extension ipath) in
  let rec move fp = function
  | (".." :: xs) -> move (Filename.dirname fp) xs
  | xs -> (fp, xs)
  in
  let (fpath'', dirs') = move fpath' dirs in
  let fpath_dirs = String.split_on_char (delim.[0]) fpath'' in
  String.concat "." ((List.tl fpath_dirs) @ dirs')

let tdata =
  let init =
    let typ = mk_pi
      [
        (Some "S", Univ TYPE, {atts_init with implicit=true});
        (None, Var "S", atts_init)
      ]
        (Univ TYPE)
    in
      [
        Prog ("eo::typeof", typ);
        Const ("Bool", Univ TYPE);
        Const ("Proof", mk_pi_nameless [Var "Bool"] (Univ TYPE));
      ]
  in
  {
    asserts = 0;
    rschema = [];
    signature = init;
    context = StrMap.empty;
    filepath = "";
    deps = StrMap.empty;
  }


(* during declaration translation, we (globally) track:
   name of current declaration, program declarations for encountered matches, and a context.*)
type declaration_data = {
  mutable name : string;
  mutable matches : int;
  mutable match_progs : cc_command list
}

let ddata = {
  name = "";
  matches = 0;
  match_progs = []
}

let eo_decl_attr (eo_atts : attr list) : cc_atts =
  { atts_init with
      implicit = List.mem_assoc "implicit" eo_atts;
      list = List.mem_assoc "list" eo_atts;
  }

let rec eo_cc_term (ctx : cc_context) (bvs : param list) (trm : eo_term) : cc_term =
  begin match trm with
  | Literal l -> Literal l
  | Symbol str ->
    (*TODO. implement Rish's hashmap trick. *)
    if str = "Type" then
      Univ TYPE
    else
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
        let (_,_,atts) = StrMap.find str tdata.context in
        mk_app ctx (Var str) args' (atts.apply)
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
      (ddata.name) (ddata.matches) in

    let params = List.map (eo_var_cc ctx []) ps in
    let ctx' = List.fold_left (fun acc p -> ctx_add p acc) ctx params in

    (* Infer types of lhs/rhs of first rule, wrt.
    locally-bound variables, and global constants. *)
    let rs' = List.map (eo_cc_rule ctx' bvs) rs in
    let (lhs,rhs) = List.hd rs' in
    let glob_ctx = StrMap.union (fun _ p _ -> Some p) (tdata.context) ctx' in
    let (ty_lhs, ty_rhs) = (infer glob_ctx lhs, infer glob_ctx rhs) in
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
        Rule (params @ bound_params @ free_params, prog_rules)
      ]
    in

    (* Update per-declaration and per-translation records. *)
    ddata.matches <- ddata.matches + 1;
    ddata.match_progs <- prog_sig @ ddata.match_progs;
    tdata.signature <- prog_sig @ tdata.signature;
    tdata.context <- ctx_add (Some prog_name, prog_ty, atts_init) tdata.context;

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
    let aname = "assert_" ^ string_of_int(tdata.asserts + 1) in
    let typ = appvar "Proof" [eo_cc_term ctx_init [] trm] in

    ddata.name <- aname;
    tdata.asserts <- tdata.asserts + 1;
    tdata.context <- ctx_add (Some aname, typ, atts_init) tdata.context;

    [ Const (aname, typ) ]

  | DeclareConst (str, typ, atts) ->
    let
      typ' = eo_cc_term ctx_init [] typ and
      att_opt =
        match atts with
        | [] -> None
        | att::[] -> Some (eo_decl_attr ctx_init [] att)
        | _ -> failwith "More than one declaration attribute."
    in
    let param = (Some str, typ', {atts_init with apply = att_opt }) in

    let assoc_rules =
      match att_opt with
      | Some (RightAssocNil nil) ->
        (* Gather all program-schema with right-assoc-nil attribute. *)
        let schema_cs = List.filter_map (fun (str, rs) ->
            if str = "right-assoc-nil" then Some rs else None
          ) tdata.rschema
        in
          List.map (fun (params, rs) ->
            let ctx' = ctx_add (mk_param str typ') tdata.context in
            let (cons, mctx) = elaborate_term ctx' (Var str) in
            let params' = IntMap.fold (fun idx trm acc ->
              (Some (string_of_int idx), trm, atts_init)::acc) mctx params in
            Rule (params', inst_schema rs [("#cons", cons); ("#nil", nil)])
          ) schema_cs
      | _ -> []
    in
      tdata.context <- ctx_add param tdata.context;
      [ Const (str, typ') ] @ assoc_rules

  | DefineConst (str, trm) ->
    let trm' = eo_cc_term ctx_init [] trm in
    let typ = infer tdata.context trm' in
    let param = (Some str, typ, {atts_init with definition = Some trm'}) in

    tdata.context <- ctx_add param tdata.context;

    [ Defn (str, typ, trm') ]

  | DeclareType (str, tys) ->
    let typ' = eo_arrow_cc ctx_init [] (tys @ [Symbol "Type"]) in
    tdata.context <- ctx_add (Some str, typ', atts_init) tdata.context;
    [ Const (str, typ') ]

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
    let trm' = eo_lambda_cc tdata.context [] vs trm in
    let typ = infer tdata.context trm' in
    let param = (Some str, typ, { atts_init with definition = Some trm' }) in
    tdata.context <- ctx_add param tdata.context;

    [ Defn (str, typ, trm') ]

  | DeclareRule (str, ps, rspec) ->
    let params = List.map (eo_var_cc ctx_init []) ps in
    let ctx = List.fold_left (fun acc p -> ctx_add p acc) ctx_init params in
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

    let arg_ptrns = Option.fold
      ~none:[] ~some:(List.map (eo_cc_term ctx []))
      rspec.arguments
    in

  (* step 1. create type signature and rewrite rule for auxillary.*)
    (* calculate type of each pattern under current signature and context.*)
    let glob_ctx = ctx_join ctx tdata.context in
    let arg_tys = List.map (infer glob_ctx) arg_ptrns in

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

    tdata.context <- ctx_add (mk_param aux_str aux_typ) tdata.context;

    (* elaborate lhs/rhs with explicits where needed.*)
    let glob_ctx' = ctx_add (mk_param aux_str aux_typ) glob_ctx in
    let rw_rules = map_cc_rule
      (infer_term glob_ctx' [])
      [(appvar aux_str (arg_ptrns @ aux_param_vars), concl_bool)]
    in
    let aux_decl = [
      Prog (aux_str, aux_typ);
      Rule (params, rw_rules) ]
    in

  (* step 2. create signature for main inference rule. *)
    let arg_params = List.mapi (fun i ty ->
      mk_param ("x" ^ string_of_int i) ty
    ) arg_tys
    in

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


    aux_decl @ [ Const (str, rule_typ) ]

  | DeclareConsts (lcat, eo_typ) ->
    [ LitTy (lcat, eo_cc_term ctx_init [] eo_typ)]

  | DeclareParamConst _ -> failwith "undefined"
  | DeclareOracleFun _ -> failwith "undefined"

  | Include ip ->
    let ip' = normalize_path ip (tdata.filepath) in
    let fp' = normalize_path (tdata.filepath) "" in
    let deps' =
      StrMap.update fp' (function
      | Some paths -> Some (StrSet.add ip'  paths)
      | None -> Some (StrSet.singleton ip')
      ) tdata.deps
    in
      tdata.deps <- deps'; []

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
