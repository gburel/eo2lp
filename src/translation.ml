open Ast
open Ast_cc
open Inference

module Prog = struct
  type t = eo_var list * (eo_term * eo_term) list
  let compare = compare
end

module ProgSet = Set.Make(Prog)

module EOSubst = struct
  type t = eo_term StrMap.t
    let compare = compare
end

module StrMapSet = Set.Make(EOSubst)

type translation_data = {
  mutable eo_progs : ProgSet.t StrMap.t;
  mutable eo_binop : StrMapSet.t StrMap.t;
  mutable asserts : int;
  mutable context : cc_context;
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
  {
    asserts = 0;
    context = StrMap.empty;
    filepath = "";
    deps = StrMap.empty;
    eo_progs =
      StrMap.of_list [
        ("right-assoc-nil", ProgSet.empty);
        ("left-assoc-nil", ProgSet.empty);
      ];
    eo_binop =
      StrMap.of_list [
        ("right-assoc-nil", StrMapSet.empty);
        ("left-assoc-nil", StrMapSet.empty);
      ];
  }

let glob_ctx_add str typ : unit =
  tdata.context <- ctx_add str typ tdata.context

let glob_ctx_add_param p : unit =
  tdata.context <- ctx_add_param p tdata.context

(*
let glob_ctx_extend (ps : param list) : unit =
  tdata.context <- ctx_extend ps tdata.context; *)

(* during declaration translation, we (globally) track:
   name of current declaration, program declarations for encountered matches, and a context.*)
type declaration_data =  {
  name : string;
  matches : int;
  match_progs : cc_command list
}

let ddata_init = {
  name = "";
  matches = 0;
  match_progs = [] }

let ddata = ref ddata_init

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
        let ctx' = ctx_join ctx tdata.context in
        begin match StrMap.find_opt str ctx' with
        | Some (_,_,atts) -> mk_app ctx (Var str) args' (atts.apply)
        | None -> failwith (Printf.sprintf "Can't find symbol %s in context." str)
        end
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
      (!ddata.name) (!ddata.matches) in

    let params = List.map (eo_var_cc ctx []) ps in
    let ctx' = ctx_append_param params ctx in
    let params' = List.map snd (StrMap.to_list ctx') in
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
    let prog_cmds =
      [
        Prog (prog_name, prog_ty);
        Rule (params' @ bound_params @ free_params, prog_rules)
      ]
    in

    (* Update per-declaration and per-translation records. *)
    ddata := { !ddata with
      matches = !ddata.matches + 1;
      match_progs = prog_cmds @ !ddata.match_progs
    };
    glob_ctx_add prog_name prog_ty;

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

let att_stem att = List.hd (String.split_on_char ' ' (string_of_attribute att))

let inst_eo_schema ctx (schema : Prog.t) (subst : EOSubst.t)  =
  let (vs, rws) = subst_prog subst schema in
  let vs' = List.map (eo_var_cc ctx []) vs in
  Rule (vs', List.map (eo_cc_rule (ctx_append_param vs' ctx) []) rws)

let base_cmd_cc (cmd : base_command) : cc_command list =
  match cmd with
  | Assert trm ->
    let aname = "assert_" ^ string_of_int(tdata.asserts + 1) in
    let typ = appvar "Proof" [eo_cc_term ctx_init [] trm] in

    ddata := { !ddata with name = aname };
    tdata.asserts <- tdata.asserts + 1;

    glob_ctx_add aname typ;
    [ Const (aname, typ) ]

  | DeclareConst (str, typ, atts) ->

    let typ' = eo_cc_term ctx_init [] typ in
    let eo_att_opt =
      match atts with
      | []      -> None
      | att::[] -> Some att
      | _ -> failwith "More than one attribute in constant declaration."
    in

    let cc_att_opt = Option.map (eo_decl_attr ctx_init []) eo_att_opt in
    glob_ctx_add_param (Some str, typ', { atts_init with apply = cc_att_opt });

    let rw_cmds =
      begin match eo_att_opt with
      | None -> []
      | Some ("right-assoc-nil", Some nil) ->
          let (ty1, ty2) = eo_binop_tys typ in
          let subst = StrMap.of_list
            [ ("cons", Symbol str); ("nil", nil);
              ("T1", ty1); ("T2", ty2) ]
          in
          (* update record of binops *)
          tdata.eo_binop <- StrMap.update "right-assoc-nil"
            (function
              | Some x -> Some (StrMapSet.add subst x)
              | _ -> None
            ) tdata.eo_binop;

          (* return all instances of prog schemas indexed by `att_str` *)
          ProgSet.fold
            (fun prog acc -> inst_eo_schema tdata.context prog subst :: acc)
            (StrMap.find "right-assoc-nil" tdata.eo_progs) []
      | Some _ -> []
      end
    in

    Const (str, typ') :: rw_cmds

  | DefineConst (str, trm) ->
    let trm' = eo_cc_term ctx_init [] trm in
    let typ = infer tdata.context trm' in
    let param = (Some str, typ, { atts_init with definition = Some trm' }) in

    glob_ctx_add_param param;
    [ Defn (str, typ, trm') ]

  | DeclareType (str, tys) ->
    let typ = eo_arrow_cc ctx_init [] (tys @ [Symbol "Type"]) in

    glob_ctx_add str typ;
    [ Const (str, typ) ]

  | DefineType _ -> failwith "DefineType"
  | DeclareFun _ -> failwith "DeclareFun"
  | DefineFun _ -> failwith "DefineFun"
  | DefineFunRec _ -> failwith "DefineFunRec"
  | DefineFunsRec _ -> failwith "DefineFunsRec"
  | DeclareSort _ -> failwith "DeclareSort"
  | DefineSort _ -> failwith "DefineSort"
  | DeclareDatatype _ -> failwith "DeclareDatatype"
  | DeclareDatatypes _ -> failwith "DeclareDatatypes"

let eunoia_cmd_cc (cmd : eunoia_command) : cc_command list =
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

    glob_ctx_add_param param;
    [ Defn (str, typ, trm') ]

  | DeclareRule (str, ps, rspec) ->
    let params = List.map (eo_var_cc ctx_init []) ps in
    let loc_ctx = ctx_append_param params ctx_init in
    let concl_bool = eo_cc_term loc_ctx [] rspec.conclusion in
    let concl = appvar "Proof" [concl_bool] in

    let rule_typ_body =
      begin match rspec.prems with
      | Some (Premises ts) ->
        let prem_tys = List.map (fun t ->
          appvar "Proof" [eo_cc_term loc_ctx [] t]) ts
        in
          mk_pi_nameless prem_tys concl

      | Some (PremiseList (trm,op)) ->
        let prem_trm = eo_cc_term loc_ctx [] trm in
        let op_trm = eo_cc_term loc_ctx [] op in
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
      | Some (Premises ts) -> List.map (eo_cc_term loc_ctx []) ts
      | Some (PremiseList (trm,_)) -> [ eo_cc_term loc_ctx [] trm ]
      | None -> [ ]
      end
    in

    let arg_ptrns = Option.fold
      ~none:[] ~some:(List.map (eo_cc_term loc_ctx []))
      rspec.arguments
    in

  (* step 1. create type signature and rewrite rule for auxillary.*)
    (* calculate type of each pattern under current signature and context.*)
    let glob_ctx = ctx_join loc_ctx tdata.context in
    let arg_tys = List.map (infer glob_ctx) arg_ptrns in

    let aux_params = ParamSet.to_list
      (ParamSet.diff
        (filter_vars loc_ctx rule_typ_body)
        (map_filter_vars loc_ctx arg_ptrns)
      )
    in
    let aux_str = str ^ "_aux" in
    let aux_typ_body =
      mk_pi_nameless arg_tys (
        mk_pi aux_params (Var "Bool")
      )
    in
    let aux_typ = close_term loc_ctx aux_typ_body in
    let aux_param_vars = List.map param_var aux_params in

    glob_ctx_add aux_str aux_typ;

    (* elaborate lhs/rhs with explicits where needed.*)
    let rws = [(appvar aux_str (arg_ptrns @ aux_param_vars), concl_bool)] in
    let aux_cmds = [ Prog (aux_str, aux_typ); Rule (params, rws) ] in

  (* step 2. create signature for main inference rule. *)
    let arg_params = List.mapi (fun i ty ->
      mk_param ("x" ^ string_of_int i) ty) arg_tys
    in

    (* eta-expand auxillary function.*)
    let aux_vars = List.map param_var (arg_params @ aux_params) in
    let aux_app =  appvar "Proof" [appvar aux_str aux_vars] in
    let rule_typ_raw = mk_pi_implicit aux_params (
      mk_pi_nameless
        (List.map (fun prop -> appvar "Proof" [prop]) prem_ptrns)
        (mk_pi arg_params aux_app)
    ) in
    let rule_typ = close_term loc_ctx rule_typ_raw in

    glob_ctx_add str rule_typ;
    aux_cmds @ [ Const (str, rule_typ) ]

  | DeclareConsts (lcat, eo_typ) ->
    [ LitTy (lcat, eo_cc_term ctx_init [] eo_typ) ]

  | DeclareParamConst _ -> failwith "undefined"
  | DeclareOracleFun _ -> failwith "undefined"

  | Include ip ->
    (* instantiate schemas here? *)
    let ip' = normalize_path ip (tdata.filepath) in
    let fp' = normalize_path (tdata.filepath) "" in
    let deps' =
      StrMap.update fp' (function
      | Some paths -> Some (StrSet.add ip'  paths)
      | None -> Some (StrSet.singleton ip')
      ) tdata.deps
    in
      tdata.deps <- deps'; []

  | Program (str, att_str_opt, eo_ps, dom_tys, ran_ty, eo_prog) ->
    let params = List.map (eo_var_cc ctx_init []) eo_ps in
    let ctx = ctx_append_param params ctx_init in
    let prog_ty_raw = eo_arrow_cc ctx [] (dom_tys @ [ran_ty]) in
    let prog_ty = close_term ctx prog_ty_raw in
    glob_ctx_add str prog_ty;

    (* infer implicits for rules *)
    let rws = List.map (eo_cc_rule ctx []) eo_prog in

    begin match att_str_opt with
    | Some astr ->
      (* update map for eo_program schema.*)
      tdata.eo_progs <- StrMap.update astr (function
        | Some x -> Some (ProgSet.add (eo_ps, eo_prog) x)
        | None -> failwith (Printf.sprintf "Unknown attribute: %s" astr)
      ) tdata.eo_progs;

      (* also, instantiate for all constants with attribute given by `att_str`*)
      let prog_insts = StrMapSet.fold
        (fun sub acc -> inst_eo_schema tdata.context (eo_ps, eo_prog) sub :: acc)
        (StrMap.find astr tdata.eo_binop) [] in

      Prog (str, prog_ty) :: prog_insts

    | None -> [ Prog (str, prog_ty); Rule (params, rws) ]
    end
  | Reference _ -> failwith "undefined"

let proof_prop (trm : cc_term) : cc_term =
  match trm with
  | Var str ->
    let typ = lookup_type tdata.context str in
    begin match typ with
    | App (Var "Proof", prop) -> prop
    | _ -> failwith (Printf.sprintf
        "Not a proof term: (%s : %s)"
        (string_of_term trm)(string_of_term typ)
      )
    end  | _ -> failwith (Printf.sprintf "Not a variable: %s" (string_of_term trm))

let proof_cmd_cc (cmd : proof_command) : cc_command list =
  match cmd with
  | Assume (str, trm) ->
    let trm' = eo_cc_term ctx_init [] trm in
    let typ = appvar "Proof" [trm'] in
    glob_ctx_add str typ;
    [ Const (str, typ) ]

  | Step (str, trm_opt, rule, prem_opt, arg_opt) ->
    (* make type of proof term *)
    let concl_prop = eo_cc_term ctx_init [] (Option.get trm_opt) in
    let concl = appvar "Proof" [concl_prop] in

    let prems = match prem_opt with
      | Some (Premises ts) -> List.map (eo_cc_term ctx_init []) ts
      | _ -> []
    in

    let args = match arg_opt with
      | Some ts -> List.map (eo_cc_term ctx_init []) ts
      | None -> []
    in

    let def = appvar rule (prems @ args) in
    let trm_defs = StrMap.filter_map
      (fun str (_,_,atts) ->
        if String.starts_with ~prefix:"@t" str
        then atts.definition else None
      ) tdata.context in

    let def' = infer_term tdata.context trm_defs def in
    let param = (Some str, concl, {atts_init with definition = Some def'}) in

    glob_ctx_add_param param;
    [ Defn (str, concl, def') ]

  | AssumePush _ -> failwith "undefined"
  | StepPop _ -> failwith "undefined"

let eo_cc (cmd : eo_command) : cc_command list =
  ddata := ddata_init;
  let () = match get_eo_name cmd with
  | Some str -> ddata := { !ddata with name = str };
  | None -> (); in
  let cc_cmds = match cmd with
  | Base cmd -> base_cmd_cc cmd
  | EO cmd -> eunoia_cmd_cc cmd
  | Prf cmd -> proof_cmd_cc cmd
  | Ctrl _ -> []
  in
  !ddata.match_progs @ cc_cmds
