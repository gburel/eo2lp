open Ast_eo
open Ast_cc
open Inference


type translation_data = {
  mutable eo_progs : ProgSet.t StrMap.t;
  mutable eo_binop : EoSubstSet.t StrMap.t;
  mutable asserts : int;
  mutable context : cc_context;
  mutable filepath : string;
  mutable deps : StrSet.t StrMap.t;
}

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
        ("right-assoc-nil", EoSubstSet.empty);
        ("left-assoc-nil", EoSubstSet.empty);
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

let eo_decl_attr (atts : attr list) : cc_atts =
  { atts_init with
      implicit = mem_att atts "implicit";
      list = mem_att atts "list";
  }

let rec eo_cc_term (ctx : cc_context) (bvs : param list) (trm : eo_term) : cc_term =
  begin match trm with
  | Literal lit -> Literal lit

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
      (* | "_" ->
        begin match List.map (eo_cc_term ctx bvs) args with
        | [] -> failwith "Explicit application with no arguments!"
        | t::ts -> app t ts
        end *)
      | _ ->
        let args' = List.map (eo_cc_term ctx bvs) args in
        let ctx' = ctx_join ctx tdata.context in
        begin match StrMap.find_opt str ctx' with
        | Some (_,_,atts) -> mk_app ctx bvs (Var str) args' (atts.apply)
        | None -> failwith (Printf.sprintf "Can't find symbol %s in context." str)
        end
    end

  | Attributed (trm', atts) ->
    begin match req_atts atts with
    | [] -> eo_cc_term ctx bvs trm'
    | rs ->
      let atts' = List.map (fun (str, tm_opt) -> Attr (str, tm_opt)) (simple_atts atts) in
      let trm'' = Attributed (trm, atts') in
      eo_requires_cc ctx bvs rs trm''
    end

  | Match (ps, trm, rs) -> eo_match_cc ctx bvs ps trm rs
  end

and typed_param_cc ctx bvs (str,ty,att) : param =
  let x = if str = "_" then None else Some str in
  (x, eo_cc_term ctx bvs ty, eo_decl_attr att)

and eo_define_cc ctx bvs vs trm =
  match vs with
  | [] -> eo_cc_term ctx bvs trm
  | v :: vs' ->
    let p = typed_param_cc ctx bvs v in
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

    let params = List.map (typed_param_cc ctx []) ps in
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
    let p = typed_param_cc ctx bvs (mk_typed_param typ) in
    Bind (Pi, p, eo_arrow_cc ctx (p::bvs) ts)

and eo_cc_rule ctx bvs (lhs,rhs) =
  (eo_cc_term ctx bvs lhs, eo_cc_term ctx bvs rhs)

let eo_decl_attr ctx bvs (att : attr) =
  match att with
  | Attr ("right-assoc", None) -> RightAssoc
  | Attr ("left-assoc", None)  -> LeftAssoc
  | Attr ("right-assoc-nil", Some trm) -> RightAssocNil (eo_cc_term ctx bvs trm)
  | Attr ("left-assoc-nil", Some trm) -> LeftAssocNil (eo_cc_term ctx bvs trm)
  | Attr ("chainable", Some trm) -> Chainable (eo_cc_term ctx bvs trm)
  | Attr ("pairwise",  Some trm) -> Pairwise (eo_cc_term ctx bvs trm)
  | Attr ("binder",    Some trm) -> Binder (eo_cc_term ctx bvs trm)
  | _ -> failwith "Unknown declaration attribute."
