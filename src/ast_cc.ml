open Term_cc

type context = datum StrMap.t

(* given a term, create a context for its binding structure *)
let rec bvars : term -> context =
  let rec aux xs trm =
    match trm with
    | (Univ _|Var _|Meta _|Literal _) -> StrMap.empty
    | Explicit t -> aux t
    | Bound i ->
      begin match List.nth_opt xs i with
      | Some x -> StrMap.singleton x
      | None -> StrMap.empty
      end
    | App (e1, e2) ->
        StrMap.union (aux xs e1) (aux xs e2)
    | Bind (_, (x,dat), t) ->
        StrMap.union (aux xs dat.typ) (aux ((x,dat)::xs) t)
  in
    aux []

let map_bvars : term list -> context =
  List.fold_left (fun acc tm -> StrMap.union acc (bvars tm)) StrMap.empty


let dummy : context = {
  theory = dummy;
  data = StrMap.empty;
  bound_vars = [];
}

let dummy ty : info = {
  typ = ty;
  implicit = false;
  list = false;
}




type attribute =
  | RightAssoc
  | LeftAssoc
  | RightAssocNil of term
  | LeftAssocNil of term
  | Chainable of term
  | Pairwise of term
  | Binder of term


let string_of_attribute att =
  match att with
  | RightAssoc -> ":right-assoc"
  | LeftAssoc -> ":left-assoc"
  | RightAssocNil trm -> ":right-assoc-nil " ^ string_of_term trm
  | LeftAssocNil trm -> ":left-assoc-nil " ^ string_of_term trm
  | Chainable trm -> ":chainable " ^ string_of_term trm
  | Pairwise trm -> ":pairwise " ^ string_of_term trm
  | Binder trm -> ":binder " ^ string_of_term trm

let rec filter_vars (xs : binding list) (trm : cc_term) : PSet.t =
  match trm with
  | Univ _ -> PSet.empty
  | Bound _ -> PSet.empty
  | Var x ->
    begin match List.find_opt x ctx with
    | Some p -> PSet.singleton p
    | None -> PSet.empty
    end
  | Meta _ -> PSet.empty
  | App (e1, e2) ->
      let f1 = filter_vars ctx e1 in
      let f2 = filter_vars ctx e2 in
      PSet.union f1 f2
  | Bind (_, (_, typ,_), body) ->
      let ftyp  = filter_vars ctx typ in
      let fbody = filter_vars ctx body in
      Pset.union ftyp fbody


type cc_command =
  | Const of string * cc_term
  | Defn of string * cc_term * cc_term
  | Prog of string * cc_term
  | Rule of rw_rule
  | LitTy of lit_category * cc_term
and rw_rule = info StrMap.t * (cc_term * cc_term) list

module StrSet = Set.Make(String)

type theory = {
  id : string;
  parents : StrSet.t;
  commands : cc_command list;
  notation : attribute StrMap.t;
  rule_schema : (rw_rule list) StrMap.t
}

let dummy : theory = {
  id = "";
  parents = StrSet.empty;
  commands = [];
  notation = StrMap.empty;
  rule_schema = StrMap.empty;
}

type context = {
  theory : theory;
  parameters : datum StrMap.t;
  bound_vars : (string * info) list
}



let merge_ctx ctx ctx' : context =
  if ctx.theory = ctx'.theory then
    {
      ctx with
        parameters = StrMap.union (fun _ a _ -> Some a) ctx.parameters ctx'.parameters;
        bound_vars = ctx.bound_vars @ ctx'.bound_vars;
    }
  else
    failwith "Cannot merge contexts from different theories."

let extend_ctx ctx (str,typ) : context =
  { ctx with parameters = StrMap.add str typ ctx.parameters }

(* ------ Utilities ------ *)

let var = fun x -> Var x

(* deprecated *)
let param_var (str_opt,_,_) =
  Option.fold ~none:(Var "BLANK") ~some:(fun str -> Var str) str_opt


(* let param_var ((_,_) : param) =
  match x_opt with
  | Some x -> Var x
  | None -> failwith "Cannot create variable from nameless parameter." *)





let lookup_param_opt (ctx : cc_context) (str : string) : param option =
  StrMap.find_opt str ctx

let lookup_type (ctx : cc_context) (str : string) : cc_term =
  match StrMap.find_opt str ctx with
  | Some (_,ty,_) -> ty
  | None -> failwith (Printf.sprintf "Cannot find variable %s in context" str)

let lookup_bvar (ctx : param list) (idx : int) : cc_term =
  match List.nth_opt ctx idx with
  | Some (Some x,_,_) -> Var x
  | None -> failwith "Bound variable index out of range."

let lookup_def (ctx : cc_context) (str : string) : cc_term option =
  match StrMap.find_opt str ctx with
  | Some (_, _, atts) -> atts.definition
  | _ -> None

let lookup_attr (ctx : cc_context) (str : string) : cc_atts option =
  match StrMap.find_opt str ctx with
  | Some (_,_,atts) -> Some atts
  | None -> None

let string_of_lcat lcat =
  match lcat with
    | STR -> "<string>"
    | NUM -> "<numeral>"
    | DEC -> "<decimal>"
    | RAT -> "<rational>"
    | BIN -> "<binary>"
    | HEX -> "<hexadecimal>"

let lookup_lit (ctx : cc_context) (lcat : lit_category) =
  StrMap.find_opt (string_of_lcat lcat) ctx




let mk_chain (f : cc_term) (agg : cc_term) (args : cc_term list) : cc_term =
  let rec chain_up args =
    match args with
    | [] -> f
    | [x] -> App (f,x)
    | x1 :: x2 :: rest ->
      let seg = app f [x1; x2] in
      match rest with
      | [] -> seg
      | _ -> app agg [seg; chain_up (x2 :: rest)]
  in chain_up args

let mk_pairwise (f : cc_term) (agg : cc_term) (args : cc_term list) : cc_term =
  let rec all_pairs = function
    | [] -> []
    | x :: xs ->
      List.map (fun y -> (x, y)) xs @ all_pairs xs
  in
  match args with
  | [] -> f
  | [x] -> App (f,x)
  | [x;y] -> App (App (f,x),y)
  | _ ->
    let pairs = all_pairs args in
    app agg (List.map (fun (a,b) -> app f [a; b]) pairs)

let is_list_param ctx bvs trm =
  match trm with
  | Var str ->
      begin match StrMap.find_opt str ctx with
      | Some (_,_,atts) -> atts.list
      | None -> false
      end
  | Bound idx ->
      begin match List.nth_opt bvs idx with
      | Some (_,_,atts) -> atts.list
      | None -> false
      end
  | _ -> false

let list_concat f t r =
  App (App (App (Var ("eo::list_concat"), f), t), r)

let list_concat_left f r t =
  App (App (App (Var ("eo::list_concat"), f), r), t)

let rec mk_app ctx bvs f args att_opt =
  match att_opt with
  | None | Some (Binder _) ->
      List.fold_left (fun e arg -> App (e, arg)) f args
  | Some RightAssoc ->
      (match args with
      | [] -> f
      | [x] -> App (f, x)
      | [x; y] -> app f [x; y]
      | x :: xs -> app f [x; mk_app ctx bvs f xs att_opt])
  | Some LeftAssoc ->
      (match args with
      | [] -> f
      | [x] -> App (f, x)
      | x :: xs -> List.fold_left (fun acc y -> app f [acc; y]) x xs)
  | Some (RightAssocNil nil) ->
      begin match args with
      | [] -> f
      | [x] -> if is_list_param ctx bvs x then x else app f [x;nil]
      (* | [x;y] -> if is_list_param ctx bvs y
          then app f [x;y]
          else app f [x; mk_app ctx bvs f [y] att_opt] *)
      | _ ->
      let n = List.length args in
      let last = List.nth args (n - 1) in
      let init, start =
        if is_list_param ctx bvs last
        then (last, n - 2) else (nil, n - 1)
      in
      let rec aux i r =
        if i < 0 then r
        else
          let t = List.nth args i in
          let r' = if is_list_param ctx bvs t then list_concat f t r else app f [t; r]
          in aux (i - 1) r'
      in
        aux start init
      end
  | Some (LeftAssocNil nil) ->
      let n = List.length args in
      if n <= 2 then
        app f args
      else
        let first = List.hd args in
        let init, start = if is_list_param ctx bvs first then (first, 1) else (nil, 0) in
        let n = List.length args in
        let rec aux i r =
          if i >= n then r
          else
            let t = List.nth args i in
            let r' =
              if is_list_param ctx bvs t then list_concat_left f r t else app f [r; t]
            in
            aux (i + 1) r'
        in
          aux start init
  | Some (Chainable agg) -> mk_chain f agg args
  | Some (Pairwise agg) -> mk_pairwise f agg args



let unfold (defs : cc_term StrMap.t) (str : string) (trm : cc_term) : cc_term =
  map_cc_term
    (fun _ str' ->
      if str' = str then
        match StrMap.find_opt str defs with
        | Some def -> def
        | None -> Var str'
      else
        Var str'
    )
    [] trm

let rec unfold_all (defs : cc_term StrMap.t) (trm : cc_term) : cc_term =
  map_cc_term
    (fun _ str ->
      match StrMap.find_opt str defs with
      | Some def -> unfold_all defs def
      | None -> Var str
    )
    [] trm

let map_cc_rule (f : cc_term -> cc_term) (rs : cc_rule) : cc_rule =
  List.map (fun (l,r) -> (f l, f r)) rs

let mk_pi_nameless (tys : cc_term list) (trm : cc_term) =
  let ps = List.map (fun ty -> (None, ty, atts_init)) tys
  in mk_pi ps trm

let list_add x xs =
  if List.mem x xs then xs else x :: xs

let mk_pi_implicit (xs : param list) (trm : cc_term) =
  let ps = List.map (fun (str_opt, ty, atts) ->
    (str_opt, ty, {atts with implicit = true})) xs
  in
    mk_pi ps trm

module StrSet = Set.Make(String)

module Param = struct
  type t = param
  let compare = compare
end






let filter_vars_list (ctx : cc_context) (trm : cc_term) : param list =
  ParamSet.to_list (filter_vars ctx trm)

let map_filter_vars (ctx : cc_context) (ts : cc_term list) =
  List.fold_left (fun vs t -> ParamSet.union (filter_vars ctx t) vs) ParamSet.empty ts

let map_filter_vars_list (ctx : cc_context) (trms : cc_term list) : param list =
  ParamSet.to_list (map_filter_vars ctx trms)

let rec close_term (ctx : cc_context) (trm : cc_term) : cc_term =
  let trm_fvars = filter_vars_list ctx trm in
  begin if trm_fvars = [] then
    trm
  else
    close_term ctx
      (mk_pi_implicit trm_fvars trm)
  end


(* ----- Pretty printing. ------ *)

let string_of_rule (l,r) =
  Printf.sprintf "%s ↪ %s"
  (string_of_term l) (string_of_term r)

let string_of_rules rs =
  String.concat "\n" (List.map string_of_rule rs)

let string_of_params ps =
  String.concat ", " (List.map (string_of_param []) ps)

let string_of_cmd cmd =
  match cmd with
  | Const (str, ty) ->
      let ty_str = Printf.sprintf " : %s" (string_of_term ty) in
      Printf.sprintf "const %s%s" str ty_str

  | Defn (str, ty, def) ->
      Printf.sprintf "def %s : %s := %s"
      str (string_of_term ty) (string_of_term def)

  | Prog (str, ty) ->
      Printf.sprintf "prog %s : %s"
      str (string_of_term ty)

  | Rule (ps, rs) ->
      Printf.sprintf "rule %s\n%s"
        (string_of_params ps) (string_of_rules rs)

let string_of_sig sg =
  String.concat "\n" (List.map string_of_cmd sg)
