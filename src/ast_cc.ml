open Ast

(* ----- Datatypes. ------ *)
type universe = TYPE | KIND (* PROP deprecated, just use Proof : Bool → TYPE. *)
[@@deriving show]

type cc_binder =
  | Let
  | Lambda
  | Pi
[@@deriving show]

type cc_term =
  | Univ of universe
  | Literal of literal
  | Implicit of cc_term
  | Var of string
  | Meta of string
  | Bound of int
  | App of cc_term * cc_term
  | Bind of cc_binder * param * cc_term
(* an param is a pair of a name and a term. *)
and param = string option * cc_term * param_attr
and param_attr = { implicit : bool; list : bool }
(* each item in a context represents a mapping between a set of strings and a term. *)
type cc_context = param list

type app_attr =
  | RightAssoc
  | LeftAssoc
  | RightAssocNil of cc_term
  | LeftAssocNil of cc_term
  | Chainable of cc_term
  | Pairwise of cc_term
  | Binder of cc_term

type cc_rule = (cc_term * cc_term) list
type cc_command =
  | Const of string * cc_term * app_attr option
  | Defn of string * cc_term * cc_term
  | Prog of string * cc_term
  | Rule of param list * cc_rule
  | LitTy of lit_category * cc_term

type cc_signature = cc_command list

(* ------ Utilities ------ *)
let is_univ trm = match trm with
  | Univ _ -> true
  | _ -> false

let is_var trm = match trm with
  | (Var _|Bound _|Meta _) -> true
  | _ -> false

let var = fun x -> Var x

let param_var ((x_opt,_,_) : param) =
  match x_opt with
  | Some x -> Var x
  | None -> failwith "Cannot create variable from nameless parameter."

let mk_param (x : string) (ty : cc_term) : param =
  (Some x, ty, {implicit=false; list=false})

let is_binder bb trm = match trm with
  | Bind (bb', _, _) -> bb = bb'
  | _ -> false

let cmd_att (cmd : cc_command) : app_attr option =
  match cmd with
  | Const (_,_,att_opt) -> att_opt
  | _ -> None

let cmd_str (cmd : cc_command) : string option =
  match cmd with
  | Const (str,_,_) -> Some str
  | Defn (str,_,_) -> Some str
  | Prog (str, _) -> Some str
  | _ -> None

let cmd_ty (cmd : cc_command) : cc_term option =
  match cmd with
  | Const (_,ty,_) -> Some ty
  | Defn (_,ty,_) -> Some ty
  | Prog (_, ty) -> Some ty
  | _ -> None

let lookup_param (ctx : cc_context) (str : string) : param option =
  List.find_opt (fun (x,_,_) -> x = Some str) ctx

let lookup_bvar (ctx : cc_context) (idx : int) : cc_term =
  match List.nth_opt ctx idx with
  | Some (Some x,_,_) -> Var x
  | None -> failwith "Bound variable index out of range."

(* Lookup type of `str` in context `ctx`. *)
let lookup_typ_opt (ctx : cc_context) (str : string) : cc_term option =
  match List.find_opt (fun (x,_,_) -> x = Some str) ctx with
  | Some (_,ty,_) -> Some ty
  | None -> None

let lookup_typ ctx x =
  match lookup_typ_opt ctx x with
  | Some ty -> ty
  | None -> failwith ("Variable not found in context: " ^ x)

(* Get command in signature with name `str`. *)
let lookup_cmd_opt (cmds : cc_signature) (str : string) : cc_command option =
  List.find_opt (fun cmd -> cmd_str cmd = Some str) cmds

(* Lookup type of `str` in signature `sigg`. *)
let lookup_typ_global (cmds : cc_signature) (ctx : cc_context) (str : string) : cc_term =
  begin match lookup_typ_opt ctx str with
  | Some ty -> ty
  | None ->
    let cmd_opt = lookup_cmd_opt cmds str in
    let ty_opt = Option.bind cmd_opt cmd_ty in
    begin match ty_opt with
    | Some ty -> ty
    | None -> failwith (Printf.sprintf
        "Variable with name %s not found in context or signature." str
      )
    end
  end

let lookup_def (cmds : cc_signature) (str : string) : cc_term option =
  match lookup_cmd_opt cmds str with
  | Some (Defn (_,_,trm)) -> Some trm
  | _ -> None

(* Maybe get attribute of command with name `str` in signature `sg`. *)
let lookup_decl_attr (sigg : cc_signature) (str : string) =
  match lookup_cmd_opt sigg str with
  | Some (Const (_, _, att_opt)) -> att_opt
  | _ -> None

let lookup_lit (cmds : cc_command list) (lcat : lit_category) =
  List.find_map (function
    | LitTy (lcat', ty) ->
        if lcat = lcat' then (Some ty) else None
    | _ -> None
  ) cmds

type assoc_dir = Left | Right

(* for a given direction, give the list of cons and nil operators in a signature *)
let sig_assocs (cmds : cc_command list) (dir : assoc_dir) =
  List.filter_map (fun cmd ->
    match (cmd_str cmd, cmd_att cmd) with
    | Some str, Some (RightAssocNil nil) ->
        if dir = Right then Some (Var str, nil) else None
    | Some str, Some (LeftAssocNil nil) ->
        if dir = Left then Some (Var str, nil) else None
    | _ -> None
  ) cmds


(* Deprecate? Convert a signature to a context. *)
let sig_context cs =
  List.filter_map (fun cmd ->
    match cmd with
      | Const (str, typ, _) ->
          Some (Some str, typ, {implicit=false; list=false})
      | _ -> None
    ) cs

let app : cc_term -> cc_term list -> cc_term =
  List.fold_left (fun acc y -> App (acc, y))

let appvar str = app (Var str)

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
  | _ ->
    let pairs = all_pairs args in
    app agg (List.map (fun (a,b) -> app f [a; b]) pairs)

(* Assume an auxiliary helper [app] exists that applies [f] to a list of arguments.
   (For example, app f [a;b] is interpreted as App(App(f,a),b).) *)
   let param_is_list ctx i =
     let rec aux i = function
       | [] -> false
       | [(_, _, attr)] -> attr.list
       | (_, _, attr) :: ps -> if i = 0 then attr.list else aux (i - 1) ps
     in aux i ctx

   let list_concat f t r =
     App (App (App (Var ("eo::list_concat"), f), t), r)

   let list_concat_left f r t =
     App (App (App (Var ("eo::list_concat"), f), r), t)

   let rec mk_app ctx f args att_opt =
     match att_opt with
     | None | Some (Binder _) ->
         List.fold_left (fun e arg -> App (e, arg)) f args
     | Some RightAssoc ->
         (match args with
         | [] -> f
         | [x] -> App (f, x)
         | [x; y] -> app f [x; y]
         | x :: xs -> app f [x; mk_app ctx f xs att_opt])
     | Some LeftAssoc ->
         (match args with
         | [] -> f
         | [x] -> App (f, x)
         | x :: xs -> List.fold_left (fun acc y -> app f [acc; y]) x xs)
     | Some (RightAssocNil nil) ->
         let n = List.length args in
         if n = 0 then f else
         let last = List.nth args (n - 1) in
         let init, start =
           if param_is_list ctx (n - 1) then (last, n - 2) else (nil, n - 1)
         in
         let rec aux i r =
           if i < 0 then r
           else
             let t = List.nth args i in
             let r' =
               if param_is_list ctx i then list_concat f t r else app f [t; r]
             in
             aux (i - 1) r'
         in
         aux start init
     | Some (LeftAssocNil nil) ->
         (match args with
         | [] -> f
         | _ ->
            let first = List.hd args in
            let init, start =
              if param_is_list ctx 0 then (first, 1) else (nil, 0)
            in
            let n = List.length args in
            let rec aux i r =
              if i >= n then r
              else
                let t = List.nth args i in
                let r' =
                  if param_is_list ctx i then list_concat_left f r t else app f [r; t]
                in
                aux (i + 1) r'
            in
            aux start init)
     | Some (Chainable agg) -> mk_chain f agg args
     | Some (Pairwise agg) -> mk_pairwise f agg args


let rec map_cc_term
  (f : string option list -> string -> cc_term)
  (bvs : string option list) (trm : cc_term)
  = match trm with
  | (Univ _|Meta _|Bound _|Literal _) -> trm
  | Implicit t -> Implicit (map_cc_term f bvs t)
  | Var x -> f bvs x
  | App (t1,t2) -> App (map_cc_term f bvs t1, map_cc_term f bvs t2)
  | Bind (bb, (str,ty,atts), trm') ->
    let x' = (str, map_cc_term f bvs ty,atts) in
    Bind (bb, x', map_cc_term f (str::bvs) trm')

let map_cc_rule (f : cc_term -> cc_term) (rs : cc_rule) : cc_rule =
  List.map (fun (l,r) -> (f l, f r)) rs

let subst_vars vs trm =
  map_cc_term (fun _ str ->
    match List.find_opt (fun (x,_) -> x = str) vs with
    | Some (_,t) -> t
    | None -> Var str
  ) [] trm

let inst_schema rs (sub : (string * cc_term) list) =
  map_cc_rule (subst_vars sub) rs

let mk_bounds (xs : string option list) (trm : cc_term) =
  map_cc_term (fun bvs str ->
    match List.find_index (fun x -> x = Some str) bvs with
    | Some i -> Bound i
    | None -> Var str
  ) xs trm

let mk_pi (xs : param list) trm =
  let rec aux bvs (ys : param list) trm : cc_term =
    match ys with
    | [] -> mk_bounds bvs trm
    | ((str,ty,atts)::zs) ->
    Bind (Pi, (str, mk_bounds bvs ty, atts), aux (str::bvs) zs trm)
  in
  aux [] xs trm

let mk_pi_nameless (tys : cc_term list) (trm : cc_term) =
  let ps = List.map
    (fun ty -> (None, ty, {implicit=false; list=false})) tys
  in
    mk_pi ps trm

module StrSet = Set.Make(String)

module Param = struct
  type t = param
  let compare = compare
end

module ParamSet = Set.Make(Param)
type param_set = ParamSet.t

let rec bvars (bvs : cc_context) (trm : cc_term) : param_set =
  match trm with
  | Univ _ -> ParamSet.empty
  | Bound i ->
    begin match List.nth_opt bvs i with
    | Some x -> ParamSet.singleton x
    | None -> ParamSet.empty
    end
  | Var _ -> ParamSet.empty
  | Meta _ -> ParamSet.empty
  | App (e1, e2) ->
      ParamSet.union (bvars bvs e1) (bvars bvs e2)
  | Bind (_, ((_, typ,_) as p), body) ->
      ParamSet.union (bvars bvs typ) (bvars (p::bvs) body)

let bvars_list bvs t = ParamSet.to_list (bvars bvs t)

let map_bvars (bvs : cc_context) (ts : cc_term list) =
  List.fold_left (fun vs t -> ParamSet.union (bvars bvs t) vs) ParamSet.empty ts

let map_bvars_list (bvs : cc_context) (trms : cc_term list) : cc_context =
  ParamSet.to_list (map_bvars bvs trms)

let rec filter_vars (ctx : cc_context) (trm : cc_term) : param_set =
  match trm with
  | Univ _ -> ParamSet.empty
  | Bound _ -> ParamSet.empty
  | Var x ->
    begin match lookup_param ctx x with
    | Some p -> ParamSet.singleton p
    | None -> ParamSet.empty
    end
  | Meta _ -> ParamSet.empty
  | App (e1, e2) ->
      let f1 = filter_vars ctx e1 in
      let f2 = filter_vars ctx e2 in
      ParamSet.union f1 f2
  | Bind (_, (_, typ,_), body) ->
      let ftyp  = filter_vars ctx typ in
      let fbody = filter_vars ctx body in
      ParamSet.union ftyp fbody

let filter_vars_list (ctx : cc_context) (trm : cc_term) : param list =
  ParamSet.to_list (filter_vars ctx trm)

let map_filter_vars (ctx : cc_context) (ts : cc_term list) =
  List.fold_left (fun vs t -> ParamSet.union (filter_vars ctx t) vs) ParamSet.empty ts

let map_filter_vars_list (ctx : cc_context) (trms : cc_term list) : cc_context =
  ParamSet.to_list (map_filter_vars ctx trms)

let rec close_term (ctx : cc_context) (trm : cc_term) : cc_term =
  (* create implicit parameters for all free variables in trm *)
  let trm_fvars = filter_vars_list ctx trm in
  begin if trm_fvars = [] then
    trm
  else
    let fvar_params =
      List.map (fun (x,ty,atts) ->
        (x, ty, {atts with implicit=true})
      ) trm_fvars
    in
      close_term ctx (mk_pi fvar_params trm)
  end


(* ----- Pretty printing. ------ *)
let dprintf b fmt =
  if b then Printf.printf fmt

let string_of_binder bb =
  match bb with
  | Let -> "let"
  | Lambda -> "λ"
  | Pi -> "Π"

let string_of_literal l =
  match l with
  | Numeral x -> Printf.sprintf "%d" x
  | Decimal x -> Printf.sprintf "%f" x
  | Rational x -> Printf.sprintf "%d/%d" (fst x) (snd x)

let string_of_param_attr ({implicit; list} : param_attr) =
  let imp_str = if implicit then ":implicit" else "" in
  let list_str = if list then ":list" else "" in
  Printf.sprintf "{ %s }"(
    String.concat ", " [imp_str; list_str]
  )

let string_of_var (x_opt : string option) =
  Option.fold ~none:"_" ~some:(fun x -> x) x_opt

let rec string_of_term' (bvs : (string option) list) (t : cc_term) =
  match t with
  | Univ KIND -> "KIND"
  | Univ TYPE -> "TYPE"
  | Literal l -> string_of_literal l
  | Implicit t -> "[" ^ string_of_term' bvs t ^ "]"
  | Var x -> x
  | Meta x -> "?" ^ x
  | Bound i -> (* Printf.sprintf "b%d" i *)
    begin match List.nth_opt bvs i with
    | Some x -> string_of_var x
    | None   -> Printf.sprintf "b%d" i
    end
  | App (e1, ((Bound _|Meta _|Var _|Literal _|Implicit _) as x)) ->
      string_of_term' bvs e1 ^ " " ^ string_of_term' bvs x
  | App(e1,e2) ->
      string_of_term' bvs e1 ^ " " ^ "(" ^ string_of_term' bvs (e2) ^ ")"
  | Bind(Let, (x,x_def,_), t') ->
      Printf.sprintf "let (%s ≡ %s) in %s"
      (string_of_var x) (string_of_term' bvs x_def)
      (string_of_term' (x::bvs) t')
  | Bind(bb, ((x,_,_) as p), t') ->
      Printf.sprintf "%s %s. %s"
        (string_of_binder bb) (string_of_param bvs p)
        (string_of_term' (x::bvs) t')

and string_of_param bvs (x,ty,atts) =
  let typ_str =
    Printf.sprintf "%s : %s"
    (string_of_var x) (string_of_term' bvs ty)
  in
  match (atts.implicit, atts.list) with
  | (true, true) -> Printf.sprintf "⟦%s⟧" typ_str
  | (true, false) -> Printf.sprintf "[%s]" typ_str
  | (false, true) -> Printf.sprintf "⦇%s⦈" typ_str
  | (false, false) -> Printf.sprintf "(%s)"typ_str
let string_of_term t = string_of_term' [] t

let string_of_rule (l,r) =
  Printf.sprintf "%s ↪ %s"
  (string_of_term l) (string_of_term r)

let string_of_rules rs =
  String.concat "\n" (List.map string_of_rule rs)

let string_of_attribute att =
  match att with
  | RightAssoc -> ":right-assoc"
  | LeftAssoc -> ":left-assoc"
  | RightAssocNil trm -> ":right-assoc-nil " ^ string_of_term trm
  | LeftAssocNil trm -> ":left-assoc-nil " ^ string_of_term trm
  | Chainable trm -> ":chainable " ^ string_of_term trm
  | Pairwise trm -> ":pairwise " ^ string_of_term trm
  | Binder trm -> ":binder " ^ string_of_term trm

let string_of_context ps =
  String.concat ", " (List.map (string_of_param []) ps)

let string_of_cmd cmd =
  match cmd with
  | Const (str, ty, att_opt) ->
    let ty_str = Printf.sprintf " : %s" (string_of_term ty) in
    let att_str = match att_opt with
      | Some att -> Printf.sprintf "\n  with %s" (string_of_attribute att)
      | None  -> ""
    in
      Printf.sprintf "const %s%s%s"
        str ty_str att_str
  | Defn (str, ty, def) ->
      Printf.sprintf "def %s : %s := %s"
        str (string_of_term ty) (string_of_term def)

  | Prog (str, ty) ->
      Printf.sprintf "prog %s : %s"
        str (string_of_term ty)
  | Rule (ps, rs) ->
    Printf.sprintf "rule %s\n%s"
      (string_of_context ps) (string_of_rules rs)

let string_of_sig sg =
  String.concat "\n" (List.map string_of_cmd sg)
