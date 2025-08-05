open Ast

(* ----- Datatypes. ------ *)
type universe = TYPE | KIND
[@@deriving show]

type cc_binder =
  | Let
  | Lambda
  | Pi
[@@deriving show]

type cc_term =
  | Univ of universe
  | Literal of literal
  | Explicit of cc_term
  | Var of string
  | Meta of int
  | Bound of int
  | App of cc_term * cc_term
  | Bind of cc_binder * param * cc_term
and param = string option * cc_term * cc_atts
and cc_atts = {
    definition : cc_term option;
    implicit : bool;
    list : bool;
    apply : app_attr option;
    premise_list : cc_term option;
  }
and app_attr =
  | RightAssoc
  | LeftAssoc
  | RightAssocNil of cc_term
  | LeftAssocNil of cc_term
  | Chainable of cc_term
  | Pairwise of cc_term
  | Binder of cc_term

type cc_context = param StrMap.t

type cc_rule = (cc_term * cc_term) list
type cc_command =
  | Const of string * cc_term
  | Defn of string * cc_term * cc_term
  | Prog of string * cc_term
  | Rule of param list * cc_rule
  | LitTy of lit_category * cc_term

(* ------ Utilities ------ *)
let atts_init = {
  definition = None;
  implicit = false;
  list = false;
  apply = None;
  premise_list = None;
}

let is_univ trm = match trm with
  | Univ _ -> true
  | _ -> false

let is_var trm = match trm with
  | (Var _|Bound _|Meta _) -> true
  | _ -> false

let var = fun x -> Var x
let param_var (str_opt,_,_) =
  Option.fold ~none:(Var "BLANK") ~some:(fun str -> Var str) str_opt

let ctx_init = StrMap.empty

let ctx_join (c1 : cc_context) (c2 : cc_context) : cc_context =
  StrMap.union (fun _ p _ -> Some p) c1 c2

let mk_param (str : string) (ty : cc_term) : param =
  (Some str, ty, atts_init)

let ctx_add str typ ctx = StrMap.add str (mk_param str typ) ctx

let ctx_add_param ((str_opt, _, _) as p) ctx =
  match str_opt with
  | Some str -> StrMap.add str p ctx
  | None -> failwith "Cannot add nameless parameter to context."

let ctx_append_param params ctx =
  List.fold_left (fun acc p -> ctx_add_param p acc) ctx params

(* let param_var ((_,_) : param) =
  match x_opt with
  | Some x -> Var x
  | None -> failwith "Cannot create variable from nameless parameter." *)



let is_binder bb trm = match trm with
  | Bind (bb', _, _) -> bb = bb'
  | _ -> false

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


let rec map_cc_term
  (f : string option list -> string -> cc_term)
  (bvs : string option list) (trm : cc_term)
  = match trm with
  | (Univ _|Meta _|Bound _|Literal _) -> trm
  | Explicit t -> Explicit (map_cc_term f bvs t)
  | Var x -> f bvs x
  | App (t1,t2) -> App (map_cc_term f bvs t1, map_cc_term f bvs t2)
  | Bind (bb, (str_opt, ty, atts), trm') ->
    let x' = (str_opt, map_cc_term f bvs ty, atts) in
    Bind (bb, x', map_cc_term f (str_opt::bvs) trm')

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

let mk_bounds (xs : string option list) (trm : cc_term) =
  map_cc_term (fun bvs str ->
    match List.find_index (fun x -> x = Some str) bvs with
    | Some i -> Bound i
    | None -> Var str
  ) xs trm

let mk_pi (xs : param list) (trm : cc_term) =
  let rec aux bvs (ys : param list) trm : cc_term =
    match ys with
    | [] -> mk_bounds bvs trm
    | (str_opt, ty,atts)::ys' ->
    Bind (Pi, (str_opt, mk_bounds bvs ty, atts), aux (str_opt::bvs) ys' trm)
  in
    aux [] xs trm

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

module ParamSet = Set.Make(Param)
type param_set = ParamSet.t

let rec bvars (bvs : param list) (trm : cc_term) : param_set =
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

let map_bvars (bvs : param list) (ts : cc_term list) =
  List.fold_left (fun vs t -> ParamSet.union (bvars bvs t) vs) ParamSet.empty ts

let map_bvars_list (bvs : param list) (trms : cc_term list) : param list =
  ParamSet.to_list (map_bvars bvs trms)

let rec filter_vars (ctx : cc_context) (trm : cc_term) : param_set =
  match trm with
  | Univ _ -> ParamSet.empty
  | Bound _ -> ParamSet.empty
  | Var x ->
    begin match StrMap.find_opt x ctx with
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

let string_of_var (x_opt : string option) =
  Option.fold ~none:"_" ~some:(fun x -> x) x_opt


let rec string_of_term' (bvs : (string option) list) (t : cc_term) =
  match t with
  | Univ KIND -> "KIND"
  | Univ TYPE -> "TYPE"
  | Literal l -> string_of_literal l
  | Explicit t -> "[" ^ string_of_term' bvs t ^ "]"
  | Var x -> "!" ^ x
  | Meta x -> "?" ^ (string_of_int x)
  | Bound i -> (* Printf.sprintf "b%d" i *)
    begin match List.nth_opt bvs i with
    | Some x -> string_of_var x
    | None   -> Printf.sprintf "b%d" i
    end
  | App (e1, ((Bound _|Meta _|Var _|Literal _|Explicit _) as x)) ->
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

and string_of_attribute att =
  match att with
  | RightAssoc -> ":right-assoc"
  | LeftAssoc -> ":left-assoc"
  | RightAssocNil trm -> ":right-assoc-nil " ^ string_of_term trm
  | LeftAssocNil trm -> ":left-assoc-nil " ^ string_of_term trm
  | Chainable trm -> ":chainable " ^ string_of_term trm
  | Pairwise trm -> ":pairwise " ^ string_of_term trm
  | Binder trm -> ":binder " ^ string_of_term trm

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

and string_of_term t = string_of_term' [] t

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
