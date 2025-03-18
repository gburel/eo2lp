open Ast
open Ast_cc

type lp_univ = Set | Prop
type lp_binder = Pi | Lambda | Let

type lp_term =
  | Univ of lp_univ
  | Literal of literal
  | El of lp_term
  | Prf of lp_term
  | Explicit of lp_term
  | Bind of lp_binder * lp_var * lp_term
  | App of lp_term * lp_term
  | Var of string
  | Ptrn of string
  | Bound of int
and lp_var = string * lp_term * bool

type lp_attr =
  | Injective
  | Constant
  | Sequential

type lp_cmd =
  | Symbol of lp_attr option * string * lp_term option * lp_term option
  | Rule of (lp_term * lp_term) list

type lp_sig = lp_cmd list

(* ------- Pretty printing ------- *)
let string_of_lp_univ univ =
  match univ with
  | Set -> "Set"
  | Prop -> "Prop"

let string_of_lp_binder bb =
  match bb with
  | Pi -> "Π"
  | Lambda -> "λ"

let string_of_lp_attr att =
  match att with
  | Sequential -> "sequential"
  | Injective -> "injective"
  | Constant -> "constant"

let rec string_of_lp_term bvs trm =
  match trm with
  | Univ u -> string_of_lp_univ u
  | Literal l -> string_of_literal l
  | El t -> string_of_lp_term bvs (App (Var "El", t))
  | Prf t -> string_of_lp_term bvs (App (Var "Prf", t))
  | Explicit t -> "[" ^  string_of_lp_term bvs t ^ "]"
  | Bind (Let,(x,ty,_),t) ->
      Printf.sprintf "let %s ≔ %s in %s"
      x (string_of_lp_term bvs ty) (string_of_lp_term (x::bvs) t)
  | Bind (bb,((str,ty,_) as v),t) ->
    (* todo. clean parens *)
    begin match (bb,str) with
    | (Pi, "_") ->
      Printf.sprintf "(%s → %s)"
      (string_of_lp_term bvs ty)
      (string_of_lp_term (str::bvs) t)
    | _ ->
      Printf.sprintf "%s %s, %s"
      (string_of_lp_binder bb)
      (string_of_lp_var bvs v) (string_of_lp_term (str::bvs) t)
    end
  | App (App (Var "⤳ᵈ", t1), t2) ->
    Printf.sprintf "(%s ⤳ᵈ %s)"
    (string_of_lp_term bvs t1) (string_of_lp_term bvs t2)
  | App (App (Var "⤳", t1), t2) ->
    Printf.sprintf "(%s ⤳ %s)"
    (string_of_lp_term bvs t1) (string_of_lp_term bvs t2)
  | App (e1, ((Bound _| Var _|Ptrn _|Explicit _|Literal _) as x)) ->
      Printf.sprintf "%s %s"
      (string_of_lp_term bvs e1) (string_of_lp_term bvs x)
  | App(e1,e2) ->
      Printf.sprintf "%s (%s)"
      (string_of_lp_term bvs e1)
      (string_of_lp_term bvs e2)
  | Var x -> x
  | Ptrn x -> "$" ^ x
  | Bound i ->
    begin match List.nth_opt bvs i with
    | Some x -> x
    | None   -> Printf.sprintf "b%d" i
    end

and string_of_lp_var bvs (str,ty,b) =
  let ty_str = string_of_lp_term bvs ty in
  if b
    then Printf.sprintf "[%s : %s]" str ty_str
    else Printf.sprintf "(%s : %s)" str ty_str

let string_of_lp_cmd cmd =
  match cmd with
  | Symbol (att_opt, str, typ_opt, def_opt) ->
    let att_str =
      match att_opt with
      | Some att -> string_of_lp_attr att ^ " "
      | None -> ""
    in
    let typ_str =
      match typ_opt with
      | Some typ -> Printf.sprintf " : %s" (string_of_lp_term [] typ)
      | None -> ""
    in
    let def_str =
      match def_opt with
      | Some def -> Printf.sprintf " ≔ %s" (string_of_lp_term [] def)
      | None -> ""
    in
    att_str ^ "symbol " ^ str ^ typ_str ^ def_str ^ ";"
  | Rule rs ->
    let rule_str = String.concat "\nwith "
      (List.map (fun (l,r) -> string_of_lp_term [] l ^ " ↪ " ^ string_of_lp_term [] r) rs)
    in
      Printf.sprintf "rule %s;" rule_str


(* ------- Encoding ------- *)
let cc_lp_binder (bb : cc_binder) =
  match bb with
  | Pi -> Pi
  | Lambda -> Lambda
  | Let -> Let

module CharSet = Set.Make(Char)

(* Define the forbidden characters once at module level *)
let forbidden_chars =
  CharSet.of_list ['\t';'\r';'\n';':';',';';';'`';'(';')';'{';'}';'[';']';'\\';'"';'.';'@';'$';'|';'?';'/']

let is_valid_regular s =
  if s = "/" then true
  else if s = "" then false
  else String.for_all (fun c -> not (CharSet.mem c forbidden_chars)) s

let cc_lp_iden (str_opt : string option) : string =
  match str_opt with
  | None -> "_"
  | Some "_" -> "{|_|}"
  | Some str -> if is_valid_regular str then str else "{|" ^ str ^ "|}"



let encode_univ univ =
  match univ with
  | TYPE -> Set
  | KIND -> failwith "Cannot encode cc.KIND."

let rec shift (i : int) (j : int) (trm : cc_term) : cc_term =
  match trm with
  | (Univ _|Var _|Meta _|Literal _) -> trm
  | Explicit t -> Explicit (shift i j t)
  | Bound k -> if k > i then Bound (k + j) else Bound k
  | App (t1, t2) -> App(shift i j t1, shift i j t2)
  | Bind (bb, (x,ty,att), body) ->
    let ty' = shift i j ty in
    let body' = shift (i+1) j body in
    Bind (bb, (x,ty',att), body')

let mk_arrow (t1,t2) = App (App (Var "⤳", t1), t2)
let mk_dep_arrow (t1,t2) = App (App (Var "⤳ᵈ", t1), t2)

(* (encode_type e) : t,  t ∈ {TYPE, Set, Prop} *)
let rec encode_type (bvs : lp_var list) (trm : cc_term) : lp_term =
  match trm with
  | Meta _  -> failwith "Cannot encode metavaraiable."
  | Literal l -> Literal l
  | Explicit t -> Explicit (encode_type bvs t)
  | Univ u -> Univ (encode_univ u)
  | Bind (Pi, (x,ty,att), body) ->
    let v' = (cc_lp_iden x, encode_type bvs ty, att.implicit) in
    Bind (Pi, v', encode_type (v'::bvs) body)
  | Bound i ->
    begin match List.nth_opt bvs i with
    | Some (_, Univ Set,_) -> El (Bound i)
    | Some _ -> Bound i
    | None -> failwith "Bound variable not found in list."
    end
  | _ -> El (encode_term bvs trm)

(* (encode_term e) : t, t ∈ { El (..), Prf (..) } *)
and encode_term (bvs : lp_var list) (trm : cc_term) : lp_term =
  match trm with
  | Meta _ -> failwith "Cannot encode metavaraiable."
  | Explicit t -> Explicit (encode_term bvs t)
  | Literal l -> Literal l
  | Univ _ -> failwith "Cannot encode universe expression as an lp-term."
  | Bind (Pi, (str_opt,ty,att), body) ->
    let ty' = encode_term bvs ty in
    begin match str_opt with
    | None -> mk_arrow (ty', encode_term bvs (shift 0 (-1) body))
    | Some str -> mk_dep_arrow (ty', Bind (Lambda, (str,ty',att.implicit), encode_term bvs body))
    end
  | Bind (Let, (v,def,_), body) ->
    let v' = (cc_lp_iden v, encode_term bvs def, false) in
    Bind (
      cc_lp_binder Let, v',
      encode_term (v'::bvs) body
    )
  | Bind (bb, (x,ty,att), body) ->
    let v' = (cc_lp_iden x, encode_type bvs ty, att.implicit) in
    Bind (
      cc_lp_binder bb, v',
      encode_term (v'::bvs) body
    )
  | Bound i -> Bound i
  | Var x   -> Var (cc_lp_iden (Some x))
  | App (App (App (App (Var "_", Explicit _), Explicit _), f), x) ->
      App (encode_term bvs f, encode_term bvs x)
  | App (App (Var "_", f), x) ->
      App (encode_term bvs f, encode_term bvs x)
  | App (t1,t2) ->
      App (encode_term bvs t1, encode_term bvs t2)

let rec map_lp_term (f : string -> lp_term) = fun trm ->
  match trm with
  | Univ u -> Univ u
  | Literal l -> Literal l
  | El t -> map_lp_term f t
  | Prf t -> map_lp_term f t
  | Explicit t -> Explicit (map_lp_term f t)
  | Bind (bb, (str,ty,b), body) ->
      Bind (bb, (str, map_lp_term f ty, b), map_lp_term f body)
  | App (t1,t2) -> App (map_lp_term f t1, map_lp_term f t2)
  | Bound i -> Bound i
  | Ptrn x -> Ptrn x
  | Var x -> f x


let mk_ptrn_vars (vs : string list) =
  let f = (fun x -> if List.mem x vs then Ptrn x else Var x)
  in map_lp_term f

let cc_lp (cmd : cc_command) =
  match cmd with
  | Const (str, ty) ->
      Symbol (
        Some Constant,
        cc_lp_iden (Some str),
        Some (encode_type [] ty),
        None
      )
  | Defn (str, ty, trm) ->
      Symbol (
        None,
        cc_lp_iden (Some str),
        Some (encode_type [] ty),
        Some (encode_term [] trm)
      )
  | LitTy _ -> Symbol (None, "dummy", Some (Univ Set), None)
  | Prog (str,ty) ->
      Symbol (
        Some Sequential,
        cc_lp_iden (Some str),
        Some (encode_type [] ty),
        None
      )
  | Rule (params, rws) ->
    let ctx = ctx_append_param params Translation.tdata.context in
    let infer = Inference.infer_term ctx StrMap.empty in
    let rws' = map_cc_rule infer rws in
    let enc t = mk_ptrn_vars
      (List.map (fun (Some x,_,_) -> x) params) (encode_term [] t) in
    let encode_rule = (fun (lhs,rhs) -> (enc lhs, enc rhs)) in
    Rule (List.map encode_rule rws')

let cc_lp_debug cmd =
  Printf.printf "Encoding cc-command:\n%s\n" (string_of_cmd cmd);
  let cmd' = cc_lp cmd in
  Printf.printf "Done:\n%s\n\n" (string_of_lp_cmd cmd');
  cmd'
