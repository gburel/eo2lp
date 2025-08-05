open Prelude

(* -------- Datatypes. -------- *)
type term =
  | Univ of universe
  | Literal of literal
  | Explicit of term
  | Var of string
  | Meta of int
  | Bound of int
  | App of term * term
  | Let of string * term * term
  | Bind of binder * param * term
and universe = Type | Kind
and binder = Lambda | Pi
and datum = {
  typ : term;
  implicit : bool;
  list : bool;
}
and param = string option * datum
[@@deriving show]

let param_name : param -> string = function
  | (Some str, _) -> str
  | (None, _) -> "_"


(* Modify the variable 'leaves' of a term. *)
let map_term (f : param list -> string -> term) : term -> term =
  let rec aux bvs trm =
    match trm with
    | (Univ _|Meta _|Bound _|Literal _) -> trm
    | Explicit t -> Explicit (aux bvs t)
    | Var x -> f bvs x
    | App (t1,t2) -> App (aux bvs t1, aux bvs t2)
    | Bind (bb, (str_opt, dat), trm') ->
      let dat' = { dat with typ = aux bvs dat.typ } in
      Bind (
        bb, (str_opt, dat'),
        aux ((str_opt, dat')::bvs) trm'
      )
  in
    aux []

let capture_vars (xs : param list) (trm : term) =
  map_term (fun bvs str ->
    match List.find_index (fun x -> fst x = Some str) (bvs @ xs) with
    | Some i -> Bound i
    | None -> Var str
  ) trm

let bind_vars (bb : binder) (xs : param list) (trm : term) =
  let rec aux ys xs =
    match xs with
    | [] -> ys
    | (str_opt, dat) :: xs' ->
      let dat' = { dat with typ = capture_vars ys dat.typ } in
      aux ((str_opt, dat')::ys) xs'
  in
    List.fold_left (fun acc x -> Bind (bb, x, acc)) trm (aux [] xs)


(* -------- Pretty printing --------- *)
let rec string_of_term_aux (bvs : param list) (t : term) =
  match t with
  | Univ Kind -> "KIND"
  | Univ Type -> "TYPE"
  | Literal l -> string_of_literal l
  | Explicit t -> "[" ^ string_of_term_aux bvs t ^ "]"
  | Var x -> x
  | Meta x -> "?" ^ (string_of_int x)
  | Bound i ->
    begin match List.nth_opt bvs i with
    | Some x -> Printf.sprintf "(b%d ⇾ %s)" i (string_of_param bvs x)
    | None   -> Printf.sprintf "(b%d ⇾ •)" i
    end
  | App (e1, ((Bound _|Meta _|Var _|Literal _|Explicit _) as x)) ->
      string_of_term_aux bvs e1 ^ " " ^ string_of_term_aux bvs x
  | App(e1,e2) ->
      string_of_term_aux bvs e1 ^ " " ^ "(" ^ string_of_term_aux bvs (e2) ^ ")"
  | Let (str, t1, t2) ->
      Printf.sprintf "let %s := %s in %s"
      str (string_of_term_aux bvs t1) (string_of_term_aux bvs t2)
  | Bind(bb, (x, d), t') ->
      Printf.sprintf "%s %s. %s"
        (string_of_binder bb) (string_of_param bvs (x,d))
        (string_of_term_aux ((x,d)::bvs) t')

and string_of_binder bb = match bb with
  | Lambda -> "λ"
  | Pi -> "Π"

and string_of_param bvs (str_opt, datum) =
  let var_str = Option.fold ~none:"_" ~some:(fun str -> str) str_opt in
  let typ_str = string_of_term_aux bvs datum.typ in
  let mem_str = var_str ^ " : " ^ typ_str in
  match (datum.implicit, datum.list) with
  | (true, true) -> Printf.sprintf "⟦%s⟧" mem_str
  | (true, false) -> Printf.sprintf "[%s]" mem_str
  | (false, true) -> Printf.sprintf "⦇%s⦈" mem_str
  | (false, false) -> Printf.sprintf "(%s)" mem_str

let string_of_term t = string_of_term_aux [] t


(* -------- Utilities -------- *)
let is_univ trm = match trm with
  | Univ _ -> true
  | _ -> false

let is_var trm = match trm with
  | (Var _|Bound _|Meta _) -> true
  | _ -> false

let is_binder bb trm = match trm with
  | Bind (bb', _, _) -> bb = bb'
  | _ -> false

let app : term -> term list -> term =
  List.fold_left (fun acc y -> App (acc, y))

let appvar (str : string) : term list -> term = app (Var str)
