open Term
open Context

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

let mk_chain (f : term) (agg : term) (args : term list) : term =
  let rec chain_up args =
    match args with
    | [] -> f
    | [x] -> App (f,x)
    | x1 :: x2 :: rest ->
      let seg = app f [x1; x2] in
      match rest with
      | [] -> seg
      | _ -> app agg [seg; chain_up (x2 :: rest)]
  in
    chain_up args

let mk_pairwise (f : term) (agg : term) (args : term list) : term =
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

let mk_attr_app ctx bvs f args = function
  | Binder _ -> List.fold_left (fun e arg -> App (e, arg)) f args

  | Chainable agg -> mk_chain f agg args

  | Pairwise agg -> mk_pairwise f agg args

  | LeftAssoc ->
      match args with
      | [] -> f
      | [x] -> App (f, x)
      | x :: xs -> List.fold_left (fun acc y -> app f [acc; y]) x xs)

  | RightAssoc ->
      match args with
      | [] -> f
      | [x] -> App (f, x)
      | [x; y] -> app f [x; y]
      | x :: xs -> app f [x; mk_attr_app ctx f xs RightAssoc])

  | RightAssocNil nil ->
      begin match args with
      | [] -> f
      | [x] -> if Ctx.is_list ctx x then x else app f [x;nil]
      | _ ->
      let n = List.length args in
      let last = List.nth args (n - 1) in
      let init, start =
        if Ctx.is_list ctx last
        then (last, n - 2) else (nil, n - 1)
      in
      let rec aux i r =
        if i < 0 then r
        else
          let t = List.nth args i in
          let r' = if Ctx.is_list ctx bvs t then list_concat f t r else app f [t; r]
          in aux (i - 1) r'
      in
        aux start init
      end

  | LeftAssocNil nil ->
      let n = List.length args in
      if n <= 2 then
        app f args
      else
        let first = List.hd args in
        let init, start = if Ctx.is_list ctx first then (first, 1) else (nil, 0) in
        let n = List.length args in
        let rec aux i r =
          if i >= n then r
          else
            let t = List.nth args i in
            let r' =
              if Ctx.is_list ctx bvs t then list_concat_left f r t else app f [r; t]
            in
            aux (i + 1) r'
        in
          aux start init
