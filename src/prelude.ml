type literal =
  | Numeral of int
  | Rational of (int * int)
  | Decimal of float
[@@deriving show]

let string_of_literal l =
  match l with
  | Numeral x -> Printf.sprintf "%d" x
  | Decimal x -> Printf.sprintf "%f" x
  | Rational x -> Printf.sprintf "%d/%d" (fst x) (snd x)

module StrMap = Map.Make(String)
