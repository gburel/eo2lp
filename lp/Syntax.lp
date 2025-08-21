require open Logic.U.Arrow;

symbol 𝒮 : TYPE;
builtin "String" ≔ 𝒮;

symbol List : TYPE;

constant symbol Bool : Set;
constant symbol true : El Bool;
constant symbol and : El (Bool ⤳ Bool ⤳ Bool);

injective symbol list : Set → Set;
injective symbol ⋅ [a] : El (list a);
injective symbol ⨾ [a] : El (a ⤳ list a ⤳ list a);
notation ⨾ infix right 10;

symbol map [a b] : El ((a ⤳ b) ⤳ list a ⤳ list b);
rule (map $f (⋅)) ↪ (⋅)
with (map $f ($x ⨾ $xs)) ↪ ($f $x) ⨾ (map $f $xs);

symbol eo : Set;
symbol EO : TYPE ≔ El eo;

injective symbol sym : 𝒮 → El (eo);
injective symbol app : 𝒮 → El (list eo ⤳ eo);

sequential symbol ty : 𝒮 → TYPE;
// rw. rules defined throughout translation. e.g.,
rule (ty "Bool") ↪ Set
with (ty "and") ↪ El (Bool ⤳ Bool ⤳ Bool);

sequential symbol tm (str : 𝒮) : ty str;
// rw. rules defined throughout translation. e.g.,
rule (tm "Bool") ↪ Bool;
rule (tm "and")  ↪ and;


symbol foldl [a b] :
  El ((b ⤳ a ⤳ b) ⤳ b ⤳ list a ⤳ b);
rule (foldl $f $acc (⋅)) ↪ $acc
with (foldl $f $acc ($x ⨾ $xs)) ↪ foldl $f ($f $acc $x) $xs;


symbol __ : EO → EO → EO;
rule (__ $e $e') ↪ (app "_" ($e ⨾ $e' ⨾ ⋅));

symbol foo : EO ≔
  foldl (λ acc e, __ acc e)
    (sym "and") (sym "true" ⨾ sym "true" ⨾ ⋅);

symbol typ : EO → EO;
symbol ev [a] : EO → El a;
