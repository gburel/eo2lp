require open Logic.U.Arrow;

symbol 𝒮 : TYPE;
builtin "String" ≔ 𝒮;
symbol string : Set;

symbol List : TYPE;
injective symbol list : Set → Set;
injective symbol ⋅ [a] : El (list a);
injective symbol ⨾ [a] : El (a ⤳ list a ⤳ list a);
notation ⨾ infix right 10;

symbol map [a b] : El ((a ⤳ b) ⤳ list a ⤳ list b);
rule (map $f (⋅)) ↪ (⋅)
with (map $f ($x ⨾ $xs)) ↪ ($f $x) ⨾ (map $f $xs);

// type of eo terms
symbol eo : Set;
injective symbol sym : El (string ⤳ eo);
injective symbol app : El (string ⤳ list eo ⤳ eo);


type (app "and" (cons "true" (cons "true" nil)));

symbol eo' : Set;
injective symbol sym' : El (string ⤳ eo');
injective symbol app' : El (eo' ⤳ eo' ⤳ eo');

symbol elaborate : El (eo ⤳ eo');

symbol ctyp : El (string) → Set;
symbol ctm  (s : El string) : El (ctyp s);

symbol interp : El (eo' ⤳ eo' ⤳ ....)




symbol Halt : El eo;

symbol EO : TYPE ≔ El eo;

// every symbol annotated with a type
injective symbol !! : 𝒮 → EO → EO;
injective symbol --> : El (list eo ⤳ eo);
injective symbol Type : El eo;

// given an arrow type `-> t1 .. tn`, and a list `e1 .. e_(n-1)`
// return `tn`, checking that each `t_i == e_i` for each i .. n-1.
sequential symbol app_tys : El (eo ⤳ list eo ⤳ eo);
rule app_tys (--> ($e ⨾ ⋅)) (⋅) ↪ $e
with app_tys (--> ($e ⨾ $es)) ($e ⨾ $es')
  ↪ (app_tys (--> $es) $es')
with app_tys (--> ($e ⨾ _)) ($e' ⨾ _) ↪ Halt
with app_tys (--> ⋅) _ ↪ Halt // empty arrow type, halt.
with app_tys _ _ ↪ Halt; // not an eo term denoting a function type, so halt.

// calculate the type of `e : EO` as an `EO`.
// needs to change to compensate for n-ary operations.
sequential symbol ty : EO → EO;
rule (ty (!! $str $t)) ↪ ($t)
with (ty (app $e $es)) ↪ (app_tys (ty $e) (map ty $es));


symbol HALT : TYPE;
symbol ∅ : Set;

// interpret a Eunoia kind as a type.
sequential symbol Ki : EO → TYPE;
rule (Ki Type) ↪ Set
with (Ki Halt) ↪ HALT
with (Ki (--> ($e ⨾ ⋅))) ↪ Ki $e
with (Ki (--> ($e ⨾ $es))) ↪ Ki $e → (Ki (--> $es));


injective symbol 𝚻 : 𝒮 → Set;

// interpret a Eunoia type as a set-code.
sequential symbol Ty : EO → Set;
rule (Ty Halt) ↪ ∅
with (Ty Type) ↪ ∅
with (Ty (!! $str Type)) ↪ 𝚻 $str
//with (Ty (app (!! $str Type)) $es) ↪ 𝚻 $str
with (Ty (--> ($e ⨾ ⋅)))   ↪ Ty $e
with (Ty (--> ($e ⨾ $es))) ↪ Ty $e ⤳ (Ty (--> $es));

// some tests.
symbol b ≔ (!! "Bool" Type);
symbol l ≔ (!! "List" (--> (Type ⨾ Type ⨾ ⋅)));

symbol lc ≔ (!! "and" (--> (b ⨾ b ⨾ b ⨾ ⋅)));
symbol t ≔ (!! "true" (b));

compute Ty (ty (app (lc) (t ⨾ t ⨾ ⋅)));

symbol lctt ≔ (app lc (t ⨾ t ⨾ ⋅));

compute Ty (ty (lctt));

symbol lb ≔ (app l (b ⨾ ⋅));
compute Ty (ty l);

compute ty (app lc (t ⨾ t ⨾ ⋅));



sequential symbol tm (str : 𝒮) : ty str;
// rw. rules defined throughout translation. e.g.,
rule (tm "Bool") ↪ Bool;
rule (tm "and")  ↪ and;

symbol foldl [a b] :
  El ((b ⤳ a ⤳ b) ⤳ b ⤳ list a ⤳ b);
rule (foldl $f $acc (⋅)) ↪ $acc
with (foldl $f $acc ($x ⨾ $xs)) ↪ foldl $f ($f $acc $x) $xs;

symbol eo' : Set;
symbol EO' : TYPE ≔ El eo';

injective symbol !! : 𝒮 → EO' → EO';
injective symbol __ : EO' → EO' → EO';

symbol elab : EO → EO';
rule (elab (sym $str)) ↪ (sym' $str)
with (elab (app $str $es))
  ↪ foldl (λ acc e, __ acc e) (!! $str $t) (map elab $es);

compute
  let foo ≔ app "and" (sym "true" ⨾ sym "true" ⨾ ⋅) in
  elab foo;

symbol Typ : EO' → TYPE;
symbol ty_of : EO' → EO';

symbol ev_tm : (Π e : EO', Typ (ty_of e));

rule (Typ (sym' "Type")) ↪ Set;
rule (ty_of (sym' "Type")) ↪ (sym' "Kind");

rule (ty_of (sym' "Bool")) ↪ (sym' "Type");
rule (ev_tm (sym' "Bool")) ↪ Bool;
rule (Typ (sym' "Bool")) ↪ El Bool;

compute ev_tm (sym' "Bool");

rule (ty_of (sym' "not")) ↪ ( "Type");
rule (ev_tm (sym' "Bool")) ↪ Bool;
rule (Typ (sym' "Bool")) ↪ El Bool;
