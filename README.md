This repository contains a tool for translating
  [Eunoia](https://github.com/cvc5/ethos/blob/main/user_manual.md)
to
  [LambdaPi](https://github.com/Deducteam/lambdapi).

The terms of Eunoia are interpreted in an OCaml datatype representing the terms
of Calculus of Constructions (CC). To translate to LambdaPi, terms are encoded
in a Tarski-style type universe and then finally translated to LambdaPi source.
