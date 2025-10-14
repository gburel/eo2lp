- section 1:
  - Eunoia,
  - SMT-LIB 3,
  - cvc5, CPC
  - lambdapi/dedukti.
  - SMT-LIB. 2.6., 2.7.,
    3.0: proposal, Barrett, Chad Brown,
    Eunoia.
  - cvc5.
  - Alethe.
      CITE. Alethe specification, surrounding papers
  - LFSC.
      old and ugly.
      ad-hoc side conditions ???
  - LambdaPi.
      CITE. Alessio's work on lambdapi output for Carcara.
      cite successful and ongoing translation projects.
      why3. current interface for ATP in lambdapi is untrusted/orcale.

- section 2:
  - discussion of commands
  - definition of term elaboration wrt. attributes
  - builtin-commands. "computational operators"
  - discussion of CPC as a Eunoia signature
  - example of cvc5 proof using cpc rules

- section 4: "results"
  - term/type-level translation
  - top-level translation.
    - (parameterized) consts. easy
    - definition
    - program
    - declare-rule
    - include
  - assume, step
  - definition of term level trans
  - rodin proof benchmarks.
  - cpc-mini.
    - `program-schema`.
    - `eo::Int`
    - insertion of explicit applications.
    - removed cases from $run_evaluate.
  - eo2lp implementation in Ocaml.
  - limitations.....
    - 'declare-consts' for literals.
  - example of translated signature
  - example of translated proofs

- section 5: "future work and conclusion"
  - towards a formal type-theoretic semantics for Eunoia
  - towards detailing correspondence between λΠ-calculus and LambdaPi.
  - towards interoperability of SMT in LambdaPi ecosystem.
  <!---->
  - prototype type checker for Eunoia.
  - prototype proof checker for cvc5.
  <!---->
  - larger benchmark, longer proofs (within QFUF).
  - cover all of CPC,
    align implementation with current version of Eunoia,
  - verifying the rules of CPC in lambdapi wrt. some small logic.
  <!---->
  - thanks:
      INRIA, CARMA, AWS.
      Haniel, Yoni Zohar, Hans-Jorg, Theo.
<!--

   (* in SMT3 but not Eunoia.
  | Import of string list
  | Open of string
  | DefineSyntax of syntax_rule * syntax_rule list
  | DefineValues of eo_term * eo_term * eo_term
  | DefineModule of ...
  | DeclareInductiveTypes of  ...
  | DefineEnumerationType of  ...
*)

(* in Eunoia but not SMT3
  | DeclareRule of string * eo_var list * assm option * prems option * args option * reqs option * eo_term
  | DeclareConsts of lit_category * eo_term
  | DeclareParamConst of string * eo_var list * eo_term * attr list
  | DeclareOracleFun of string * eo_term list * eo_term * string
  | Include of string
  | Program of string * eo_var list * eo_term list * eo_term * (eo_term * eo_term) list
  | Reference of string * string option

*)-->
