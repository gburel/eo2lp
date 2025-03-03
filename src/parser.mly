%{
open Ast
%}

%token <string> SYMBOL STRING
%token <int> NUMERAL
%token <float> DECIMAL
%token <int * int> RATIONAL

%token LPAREN RPAREN COLON BANG EOF
%token // syntactic categories for literals
  STR NUM DEC RAT BIN HEX
%token EO_MATCH EO_DEFINE
%token // control commands
  CHECK_SAT CHECK_SAT_ASSUMING ECHO EXIT GET_ASSERTIONS GET_ASSIGNMENT GET_INFO GET_MODEL
  GET_OPTION GET_PROOF GET_UNSAT_ASSUMPTIONS GET_UNSAT_CORE GET_VALUE POP PUSH RESET
  RESET_ASSERTIONS SET_INFO SET_LOGIC SET_OPTION
%token // context modifying commands
  ASSERT DECLARE_CONST DECLARE_DATATYPE DECLARE_DATATYPES DECLARE_FUN DECLARE_SORT
  DECLARE_TYPE DEFINE_CONST DEFINE_FUN DEFINE_FUN_REC DEFINE_FUNS_REC DEFINE_SORT DEFINE_TYPE
%token // eo commands
  DECLARE_RULE PROGRAM PROGRAM_SCHEMA INCLUDE REFERENCE
  DECLARE_CONSTS DECLARE_PARAMETERIZED_CONST DECLARE_ORACLE_FUN
%token // attributes for `declare-rule`
  CONCLUSION ASSUMPTION PREMISE_LIST PREMISES ARGS REQUIRES RULE
%token // proof script commands
  ASSUME ASSUME_PUSH DEFINE STEP STEP_POP

%start <eo_command option> toplevel_eof

%%
toplevel_eof:
  | EOF { None }
  | toplevel { Some $1 }

toplevel:
  | base_command { Base $1 }
  | eunoia_command   { EO $1 }
  | control_command { Ctrl $1 }
  | proof_command   { Prf $1 }
term:
  | NUMERAL { Literal (Numeral $1) }
  | DECIMAL { Literal (Decimal $1) }
  | RATIONAL { Literal (Rational $1) }
  | SYMBOL
    { Symbol $1 }
  | LPAREN; SYMBOL; nonempty_list(term); RPAREN
    { AppList ($2, $3) }
  | LPAREN; EO_DEFINE; LPAREN; nonempty_list(eo_var); RPAREN; term; RPAREN
    { Define ($4, $6) }
  | LPAREN; EO_MATCH; LPAREN; list(eo_var); RPAREN; term;
      LPAREN; list(term_pair); RPAREN; RPAREN
    { Match ($4, $6, $8) }
  | LPAREN; BANG; term; list(req_attr); list(attr); RPAREN
    { Attributed ($3, $4, $5) }
eo_var:
  | LPAREN; SYMBOL; term; list(attr); RPAREN
    { ($2, $3, $4) }
attr:
  | COLON; SYMBOL; option(term) { ($2, $3) }
req_attr:
  | REQUIRES; LPAREN; term; term; RPAREN { ($3, $4) }
term_pair:
  | LPAREN; term; term; RPAREN { ($2, $3) }
lit_category:
  | NUM { NUM }
  | DEC { DEC }
  | RAT { RAT }
  | BIN { BIN }
  | HEX { HEX }
  | STR { STR }
base_command:
  | LPAREN; ASSERT; term; RPAREN
    { Assert ($3) }
  | LPAREN; DECLARE_CONST; SYMBOL; term; list(attr); RPAREN
    { DeclareConst ($3, $4, $5) }
  | LPAREN; DEFINE_CONST; SYMBOL; term; RPAREN
    { DefineConst ($3, $4) }
  | LPAREN; DECLARE_DATATYPE; SYMBOL; datatype_decl; RPAREN;
    { DeclareDatatype ($3, $4) }
  | LPAREN; DECLARE_DATATYPES; LPAREN; list(sort_decl); RPAREN; LPAREN; list(datatype_decl); RPAREN; RPAREN;
    { DeclareDatatypes ($4, $7) }
  | LPAREN; DECLARE_FUN; SYMBOL; LPAREN; list(term); RPAREN; term; list(attr); RPAREN
    { DeclareFun ($3, $5, $7, $8) }
  | LPAREN; DEFINE_FUN; function_def; RPAREN
    { DefineFun ($3) }
  | LPAREN; DEFINE_FUN_REC; function_def; RPAREN
    { DefineFunRec ($3) }
  | LPAREN; DEFINE_FUNS_REC;
      LPAREN; nonempty_list(funs_decl); RPAREN;
      LPAREN; nonempty_list(term); RPAREN;
    RPAREN
    { DefineFunsRec ($4, $7) } (*insert length check here?*)
  | LPAREN; DECLARE_TYPE; SYMBOL; LPAREN; list(term); RPAREN; RPAREN
    { DeclareType ($3, $5) }
  | LPAREN; DEFINE_TYPE; SYMBOL; LPAREN; list(term); RPAREN; term; RPAREN
    { DefineType ($3, $5, $7) }
  | LPAREN; DECLARE_SORT; sort_decl; RPAREN
    { DeclareSort ($3) }
  | LPAREN; DEFINE_SORT; SYMBOL; LPAREN; list(SYMBOL); RPAREN; term; RPAREN
    { DefineSort ($3, $5, $7) }
function_def:
  | SYMBOL; LPAREN; list(eo_var); RPAREN; term; term; { ($1, $3, $5, $6) }
funs_decl:
  | LPAREN; SYMBOL; LPAREN; list(eo_var); RPAREN; term; RPAREN;
    { ($2, $4, $6) }
datatype_decl:
  | LPAREN; nonempty_list(cons_decl); RPAREN { $2 }
cons_decl:
  | LPAREN; SYMBOL; list(var_decl); RPAREN { ($2, $3) }
var_decl:
  | LPAREN; SYMBOL; term; RPAREN { ($2, $3) }
sort_decl:
  | LPAREN; SYMBOL; NUMERAL; RPAREN { ($2, $3) }

eunoia_command:
  | LPAREN; DEFINE; SYMBOL; LPAREN; list(eo_var); RPAREN; term; RPAREN
    { Define ($3, $5, $7) }
  | LPAREN; DECLARE_CONSTS; lit_category; term; RPAREN
    { DeclareConsts ($3, $4) }
  | LPAREN; DECLARE_RULE; SYMBOL;
      LPAREN; list(eo_var); RPAREN; rule_attr; RPAREN
    { DeclareRule ($3, $5, $7) }
// (declare-parameterized-const <symbol> (<typed-param>*) <type> <attr>*)
  | LPAREN; DECLARE_PARAMETERIZED_CONST; SYMBOL;
      LPAREN; list(eo_var); RPAREN; term; list(attr); RPAREN
    { DeclareParamConst ($3, $5, $7, $8)}
// (declare-oracle-fun <symbol> (<type>*) <type> <symbol>)
  | LPAREN; DECLARE_ORACLE_FUN; SYMBOL;
      LPAREN; list(term); RPAREN; term; SYMBOL; RPAREN
    { DeclareOracleFun ($3, $5, $7, $8) }
  | LPAREN; INCLUDE; STRING; RPAREN
    { Include ($3) }
// (program <symbol> (<typed-param>*) (<type>*) <type> ((<term> <term>)+))
  | LPAREN; PROGRAM; SYMBOL; LPAREN; list(eo_var); RPAREN;
      LPAREN; list(term); RPAREN; term;
      LPAREN; nonempty_list(term_pair); RPAREN; RPAREN
    { Program ($3, None, $5, $8, $10, $12) }
  | LPAREN; PROGRAM_SCHEMA; COLON; SYMBOL; SYMBOL; LPAREN; list(eo_var); RPAREN;
      LPAREN; list(term); RPAREN; term;
      LPAREN; nonempty_list(term_pair); RPAREN; RPAREN
    { Program ($5, Some $4, $7, $10, $12, $14)}
  | LPAREN; REFERENCE; STRING; option(SYMBOL); RPAREN
    { Reference ($3, $4) }

rule_attr:
  | option(assumption); option(premises); option(arguments); option(reqs); conclusion; list(attr)
    { {assumes = $1; prems = $2; arguments = $3; requires = $4; conclusion = $5; attrs = $6} }
assumption:
  | ASSUMPTION; term { $2 }
premises:
  | PREMISES; LPAREN; list(term); RPAREN { Premises $3 }
  | PREMISE_LIST; term; term { PremiseList ($2, $3) }
arguments:
  | ARGS; LPAREN; list(term); RPAREN { $3 }
reqs:
  | REQUIRES; LPAREN; list(term_pair); RPAREN { $3 }
conclusion:
  | CONCLUSION; term { $2 }

proof_command:
  | LPAREN; ASSUME; SYMBOL; term; RPAREN
    { Assume ($3, $4) }
  | LPAREN; ASSUME_PUSH; SYMBOL; term; RPAREN
    { AssumePush ($3, $4) }
  | LPAREN; STEP; SYMBOL; option(term); RULE; SYMBOL; option(premises); option(arguments); RPAREN
    { Step ($3, $4, $6, $7, $8) }
  | LPAREN; STEP_POP; SYMBOL; option(term); RULE; SYMBOL; option(premises); option(arguments); RPAREN
    { StepPop ($3, $4, $6, $7, $8) }

control_command:
  | LPAREN; ECHO; STRING; RPAREN { Echo $3 }
  | LPAREN; EXIT; RPAREN { Exit }
  | LPAREN; CHECK_SAT; RPAREN { CheckSatAssuming [] }
  | LPAREN; CHECK_SAT_ASSUMING; LPAREN; list(term); RPAREN; RPAREN { CheckSatAssuming $4 }
  | LPAREN; RESET; RPAREN { Reset }
  | LPAREN; PUSH; NUMERAL; RPAREN { Push $3 }
  | LPAREN; POP; NUMERAL; RPAREN { Pop $3 }
  | LPAREN; SET_INFO; attr; RPAREN { SetInfo $3 }
  | LPAREN; GET_INFO; STRING; RPAREN { GetInfo $3 }
  | LPAREN; SET_LOGIC; SYMBOL; RPAREN { SetLogic $3 }
  | LPAREN; SET_OPTION; STRING; RPAREN { SetOption $3 }
  | LPAREN; GET_OPTION; STRING; RPAREN { GetOption $3 }
  | LPAREN; RESET_ASSERTIONS; RPAREN { ResetAssertions }
  | LPAREN; GET_ASSERTIONS; RPAREN { GetAssertions }
  | LPAREN; GET_VALUE; LPAREN; list(term); RPAREN; RPAREN { GetValue $4 }
  | LPAREN; GET_ASSIGNMENT; RPAREN { GetAssignment }
  | LPAREN; GET_MODEL; RPAREN { GetModel }
  | LPAREN; GET_PROOF; RPAREN { GetProof }
  | LPAREN; GET_UNSAT_CORE; RPAREN { GetUnsatCore }
  | LPAREN; GET_UNSAT_ASSUMPTIONS; RPAREN { GetUnsatAssumptions }

// opt:
//   | COLON; DIAGNOSTIC_OUTPUT_CHANNEL; STRING { DiagnosticOutputChannel $3 }
//   | COLON; GLOBAL_DECLARATIONS; b_value { GlobalDeclarations $3 }
//   | COLON; INTERACTIVE_MODE; b_value { InteractiveMode $3 }
//   | COLON; PRINT_SUCCESS; b_value { PrintSuccess $3 }
//   | COLON; PRODUCE_ASSERTIONS; b_value { ProduceAssertions $3 }
//   | COLON; PRODUCE_ASSIGNMENTS; b_value { ProduceAssignments $3 }
//   | COLON; PRODUCE_MODELS; b_value { ProduceModels $3 }
//   | COLON; PRODUCE_PROOFS; b_value { ProduceProofs $3 }
//   | COLON; PRODUCE_UNSAT_ASSUMPTIONS; b_value { ProduceUnsatAssumptions $3 }
//   | COLON; PRODUCE_UNSAT_CORES; b_value { ProduceUnsatCores $3 }
//   | COLON; RANDOM_SEED; NUMERAL { RandomSeed $3 }
//   | COLON; REGULAR_OUTPUT_CHANNEL; STRING { RegularOutputChannel $3 }
//   | COLON; REPRODUCIBLE_RESOURCE_LIMIT; NUMERAL { ReproducibleResourceLimit $3 }
//   | COLON; VERBOSITY; NUMERAL { Verbosity $3 }
//   | attr { Attribute $1 }

// %type <term> term
// %type <binder> binder
// %type <attr> attr
// %type <opt> opt
// %type <eo_var> eo_var
// %type <eq_var> eq_var
// %type <term * term> term_pair
// %type <lit_category> lit_category
// %type <base_command> base_command
// %type <datatype_decl> datatype_decl
// %type <cons_decl> cons_decl
// %type <var_decl> var_decl
// %type <sort_decl> sort_decl
// %type <eo_command> eo_command
// %type <rule_attr> rule_attr
// %type <assumption> assumption
// %type <premises> premises
// %type <simple_prems> simple_premises
// %type <arguments> arguments
// %type <reqs> reqs
// %type <term> conclusion
// %type <control_command> control_command
// %type <proof_command> proof_command
