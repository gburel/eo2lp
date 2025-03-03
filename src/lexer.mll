{
open Parser
}

let simple_symbol = ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '^' '=' '%' '?' '!' '.' '$' '_' '&' '<' '>' '@' '#']
  ['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '^' '=' '%' '?' '!' '.' '$' '_' '&' '<' '>' '@' ':']*
let symbol = simple_symbol | '|' [^ '|' '\\']* '|'
let numeral = ['0'-'9']+
let decimal = numeral '.' numeral
let rational = numeral '/' numeral
let binary = "#b" ['0'-'1']+
let hexadecimal = "#x" ['0'-'9' 'a'-'f' 'A'-'F']+
let string = '"' ([^'"'])* '"'

rule token = parse
  | ';' [^'\n']* '\n' { Lexing.new_line lexbuf; token lexbuf }  (* Ignore comments *)
  | ';' [^'\n']* eof  { token lexbuf }   (* Ignore comments at end of file *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | eof             { EOF }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ':'             { COLON }
  | "!"             { BANG }
  | "eo::match"     { EO_MATCH }
  | "eo::define"    { EO_DEFINE }
  (* base smt2/smt3 context modifying commands *)
  | "assert"        { ASSERT }
  | "declare-type"  { DECLARE_TYPE }
  | "define-type"   { DEFINE_TYPE }
  | "declare-const" { DECLARE_CONST }
  | "declare-fun"   { DECLARE_FUN }
  | "declare-sort"  { DECLARE_SORT }
  | "define-fun"    { DEFINE_FUN }
  | "define-funs-rec" { DEFINE_FUNS_REC }
  | "define-const"  { DEFINE_CONST }
  | "define-sort"   { DEFINE_SORT }
  | "declare-datatype"  { DECLARE_DATATYPE }
  | "declare-datatypes" { DECLARE_DATATYPES }
  (* base smt2/smt3 control commands *)
  | "check-sat"          { CHECK_SAT }
  | "check-sat-assuming" { CHECK_SAT_ASSUMING }
  | "get-value"          { GET_VALUE }
  | "get-assignment"     { GET_ASSIGNMENT}
  | "get-unsat-assumptions" { GET_UNSAT_ASSUMPTIONS }
  | "get-unsat-core"     { GET_UNSAT_CORE }
  | "get-proof"          { GET_PROOF }
  | "get-model"          { GET_MODEL }
  | "set-info"           { SET_INFO }
  | "set-logic"          { SET_LOGIC }
  | "set-option"         { SET_OPTION }
  | "get-option"         { GET_OPTION }
  | "push"               { PUSH }
  | "pop"                { POP }
  | "echo"               { ECHO }
  | "exit"               { EXIT }
  | "reset"              { RESET }
  (* eunoia context modifying commands *)
  | "declare-rule"             { DECLARE_RULE }
  | "declare-consts"           { DECLARE_CONSTS }
  | "declare-parameterized-const" { DECLARE_PARAMETERIZED_CONST }
  | "declare-oracle-fun"       { DECLARE_ORACLE_FUN }
  | "define"                  { DEFINE }
  | "include"        { INCLUDE }
  | "program"        { PROGRAM }
  | "program-schema" { PROGRAM_SCHEMA }
  | "reference"      { REFERENCE }
  (* eunoia proof script commands *)
  | "assume"         { ASSUME }
  | "assume-push"    { ASSUME_PUSH }
  | "step"           { STEP }
  | "step-pop"       { STEP_POP }
  (* rule declaration *)
  | ":conclusion"    { CONCLUSION }
  | ":assumption"    { ASSUMPTION }
  | ":premise-list"  { PREMISE_LIST }
  | ":premises"      { PREMISES }
  | ":args"          { ARGS }
  | ":requires"      { REQUIRES }
  | ":rule"          { RULE }
  (* syntactic categories *)
  | "<string>"       { STR }
  | "<numeral>"      { NUM }
  | "<decimal>"      { DEC }
  | "<rational>"     { RAT }
  | "<binary>"       { BIN }
  | "<hexadecimal>"  { HEX }
  (* syntactic literals *)
  | symbol as s      { SYMBOL s }
  | string as s      { STRING s }
  | numeral as x     { NUMERAL (int_of_string x) }
  | decimal as x     { DECIMAL (float_of_string x) }
  | rational as x    { RATIONAL
        (let [y;z] = String.split_on_char '/' x in
            (int_of_string y, int_of_string z)) }
  (*
  | binary as x      { BINARY x }
  | hexadecimal as x { HEXADECIMAL x }
  *)
  | _ { token lexbuf }
