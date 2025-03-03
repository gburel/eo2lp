open Ast
open Ast_cc
open Sys
open Filename
open Translation
open Encoding

let eo_files = [
  "cpc-less/CompOp.eo";
  "cpc-less/programs/Utils-less.eo";
  "cpc-less/programs/Nary-less.eo";
  "cpc-less/theories/Builtin.eo";
  "cpc-less/rules/Builtin.eo";
  "cpc-less/rules/Booleans-less.eo";
  "cpc-less/rules/Rewrites-less.eo";
  "test/rodin/smt1468783596909311386.smt2.prf";
  (* "cpc-less/rules/Uf.eo"; *)
  (* "cpc-less/rules/Arith.eo"; *)
]

let find_eo_files (dir : string) : string list =
  let rec aux (dir : string) (acc : string list) =
    Array.fold_left (fun acc entry ->
      let path = concat dir entry in
      if is_directory path then
        aux path acc
      else if check_suffix entry ".eo" then
        path :: acc
      else
        acc
    ) acc (readdir dir)
  in
  aux dir []

let parse_cmd (lx : Lexing.lexbuf) : eo_command option =
  try
    Parser.toplevel_eof Lexer.token lx
  with
  | Parser.Error ->
      let pos = lx.lex_curr_p in
      Printf.printf "Parser error at line %d, column %d: token '%s'\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) (Lexing.lexeme lx);
      None

let parse_file (fp : string) : eo_command list =
  let ch = open_in fp in
  let lx = Lexing.from_channel ch in
  let rec parse_all acc =
    match parse_cmd lx with
    | Some cmd -> parse_all (cmd :: acc)
    | None -> close_in ch; (List.rev acc)
  in
    parse_all []

(*
let parse_directory (dir : string) : eo_library =
  Printf.printf "Parsing directory: %s\n" dir;
  let files = find_eo_files dir in
  Printf.printf "Found %d EO files.\n" (List.length files);
  List.map (fun file -> (file, parse_file file)) files
*)

let lp_imports =
  [
    "require open Logic.U.Set Logic.U.Prop;";
    "require open Logic.U.Arrow Logic.U.DepArrow;";
    "require open eo2lp.Prelude;";
    ""
  ]

let write_line ch str = output_string ch str; output_char ch '\n'
let write_lp_cmd ch cmd = write_line ch (string_of_lp_cmd cmd)

let proc_eo_cmd (ch : out_channel) (cmd : eo_command) =
  begin
    ddata_ref := ddata_init;
    let cs = eo_cc cmd in
    if cs <> [] then
      List.iter (fun cmd ->
        Printf.printf "Encoding command...\n%s\n" (string_of_cmd cmd);
        tdata_ref := { !tdata_ref with signature =
          { !tdata_ref.signature with cmds = cmd :: !tdata_ref.signature.cmds }
        };
        let lp_cmd = cc_lp cmd in
        Printf.printf "Done!\n%s\n\n" (string_of_lp_cmd lp_cmd);
        write_lp_cmd ch lp_cmd;
        (* output_char ch '\n'; *)
      ) (!ddata_ref.match_progs @ cs)
  end

let proc_eo_file (ch : out_channel) (fp : string) =
  begin
    Printf.printf "Parsing file %s... " fp;
    write_line ch (Printf.sprintf "// Begin translation of: %s" fp);
    let eo_cmds = parse_file fp in
    Printf.printf "Done!\n";
    List.iter (proc_eo_cmd ch) eo_cmds;
    output_char ch '\n';
  end

let main : unit =
  begin
    tdata_ref := tdata_init;
    let ch = open_out "lp/out.lp" in
    List.iter (write_line ch) lp_imports;
    List.iter (proc_eo_file ch) eo_files;
    close_out ch;
  end
(* let lp_builtin = List.concat_map (translate_toplevel thy_init) cpc_builtin
let lp_builtin_str = List.map (show_lp_command) lp_builtin  *)
(* Debugging: Print the results *)
(* let () =
  List.iter (fun (file, commands) ->
    Printf.printf "File: %s, Commands: %d\n" file (List.length commands)
  ) cpc_lib *)
