open Ast
open Ast_cc
open Sys
open Filename
open Translation
open Encoding

let string_of_strset str =
    StrSet.fold (fun str acc -> Printf.sprintf "%s, %s" str acc) str ""
let string_of_strmap = StrMap.iter (fun str x -> Printf.printf "%s ~~> {%s}\n" str (string_of_strset x))

let eo_files = [
  "cpc-less/CompOp.eo";
  "cpc-less/programs/Utils-less.eo";
  "cpc-less/programs/Nary-less.eo";
  "cpc-less/theories/Builtin.eo";
  "cpc-less/rules/Builtin.eo";
  (* "cpc-less/rules/Booleans-less.eo";
  "cpc-less/rules/Rewrites-less.eo";
  "cpc-less/rules/Uf.eo"; *)
  (* "test/rodin/smt1468783596909311386.smt2.prf"; *)
  (* "cpc-less/rules/Uf.eo"; *)
  (* "cpc-less/rules/Arith.eo"; *)
]

let show (str : string) : string =
  match lookup_cmd_opt (!tdata_ref.signature) str with
  | Some cmd -> Printf.sprintf "%s" (string_of_cmd cmd)
  | None -> Printf.sprintf "Symbol %s not found in signature" str

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
let write_line ch str = output_string ch str; output_char ch '\n'
let write_lp_cmd ch cmd = write_line ch (string_of_lp_cmd cmd)

let proc_eo_cmd (cmd : eo_command)  =
  begin
    ddata_ref := ddata_init;
    let cs = eo_cc cmd in
    if cs <> [] then
      List.fold_right (fun cmd acc ->
        tdata_ref := { !tdata_ref with signature = cmd :: !tdata_ref.signature };
        Printf.printf "Encoding command...\n%s\n" (string_of_cmd cmd);
        let lp_cmd = cc_lp cmd in
          Printf.printf "Done!\n%s\n\n" (string_of_lp_cmd lp_cmd); (lp_cmd :: acc)
        (* output_char ch '\n'; *)
      ) (!ddata_ref.match_progs @ cs) []
    else []
  end

let generic_imports =
  [
    "require open Logic.U.Set Logic.U.Prop;";
    "require open Logic.U.Arrow Logic.U.DepArrow;";
    "require open eo2lp.Prelude;";
  ]

let lp_imports (fp : string) : string =
  let rec trcl str : StrSet.t =
    match StrMap.find_opt str (!tdata_ref.deps) with
    | Some ips ->
        StrSet.fold (fun str x ->
          StrSet.add str (StrSet.union (trcl str) x)
        ) ips (StrSet.empty)
    | None -> StrSet.empty
  in
  let eo_trcl = StrSet.map (fun str -> "eo2lp." ^ str) (trcl fp) in
  if StrSet.is_empty eo_trcl then
    ""
  else
    let import_str = String.concat " " (StrSet.to_list eo_trcl) in
    Printf.sprintf "require open %s;" import_str

let proc_eo_file (fp : string) =
  begin
    Printf.printf "Parsing file %s... " fp;

    let idx = String.index fp '/' in
    let fp' = String.sub fp
      (idx + 1) (String.length fp - idx - 1)
    in
    tdata_ref := { !tdata_ref with filepath = fp' };
    let eo_cmds = parse_file fp in
    let lp_cmds = List.concat_map proc_eo_cmd eo_cmds in

    let lp_fp = Filename.concat "lp" (Filename.chop_extension fp') ^ ".lp" in
    Printf.printf "%s" lp_fp;
    try Sys.mkdir (Filename.dirname lp_fp) 0o755 with Sys_error _ -> Printf.printf "fail!";
    let ch = open_out lp_fp in

    write_line ch (Printf.sprintf "// Begin translation of: %s" fp);
    List.iter (write_line ch) generic_imports;
    write_line ch (lp_imports (normalize_path fp' ""));
    List.iter (write_lp_cmd ch) lp_cmds;
    Printf.printf "Done!\n";
    output_char ch '\n';
    close_out ch;
  end

let main : unit =
  begin
    tdata_ref := tdata_init;
    List.iter (proc_eo_file) eo_files;
  end
(* let lp_builtin = List.concat_map (translate_toplevel thy_init) cpc_builtin
let lp_builtin_str = List.map (show_lp_command) lp_builtin  *)
(* Debugging: Print the results *)
(* let () =
  List.iter (fun (file, commands) ->
    Printf.printf "File: %s, Commands: %d\n" file (List.length commands)
  ) cpc_lib *)
