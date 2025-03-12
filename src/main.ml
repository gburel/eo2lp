open Ast
open Ast_cc
open Sys
open Filename
open Translation
open Encoding

let debug_encode = ref false

let string_of_strset str =
    StrSet.fold (fun str acc -> Printf.sprintf "%s, %s" str acc) str ""
let string_of_strmap = StrMap.iter
  (fun str x -> Printf.printf "%s ~~> {%s}\n" str (string_of_strset x))

let show (str : string) : string =
  match StrMap.find_opt str (tdata.context) with
  | Some param -> Printf.sprintf "%s" (string_of_param [] param)
  | None -> Printf.sprintf "Symbol %s not found in context." str

let eo_files = [
  "cpc-less/CompOp.eo";
  "cpc-less/programs/Utils-less.eo";
  "cpc-less/programs/Nary-less.eo";
  "cpc-less/theories/Builtin.eo";
  "cpc-less/rules/Builtin.eo";
  "cpc-less/rules/Booleans-less.eo";
  "cpc-less/rules/Rewrites-less.eo";
  "cpc-less/rules/Uf.eo";
  (* "cpc-less/rules/Uf.eo"; *)
  (* "cpc-less/rules/Arith.eo"; *)
]

let proof_files = [
  (* "test/rodin/smt1468783596909311386.smt2.prf"; *)
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
let write_line ch str =
  if str = "" then () else
  output_string ch str; output_char ch '\n'

let write_lp_cmd ch cmd = write_line ch (string_of_lp_cmd cmd)

let thyU_imports =
  [
    "require open Logic.U.Set Logic.U.Prop;";
    "require open Logic.U.Arrow Logic.U.DepArrow;";
  ]

let lp_imports (fp : string) : string =
  let rec trcl str : StrSet.t =
    match StrMap.find_opt str (tdata.deps) with
    | Some ips ->
        StrSet.fold (fun str x ->
          StrSet.add str (StrSet.union (trcl str) x)
        ) ips (StrSet.empty)
    | None -> StrSet.empty
  in
  let eo_trcl = StrSet.map (fun str -> "eo2lp." ^ str) (trcl fp) in
  if StrSet.is_empty eo_trcl then ""
  else
    let import_str = String.concat " " (StrSet.to_list eo_trcl) in
    Printf.sprintf "require open %s;" import_str

let rec create_parent_dir fn =
  let parent_dir = Filename.dirname fn in
  if not (Sys.file_exists parent_dir) then begin
    create_parent_dir parent_dir;
    Sys.mkdir parent_dir 0o755
  end

let write_lp_file (eo_fp : string) (cmds : lp_cmd list) : unit =
    let import_str = lp_imports (normalize_path eo_fp "") in
    let lp_fp = Filename.concat "lp" (Filename.chop_extension eo_fp) ^ ".lp" in
    Printf.printf "Begin writing file: %s\n" lp_fp;
    let ch = create_parent_dir lp_fp; open_out lp_fp in
    begin
      write_line ch (Printf.sprintf "// Begin translation of: %s" eo_fp);
      List.iter (write_line ch) thyU_imports;
      if basename lp_fp <> "CompOp.lp" then
        write_line ch "require open eo2lp.CompOp;";
      write_line ch import_str; output_char ch '\n';
      List.iter (write_lp_cmd ch) cmds;
      Printf.printf "Done!\n\n";
      output_char ch '\n';
      close_out ch;
    end

let proc_eo_file (fp : string) =
  begin
    let idx = String.index fp '/' in
    let eo_fp = String.sub fp (idx + 1) (String.length fp - idx - 1) in
    tdata.filepath <- eo_fp;

    let t = Sys.time () in
    Printf.printf "Parsing file %s... " fp;
    let eo_cmds = parse_file fp in
    let t' = Sys.time () in
    Printf.printf "%fms\n" (Float.mul (Float.sub t' t) 1000.0);

    let t = Sys.time () in
    Printf.printf "Translating %d commands... " (List.length eo_cmds);
    let cc_cmds = List.concat_map eo_cc eo_cmds in
    let t' = Sys.time () in
    Printf.printf "%fms\n" (Float.mul (Float.sub t' t) 1000.0);

    let t = Sys.time () in
    Printf.printf "Encoding %d commands... " (List.length cc_cmds);
    let lp_cmds = List.map cc_lp cc_cmds in
    let t' = Sys.time () in
    Printf.printf "%fms\n" (Float.mul (Float.sub t' t) 1000.0);

    write_lp_file eo_fp lp_cmds;
  end

let main : unit =
  begin
    let t = Sys.time () in
    init_tdata;
    List.iter (proc_eo_file) eo_files;
    let t' = Sys.time () in
    Printf.printf "Total processing time: %fms\n" (Float.mul (Float.sub t' t) 1000.0);
  end
(* let lp_builtin = List.concat_map (translate_toplevel thy_init) cpc_builtin
let lp_builtin_str = List.map (show_lp_command) lp_builtin  *)
(* Debugging: Print the results *)
(* let () =
  List.iter (fun (file, commands) ->
    Printf.printf "File: %s, Commands: %d\n" file (List.length commands)
  ) cpc_lib *)
