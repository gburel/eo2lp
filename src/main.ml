open Ast
open Ast_cc
open Sys
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



let find_eo_files (dir : string) : string list =
  let rec aux (dir : string) (acc : string list) =
    Array.fold_left (fun acc entry ->
      let path = Filename.concat dir entry in
      if is_directory path then
        aux path acc
      else if Filename.check_suffix entry ".eo" then
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

let thyU_imports = [
    "Logic.U.Set";
    "Logic.U.Prop";
    "Logic.U.Arrow";
    "Logic.U.DepArrow";
  ]

let lp_imports (fp : string) : string list =
  let fp_norm = normalize_path fp "" in
  let rec trcl str : StrSet.t =
    match StrMap.find_opt str (tdata.deps) with
    | Some ips ->
        StrSet.fold (fun str x ->
          StrSet.add str (StrSet.union (trcl str) x)
        ) ips (StrSet.empty)
    | None -> StrSet.empty
  in
    StrSet.to_list (StrSet.map (fun str -> "eo2lp." ^ str) (trcl fp_norm))

(* let proof_imports : string list = failwith "undefined" *)


let rec create_parent_dir fn =
  let parent_dir = Filename.dirname fn in
  if not (Sys.file_exists parent_dir) then begin
    create_parent_dir parent_dir;
    Sys.mkdir parent_dir 0o755
  end

let write_lp_file (fp : string) (imports : string list) (cmds : lp_cmd list) : unit =
    let import_str =
      Printf.sprintf "require open %s;\n\n"
      (String.concat " " imports)
    in

    let lp_fp = Filename.concat "lp" (Filename.chop_extension fp) ^ ".lp" in
    let ch = create_parent_dir lp_fp; open_out lp_fp in
    begin
      Printf.printf "Begin writing file: %s\n" lp_fp;
      write_line ch (Printf.sprintf "// Begin translation of: %s" fp);
      write_line ch import_str;
      List.iter (write_lp_cmd ch) cmds;
      output_char ch '\n';
      close_out ch;
      Printf.printf "Done!\n\n";
    end

let proc_eo_file (fp : string) =
  begin
    let t = Sys.time () in
    Printf.printf "Parsing file %s... " fp;
    let eo_cmds = parse_file fp in
    let t' = Sys.time () in
    Printf.printf "%fms\n" (Float.mul (Float.sub t' t) 1000.0);

    let idx = String.index fp '/' in
    let fp' = String.sub fp (idx + 1) (String.length fp - idx - 1) in
    tdata.filepath <- fp';

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

    let imports = (thyU_imports @ lp_imports fp') in
    write_lp_file fp' imports lp_cmds;
  end

let eo_lib_paths = [
    "CompOp.eo";
    "programs/Utils-less.eo";
    "programs/Nary-less.eo";
    "theories/Builtin.eo";
    "rules/Builtin.eo";
    "rules/Booleans-less.eo";
    "rules/Rewrites-less.eo";
    "rules/Uf.eo";
    (* "cpc-less/rules/Uf.eo"; *)
    (* "cpc-less/rules/Arith.eo"; *)
  ]

let proc_eo_library (dir : string) : unit =
  begin
    Printf.printf "Begin translating Eunoia library.";
    let t = Sys.time () in
    List.iter (fun fp -> proc_eo_file (Filename.concat dir fp)) eo_lib_paths;
    let t' = Sys.time () in
    Printf.printf "Total processing time: %fms\n" (Float.mul (Float.sub t' t) 1000.0);
  end

let prf_paths = [
    "rodin/smt1468783596909311386.smt2.prf";
  ]

let proc_eo_proofs (dir : string) : unit =
  List.iter (fun fp ->
    tdata.deps <- StrMap.update
      (normalize_path fp "")
      (fun _ -> Some (StrSet.of_list (List.map (fun fp -> normalize_path fp "") eo_lib_paths)))
      tdata.deps
  ) prf_paths;
  List.iter proc_eo_file
    (List.map (Filename.concat dir) prf_paths)

let main : unit =
  begin
    proc_eo_library "cpc-less";
    proc_eo_proofs "test";
  end





(* let lp_builtin = List.concat_map (translate_toplevel thy_init) cpc_builtin
let lp_builtin_str = List.map (show_lp_command) lp_builtin  *)
(* Debugging: Print the results *)
(* let () =
  List.iter (fun (file, commands) ->
    Printf.printf "File: %s, Commands: %d\n" file (List.length commands)
  ) cpc_lib *)
