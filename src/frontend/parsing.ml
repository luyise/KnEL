open Parse
open Ast
open PriorityManager
open Lexing

module SSet = Set.Make(String)

let rec new_name dir name =
  if String.length name > 3 && name.[0] = '.' && name.[1] = '.' && name.[2] = '/' && dir <> "."
  then new_name (Filename.dirname dir) (String.sub name 3 ((String.length name) - 3))
  else dir^"/"^name^".knl"

let cstSet = List.fold_left (fun s (id, _) -> SSet.add id s) SSet.empty Constants.constants

let report filename (b, e) =
  let l = b.pos_lnum in
  let cb = b.pos_cnum - b.pos_bol + 1 in
  let ce = e.pos_cnum - b.pos_bol + 1 in
  Format.eprintf "File \"%s\", line %d, characters %d-%d:\n" filename l cb ce

let edit_open fdir = function
  | OpenSection (fname, as_name, el) ->
    OpenSection (Filename.dirname fdir^"/" ^ fname ^".knl", as_name, el)
  | s -> s


let get_file_ast fdir_name =
  let fdesc = open_in fdir_name in
  let lexbuf = Lexing.from_channel fdesc in
  if !Config.html_view
  then Printf.printf "<font style=\"color:#3498DB\">parsing %s ...\n</font><br>" fdir_name
  else Printf.printf "\x1B[38;5;39mparsing %s ...\n\x1B[39m" fdir_name;
  try
    let (pc, file) = Parser.file Lexer.next_token lexbuf in
    close_in fdesc;
    List.map (fun (id, e) -> (id, expr_of_parsed_expr cstSet prioDefault e)) pc,
    pc,
    (List.map (edit_open fdir_name) file)
  with
    Parser.Error ->
      report fdir_name (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf);
      print_endline "syntax error.";
      exit 1 
