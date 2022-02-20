open Lexing
open FileProceeding

(* open NomDuFichier : ouvre un nom du fichier, de façon publique *)
(* NomDuFichier.definition_interne : utilise localement la donnée d'un autre fichier *)

let shutdown = ref false

let options = [
  "--stop", Arg.Set shutdown, "stop the program";
]

let usage = "usage : main.exe file.knl"

let report filename (b, e) =
  let l = b.pos_lnum in
  let cb = b.pos_cnum - b.pos_bol + 1 in
  let ce = e.pos_cnum - b.pos_bol + 1 in
  Format.eprintf "File \"%s\", line %d, characters %d-%d:\n" filename l cb ce

let main filename =
  if !shutdown then exit 0;
  if not (Filename.check_suffix filename ".knl")
    then raise (Arg.Bad "expected .knl extension");
  let file_desc = open_in filename in
  let lexbuf = Lexing.from_channel file_desc in
  try
    let (ctxt, thml) = Parser.file Lexer.next_token lexbuf in
    match thml with
      |[] -> execute_file ctxt None [] (* remplacer par knl_file *)
      |(name, statement, (proof, endkwd))::tl -> execute_file ctxt (Some statement) proof

  with
  Parser.Error ->
    report filename (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf);
    print_endline "syntax error.";
    exit 1


let _ = Arg.parse options main usage