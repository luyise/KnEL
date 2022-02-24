open Lexing

(* open NomDuFichier : ouvre un nom du fichier, de façon publique *)
(* NomDuFichier.definition_interne : utilise localement la donnée d'un autre fichier *)

let report filename (b, e) =
  let l = b.pos_lnum in
  let cb = b.pos_cnum - b.pos_bol + 1 in
  let ce = e.pos_cnum - b.pos_bol + 1 in
  Format.eprintf "File \"%s\", line %d, characters %d-%d:\n" filename l cb ce

let set_file f = Parsing.files_to_parse := f :: !Parsing.files_to_parse

let () = Config.parse_arguments set_file

let () = if !Config.shutdown then exit 0

let check_file_name filename =
  if not (Filename.check_suffix filename ".knl")
    then raise (Arg.Bad ("file \""^filename^"\" is not a .knl file"))

let main () =
  let main_file =
    match !Parsing.files_to_parse with
      | [] -> exit 0
      | [x] -> x
      | _ -> exit 1 in
  check_file_name main_file;
  while List.length !Parsing.files_to_parse <> 0 do
      match !Parsing.files_to_parse with
        | filename::tl ->
          let () = Parsing.files_to_parse := tl in
          let file_desc = open_in filename in
          let lexbuf = Lexing.from_channel file_desc in
          begin 
            try
              Parsing.parse_file filename lexbuf
            with
              Parser.Error -> begin
                  report filename (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf);
                  print_endline "syntax error."; exit 1
                end
          end
        | [] -> assert false
  done;
  Knel_modules.main_file main_file

(* let _ = FileProceeding.execute_file Code_random.myFile *)
 
let () = main ()
