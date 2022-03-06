open Parse
open Lexing

let report filename (b, e) =
  let l = b.pos_lnum in
  let cb = b.pos_cnum - b.pos_bol + 1 in
  let ce = e.pos_cnum - b.pos_bol + 1 in
  Format.eprintf "File \"%s\", line %d, characters %d-%d:\n" filename l cb ce

let set_file f = Parsing.files_to_parse := f :: !Parsing.files_to_parse

let () = Config.parse_arguments set_file

(* Style de l'affichage html *)
let _ = if !Config.html_view then begin
  Format.printf "<html>";
  Format.printf "<body style=\"font-family:Ubuntu Mono; FreeSans;\">"
end;;

let () = if !Config.shutdown then exit 0

let check_file_name filename =
  if not (Filename.check_suffix filename ".knl")
    then raise (Arg.Bad ("file \""^filename^"\" is not a .knl file"))

let main () =
  List.iter check_file_name !Parsing.files_to_parse;
  List.iter (Knel_modules.main_file FileProceeding.execute_section_list FileProceeding.print_error_op) !Parsing.files_to_parse
 
let () = main ()

(* gestion du style html *)
let _ = if !Config.html_view then begin
  Format.printf "</body>";
  Format.printf"</html>"
end;;
