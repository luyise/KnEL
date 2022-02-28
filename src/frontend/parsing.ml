
let files_to_parse : string list ref = ref []

module SSet = Set.Make(String)

let parsed_files = ref SSet.empty

let rec new_name dir name =
  if String.length name > 3 && name.[0] = '.' && name.[1] = '.' && name.[2] = '/' && dir <> "."
  then new_name (Filename.dirname dir) (String.sub name 3 ((String.length name) - 3))
  else dir^"/"^name^".knl"

let parse_file fname lexbuf =
  if not (SSet.mem fname !parsed_files)
  then begin
    Printf.eprintf "parsing %s ...\n" fname;
    parsed_files := SSet.add fname !parsed_files;
    let (deps, ast) = Parser.file Lexer.next_token lexbuf in
    let deps2 = List.map (fun (e, as_name) -> new_name (Filename.dirname fname) e, as_name) deps in
    files_to_parse := List.fold_left (fun l (e, _) -> e :: l) !files_to_parse deps2;
    Knel_modules.add_file fname (ast, deps2)
  end
