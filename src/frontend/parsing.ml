open Parse
open Ast
open Tactic

let files_to_parse : string list ref = ref []

module SSet = Set.Make(String)

let parsed_files = ref SSet.empty

let rec new_name dir name =
  if String.length name > 3 && name.[0] = '.' && name.[1] = '.' && name.[2] = '/' && dir <> "."
  then new_name (Filename.dirname dir) (String.sub name 3 ((String.length name) - 3))
  else dir^"/"^name^".knl"

let cstSet = List.fold_left (fun s (id, _) -> SSet.add id s) SSet.empty Constants.constants

let fopt f = function
  | None -> None
  | Some e -> Some (f e)

let check_if_allowed ~loc id = if SSet.mem id cstSet then assert false else id

let rec changeVarToCst expr =
  let desc = match expr.desc with
  | EVar n when SSet.mem n cstSet -> EConst n
  | EPi ((id, _), _) | ESigma ((id, _), _) | ELam ((id, _), _)
    when SSet.mem id cstSet -> assert false
  | EPi ((id, e1), e2) -> EPi ((id, changeVarToCst e1), changeVarToCst e2)
  | ELam ((id, e1), e2) -> ELam ((id, changeVarToCst e1), changeVarToCst e2)
  | ESigma ((id, e1), e2) -> ESigma ((id, changeVarToCst e1), changeVarToCst e2)
  | EPair ((e1, e2), e3) -> EPair ((changeVarToCst e1, changeVarToCst e2), fopt changeVarToCst e3)
  | EFst e -> EFst (changeVarToCst e)
  | ESnd e -> ESnd (changeVarToCst e)
  | EApp (e1, e2) -> EApp (changeVarToCst e1, changeVarToCst e2)
  | EVar _ | EConst _ -> expr.desc
  in { desc; loc = expr.loc }

let changeVarToCstFileSection = function
  | RawHypothesisSection l ->
    RawHypothesisSection (List.map (fun (n, e) -> (check_if_allowed ~loc:e.loc n, changeVarToCst e)) l)
  | RawDefinitionSection (id, e1, e2) ->
    RawDefinitionSection (check_if_allowed ~loc:e1.loc id, changeVarToCst e1, changeVarToCst e2)
  | RawReasoningSection (bt, idop, e, el, et) ->
    RawReasoningSection 
      (bt,
       fopt (check_if_allowed ~loc:e.loc) idop,
       changeVarToCst e,
       List.map changeVarToCst el,
       et)
  | RawTacticDeclSection (id, expr) -> 
    RawTacticDeclSection (check_if_allowed ~loc:expr.loc id, changeVarToCst expr)

let changeVarToCstFile = List.map changeVarToCstFileSection

let parse_file fname lexbuf =
  if not (SSet.mem fname !parsed_files)
  then begin
    Printf.eprintf "parsing %s ...\n" fname;
    parsed_files := SSet.add fname !parsed_files;
    let (deps, ast) = Parser.file Lexer.next_token lexbuf in
    let deps2 = List.map (fun (e, as_name) -> new_name (Filename.dirname fname) e, as_name) deps in
    files_to_parse := List.fold_left (fun l (e, _) -> e :: l) !files_to_parse deps2;
    Knel_modules.add_file fname (changeVarToCstFile ast, deps2)
  end
