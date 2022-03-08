open Parse
open Ast
open PriorityManager
open Tactic
(*
let files_to_parse : string list ref = ref []
*)
module SSet = Set.Make(String)
(*
let parsed_files = ref SSet.empty
*)
let rec new_name dir name =
  if String.length name > 3 && name.[0] = '.' && name.[1] = '.' && name.[2] = '/' && dir <> "."
  then new_name (Filename.dirname dir) (String.sub name 3 ((String.length name) - 3))
  else dir^"/"^name^".knl"

let cstSet = List.fold_left (fun s (id, _) -> SSet.add id s) SSet.empty Constants.constants
(*
let fopt f = function
  | None -> None
  | Some e -> Some (f e)

let rec changeVarToCst expr =
  let desc = match expr.desc with
  | EVar n when SSet.mem n cstSet -> EConst n
  | EPi ((id, _), _, _) | ESigma ((id, _), _, _) | ELam ((id, _), _, _)
    when SSet.mem id cstSet -> assert false
  | EPi ((id, e1), e2, p) -> EPi ((id, changeVarToCst e1), changeVarToCst e2, p)
  | ELam ((id, e1), e2, p) -> ELam ((id, changeVarToCst e1), changeVarToCst e2, p)
  | ESigma ((id, e1), e2, p) -> ESigma ((id, changeVarToCst e1), changeVarToCst e2, p)
  | EPair ((e1, e2), e3) -> EPair ((changeVarToCst e1, changeVarToCst e2), fopt changeVarToCst e3)
  | EFst e -> EFst (changeVarToCst e)
  | ESnd e -> ESnd (changeVarToCst e)
  | EApp (e1, e2) -> EApp (changeVarToCst e1, changeVarToCst e2)
  | EVar _ | EConst _ -> expr.desc
  in { desc; loc = expr.loc }

let changeVarToCstFileSection fdir = function
  | HypothesisSection l ->
    HypothesisSection (List.map (fun (n, e) -> (check_if_allowed ~loc:e.loc n, changeVarToCst e)) l)
  | DefinitionSection (id, e1, e2) ->
    DefinitionSection (check_if_allowed ~loc:e1.loc id, changeVarToCst e1, changeVarToCst e2)
  | ReasoningSection (bt, idop, e, el, et) ->
    ReasoningSection 
      (bt,
       fopt (check_if_allowed ~loc:e.loc) idop,
       changeVarToCst e,
       List.map changeVarToCst el,
       et)
  | TacDeclSection (id, expr) -> 
    TacDeclSection (check_if_allowed ~loc:expr.loc id, changeVarToCst expr)
  | BetaRuleDeclSection brt -> BetaRuleDeclSection brt
  | OpenSection (fname, as_name, el) ->
    OpenSection (Filename.dirname fdir^"/" ^ fname ^".knl", as_name, List.map changeVarToCst el)

let changeVarToCstFile fdir = List.map (changeVarToCstFileSection fdir)
*)

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
  let (pc, file) = Parser.file Lexer.next_token lexbuf in
  close_in fdesc;
  List.map (fun (id, e) -> (id, expr_of_parsed_expr cstSet prioDefault e)) pc,
  pc,
  (List.map (edit_open fdir_name) file)
