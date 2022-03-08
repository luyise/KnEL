open Parse
open Ast
open KnelState

exception DependenciesError
exception WasAlreadyCompiledButShouldNot

module SMap = Map.Make(String)
module SSet = Set.Make(String)

let build_module_map : (context * knel_state) SMap.t ref = ref SMap.empty
let opened_files : string list ref = ref []
let file_handler = ref None 


let main_file proceeding print_error_op fname =
  let s = !opened_files in
  let () = opened_files := fname :: s in
  let (demanded_ctxt, variables, ast) = Parsing.get_file_ast fname in
  let knl_state = KnelState.new_knel_state [] [] [] Tactic.base_tactic_ctxt true in
  let () = file_handler := Some proceeding in
  let out_state = proceeding knl_state (HypothesisSection variables :: ast) in
  let () = opened_files := s in
  let () = print_error_op out_state in
  build_module_map := SMap.add fname (demanded_ctxt, out_state) !build_module_map

let rec rename_in_expr ?(set=SSet.empty) rename expr =
  let desc = match expr.desc with
    | EVar n when SSet.mem n set -> EVar n
    | EVar i -> EVar (rename i)
    | EConst i -> EConst i
    | EApp (e1, e2) ->
      EApp (rename_in_expr ~set rename e1, rename_in_expr ~set rename e2)
    | EPair ((e1, e2), None) ->
      EPair ((rename_in_expr ~set rename e1, rename_in_expr ~set rename e2), None)
    | EPair ((e1, e2), Some e3) ->
      EPair ((rename_in_expr ~set rename e1, rename_in_expr ~set rename e2), Some (rename_in_expr ~set rename e3))
    | ELam ((id, e1), e2, path) ->
      ELam ((id, rename_in_expr ~set rename e1), rename_in_expr ~set:(SSet.add id set) rename e2, path)
    | EPi ((id, e1), e2, path) ->
      EPi ((id, rename_in_expr ~set rename e1), rename_in_expr ~set:(SSet.add id set) rename e2, path)
    | ESigma ((id, e1), e2, path) ->
      ESigma ((id, rename_in_expr ~set rename e1), rename_in_expr ~set:(SSet.add id set) rename e2, path)
    | EFst e -> EFst (rename_in_expr ~set rename e)
    | ESnd e -> ESnd (rename_in_expr ~set rename e)
    in {expr with desc }

let get_content state fdir as_name args =
  let s = !opened_files in
  if List.mem fdir s then begin
    let rec path_loop_printer = function
      | f1::f2::tl ->
        Format.printf "%s required by %s\n" f1 f2;
        if tl <> []
          then path_loop_printer (f2::tl)
      | _ -> assert false
    in Format.printf "Dependancy loop found\n";
    path_loop_printer (fdir::s);
    { state with status = Error "Open file failed" }
  end else begin
    let () = opened_files := fdir :: s in
    assert (args = []);
    let (var, out_state) =
      if SMap.mem fdir !build_module_map
      then
        SMap.find fdir !build_module_map
      else
        let (demanded_ctxt, variables, ast) = Parsing.get_file_ast fdir in
        let knl_state = KnelState.new_knel_state [] [] [] Tactic.base_tactic_ctxt false in
        let outState = match !file_handler with
          | Some f -> f knl_state (HypothesisSection variables :: ast)
          | None -> assert false in
        let () = build_module_map := SMap.add fdir (demanded_ctxt, outState) !build_module_map
        in (demanded_ctxt, outState)
    in
    let () = opened_files := s in
    let rename = if as_name = "" then (fun x -> x) else (fun x -> as_name ^ "." ^ x) in
    match out_state.status with
      | AllDone ->
        { state with
          global_context = (List.map (fun (i, e) -> (rename i, rename_in_expr rename e)) out_state.global_context) @ state.global_context
        ; used_ident = (List.map rename out_state.used_ident) @ state.used_ident
        ; tactic_ctxt = Tactic.tac_ctxt_merge (Tactic.map_tac_ctxt rename out_state.tactic_ctxt) state.tactic_ctxt
        ; beta_rules = out_state.beta_rules @ state.beta_rules
        ; definitions = (List.map (fun (i, e) -> (rename i, rename_in_expr rename e)) out_state.definitions) @ state.definitions
        ; environments = out_state.environments @ state.environments
        }
      | _ -> { state with status = Error "Open file failed" }
  end
