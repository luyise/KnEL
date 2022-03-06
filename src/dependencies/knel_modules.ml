open Parse
open Ast
open KnelState

exception DependenciesError
exception WasAlreadyCompiledButShouldNot

module SMap = Map.Make(String)

let build_module_map : knel_state SMap.t ref = ref SMap.empty
(*
type file_status =
  | ToDoStatus of knel_file
  | DoneStatus of KnelState.knel_state

let build_module_map : (file_status * (string * string) list) SMap.t ref = ref SMap.empty

let add_file (fname_str : string) (file, deps) =
  build_module_map := SMap.add fname_str (ToDoStatus file, deps) !build_module_map

let topological_sort_of_files_inner (smap: string list SMap.t) : string list =
  let g = Graph.mk_graph () in
  let () = SMap.iter (fun k _ -> Graph.add_node g k) smap in
  let () = SMap.iter (fun k l -> List.iter (fun j -> Graph.add_edge g j k) l) smap in
  Graph.topological g

let context_of_file fname as_name =
  let (file_status, _) = SMap.find fname !build_module_map in
  match file_status with
    | ToDoStatus _ -> assert false
    | DoneStatus state ->
      [],
      List.map (fun (name, c) -> (if as_name = "" then name else (as_name ^ "." ^name)), c) state.global_context,
      Tactic.map_tac_ctxt (fun name -> if as_name = "" then name else (as_name ^ "." ^ name)) state.tactic_ctxt

let rec ctxt_of_knel_file = function
    | [] -> [], []
    | HypothesisSection ctxt::tl ->
        let (defs, ctxt_tl) = ctxt_of_knel_file tl in
          (defs, ctxt @ ctxt_tl)
    | ReasoningSection (_, None, _, _, _)::tl -> ctxt_of_knel_file tl
    | ReasoningSection (_, Some name, statement, _, _)::tl ->
      let (defs, ctxt_tl) = ctxt_of_knel_file tl in
        (defs, (name, statement) :: ctxt_tl)
    | DefinitionSection (i, e1, e2)::tl ->
      let (defs_tl, ctxt) = ctxt_of_knel_file tl in
        ((i, e1, e2) :: defs_tl, ctxt)
    | _::tl -> ctxt_of_knel_file tl

let update_tree f data =
  let deps = SMap.find f !build_module_map in
  build_module_map := SMap.add f (data, snd deps) !build_module_map

(* let compile_file ?(show=false) f =
  let (content, deps) = SMap.find f !build_module_map
  in match content with
    | ToDoStatus knl_file ->
      let (defs, ctxt, tac_env) =
        List.fold_right
          (fun (dep, as_name) (defs_l, ctxt_l, tac_l) -> 
            let (defs, ctxt, tac) = context_of_file dep as_name in
              (defs @ defs_l, ctxt @ ctxt_l, Tactic.tac_ctxt_merge tac tac_l))
          deps
          ([], [], Tactic.base_tactic_ctxt)
      in
      let () = Format.printf "\x1B[38;5;39mcompiling %s ...\n\x1B[39m" f in
(*      let (tac_env, knl_file) = Tactic.unraw_file tac_env knl_file in*)
      let knl_state = KnelState.new_knel_state (List.rev ctxt) (List.rev defs) [] tac_env show in
      let out_state = FileProceeding.execute_section_list knl_state knl_file in
      let () = FileProceeding.print_error_op out_state in
      update_tree f (DoneStatus out_state)
    | DoneStatus _ -> assert false 
  

let rec compile_list_of_files = function
  | [] -> ()
  | hd::tl ->
    let () = compile_file hd in
    compile_list_of_files tl

let main_file fname_str =
  let deps_map = SMap.map (fun (_, d) -> List.map fst d) (SMap.filter (fun x _ -> x <> fname_str) !build_module_map) in
  let file_list = topological_sort_of_files_inner deps_map in
  List.iter compile_file file_list;
  compile_file ~show:true fname_str *)
*)
let file_handler = ref None 

let main_file proceeding fname =
  let ast = Parsing.get_file_ast fname in
  let knl_state = KnelState.new_knel_state [] [] [] Tactic.base_tactic_ctxt false in
  let () = file_handler := Some proceeding in
  build_module_map := SMap.add fname (proceeding knl_state ast) !build_module_map

let get_content state fdir as_name args =
  assert (args = []);
  let out_state =
    if SMap.mem fdir !build_module_map
    then
      SMap.find fdir !build_module_map
    else
      let ast = Parsing.get_file_ast fdir in
      let knl_state = KnelState.new_knel_state [] [] [] Tactic.base_tactic_ctxt false in
      match !file_handler with
        | Some f -> f knl_state ast
        | None -> assert false
  in
  let () = build_module_map := SMap.add fdir out_state !build_module_map in
  match out_state.status with
    | AllDone ->
      { state with
        global_context = state.global_context @ out_state.global_context
      ; used_ident = out_state.used_ident @ state.used_ident
      ; tactic_ctxt = Tactic.tac_ctxt_merge out_state.tactic_ctxt state.tactic_ctxt
      ; beta_rules = out_state.beta_rules @ state.beta_rules
      ; definitions = out_state.definitions @ state.definitions
      ; environments = out_state.environments @ state.environments
      }
    | _ -> { state with status = Error "Open file failed" }
