open Parse
open Ast

exception DependenciesError
exception WasAlreadyCompiledButShouldNot

module SMap = Map.Make(String)

type file_status =
  | ToDoStatus of Tactic.raw_knel_file
  | DoneStatus of ((ident * expr * expr) list * context * Tactic.tactic_ctxt)

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
    | DoneStatus (_, ctxt, tactics) ->
      [],
      List.map (fun (name, c) -> (if as_name = "" then name else (as_name ^ "." ^name)), c) ctxt,
      Tactic.map_tac_ctxt (fun name -> if as_name = "" then name else (as_name ^ "." ^ name)) tactics

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

let update_tree f data =
  let deps = SMap.find f !build_module_map in
  build_module_map := SMap.add f (data, snd deps) !build_module_map

let compile_file ?(show=false) f =
  let (content, deps) = SMap.find f !build_module_map
  in match content with
    | ToDoStatus cnt ->
      let (defs, ctxt, tac_env) =
        List.fold_right
          (fun (dep, as_name) (defs_l, ctxt_l, tac_l) -> 
            let (defs, ctxt, tac) = context_of_file dep as_name in
              (defs @ defs_l, ctxt @ ctxt_l, Tactic.tac_ctxt_merge tac tac_l))
          deps
          ([], [], Tactic.base_tactic_ctxt)
      in
      let () = Format.eprintf "compiling %s ...\n" f in
      let (tac_env, knl_file) = Tactic.unraw_file tac_env cnt in
      let knl_state = KnelState.new_knel_state (List.rev ctxt) (List.rev defs) [] show in
      let out_state = FileProceeding.execute_section_list knl_state knl_file in
      let () = FileProceeding.print_error_op out_state in
      let new_defs, new_ctxt = ctxt_of_knel_file knl_file in
      update_tree f (DoneStatus (new_defs, new_ctxt, tac_env))
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
  compile_file ~show:true fname_str
