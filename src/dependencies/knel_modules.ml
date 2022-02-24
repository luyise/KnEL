open Ast

exception DependenciesError
exception WasAlreadyCompiledButShouldNot

module SMap = Map.Make(String)

type file_status =
  | ToDoStatus of Tactic.raw_knel_file
  | DoneStatus of context

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
    | DoneStatus ctxt ->
      List.map (fun (name, c) -> (as_name ^ "." ^name, c)) ctxt

let rec ctxt_of_knel_file = function
    | [] -> []
    | HypothesisSection ctxt::tl -> ctxt @ ctxt_of_knel_file tl
    | ReasoningSection (_, None, _, _, _)::tl -> ctxt_of_knel_file tl
    | ReasoningSection (_, Some name, statement, _, _)::tl -> (name, statement)::ctxt_of_knel_file tl

let update_tree f data =
  let deps = SMap.find f !build_module_map in
  build_module_map := SMap.add f (data, snd deps) !build_module_map

let compile_file ?(show=false) f =
  let (content, deps) = SMap.find f !build_module_map
  in match content with
    | ToDoStatus cnt ->
      let ctxt =
        List.fold_left (fun l (dep, as_name) -> List.rev_append (List.rev (context_of_file dep as_name)) l) [] deps
      in
      let () = Format.eprintf "compiling %s ...\n" f in
      let (tac_env, knl_file) = Tactic.unraw_file Tactic.base_tactic_ctxt cnt in
      let () = FileProceeding.execute_file ~show knl_file in
      let new_ctxt = ctxt_of_knel_file knl_file in
      update_tree f (DoneStatus new_ctxt)
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