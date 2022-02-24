open Ast

exception DependenciesError
exception WasAlreadyCompiledButShouldNot

module SMap = Map.Make(String)
(*
type fname =
  | FN_Above of fname
  | FN_In of string * fname
  | FN_Is of (string * string option)
[@@deriving show]
*)
type file_status =
  | ToDoStatus of Tactic.raw_knel_file
  | DoneStatus of context
(*
type module_tree =
  | MDir of module_tree SMap.t
  | MFile of file_status * fname list

let rec string_of_fname = function
  | FN_Above f    -> "../"^string_of_fname f
  | FN_In (s, f)  -> s ^"/"^string_of_fname f
  | FN_Is (s, _)  -> s

let fname_of_string s =
  let l = String.split_on_char '/' s in
  let rec build_fname = function
    | [] -> assert false
    | [basename] ->
      let (p1, p2) = match String.split_on_char ' ' basename with
        | [s] -> s, None
        | [s1; s2] -> s1, Some s2
        | _ -> assert false
      in FN_Is (p1, p2)
    | hd::tl when hd = ".." ->
      FN_Above (build_fname tl)
    | hd::tl ->
      FN_In (hd, build_fname tl)
  in build_fname l*)

let build_module_map : (file_status * (string * string) list) SMap.t ref = ref SMap.empty

let add_file (fname_str : string) (file, deps) =
  build_module_map := SMap.add fname_str (ToDoStatus file, deps) !build_module_map
  (*let fname = fname_of_string fname_str in
  let rec build_new_tree tree_smap = function
    | FN_Is (s, None) ->
      if SMap.find_opt s tree_smap <> None
      then assert false
      else
        SMap.add s (MFile (ToDoStatus file, deps)) tree_smap
    | FN_In (s, tl) ->
      let subdir = match SMap.find_opt s tree_smap with
        | None -> SMap.empty
        | Some (MDir map) -> map
        | _ -> assert false
      in let updated_dir = build_new_tree subdir tl in
      SMap.add s (MDir updated_dir) tree_smap
    | FN_Above tl ->
      let subdir = match SMap.find_opt ".." tree_smap with
        | None -> SMap.empty
        | Some (MDir map) -> map
        | _ -> assert false
      in let updated_dir = build_new_tree subdir tl in
      SMap.add ".." (MDir updated_dir) tree_smap
  in build_module_map := build_new_tree !build_module_map fname;
  assert (SMap.find_opt "test1.knl" !build_module_map <> None)*)

let topological_sort_of_files_inner (smap: string list SMap.t) : string list =
  let g = Graph.mk_graph () in
  let () = SMap.iter (fun k _ -> Graph.add_node g k) smap in
  let () = SMap.iter (fun k l -> List.iter (fun j -> Graph.add_edge g j k) l) smap in
  Graph.topological g
(*
let topological_sort_of_files (fnameL : (fname * fname list) list) =
  let rec smap_of_list smap1 smap2 = function
    | [] -> (smap1, smap2)
    | (name, deps)::tl ->
      let strname = string_of_fname name in
      smap_of_list
        (SMap.add strname name smap1)
        (SMap.add strname (List.map string_of_fname deps) smap2)
        tl
  in
  let (namesmap, depsmap) = smap_of_list SMap.empty SMap.empty fnameL in
  let sorted = topological_sort_of_files_inner depsmap in
  let rec translate_names = function
    | [] -> []
    | hd::tl -> (SMap.find hd namesmap)::translate_names tl
  in translate_names sorted

let get_file fname =
  let rec get_file (smap : module_tree SMap.t) = function
  | FN_Is (n, opt) ->
      let content =
        match SMap.find_opt n smap with
          | Some (MFile (c, d)) -> (c, d)
          | _ -> assert false
      in
      let name = match opt with
        | Some n2 -> n2
        | None -> n
      in (content, name)
  | FN_In (fname, fnametl) ->
      let submap =
        match SMap.find_opt fname smap with
          | Some (MDir dir) -> dir
          | _ -> assert false
      in get_file submap fnametl
  | FN_Above fnametl ->
    let submap =
      match SMap.find_opt ".." smap with
        | Some (MDir dir) -> dir
        | _ -> assert false
    in get_file submap fnametl
  in get_file !build_module_map fname
*)
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
  (*let rec compute_new_subtree (smap : module_tree SMap.t) = function
    | FN_Is (n, opt) ->
      let deps =
        match SMap.find_opt n smap with
          | Some (MFile (c, d)) -> d
          | _ -> assert false
      in SMap.add n (MFile (data, deps)) smap
  | FN_In (fname, fnametl) ->
      let submap =
        match SMap.find_opt fname smap with
          | Some (MDir dir) -> dir
          | _ -> assert false
      in SMap.add fname (MDir (compute_new_subtree submap fnametl)) smap
  | FN_Above fnametl ->
    let submap =
      match SMap.find_opt ".." smap with
        | Some (MDir dir) -> dir
        | _ -> assert false
    in SMap.add ".." (MDir (compute_new_subtree submap fnametl)) smap
  in build_module_map := compute_new_subtree !build_module_map f*)

let compile_file ?(show=false) f =
  let (content, deps) = SMap.find f !build_module_map(*get_file f*)
  in match content with
    | ToDoStatus cnt ->
      let ctxt =
        List.fold_left (fun l (dep, as_name) -> List.rev_append (List.rev (context_of_file dep as_name)) l) [] deps
      in
      let () = print_endline ("-- going though "^f) in
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