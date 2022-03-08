open Ast
open Location

module SMap = Map.Make(String)
module SSet = Set.Make(String)
module IMap = Map.Make(Int)

type assoc =
  | Left
  | Right

type priority_ctxt = (int * assoc) SMap.t

let combine_locs l1 l2 =
  {
    loc_ghost = l1.loc_ghost & l2.loc_ghost;
    loc_start = l1.loc_start;
    loc_end   = l2.loc_end;
  }


let check_if_allowed ~loc cstSet id = if SSet.mem id cstSet then assert false else id


let rec find_loc_inner id e = match e.desc with
  | EVar id2 when id = id2 -> Some []
  | EPi ((id1, e1), { desc = EApp (e2, { desc = EVar id2; _ }); _ }, None) when id1 = id2 -> begin
      match find_loc_inner id e1 with
          | Some p -> Some (PFunSource::p)
          | None ->
          begin match find_loc_inner id e2 with
              | Some p -> Some (PFunDepTarget::p)
              | None -> None
      end end
  | ESigma ((id1, e1), { desc = EApp (e2, { desc = EVar id2; _ }); _ }, None) when id1 = id2 -> begin
      match find_loc_inner id e1 with
          | Some p -> Some (PSigFst::p)
          | None ->
          begin match find_loc_inner id e2 with
              | Some p -> Some (PSigDepSnd::p)
              | None -> None
      end end 
  | EPi ((_, e1), e2, None) -> begin
      match find_loc_inner id e1 with
          | Some p -> Some (PFunSource::p)
          | None ->
          begin match find_loc_inner id e2 with
              | Some p -> Some (PFunNonDepTarget::p)
              | None -> None
      end end
  | ESigma ((_, e1), e2, None) -> begin
      match find_loc_inner id e1 with
          | Some p -> Some (PSigFst::p)
          | None ->
          begin match find_loc_inner id e2 with
              | Some p -> Some (PSigNonDepSnd::p)
              | None -> None
      end end 
  | _ -> None

let find_loc b id e2 =
  let rec go_to_inner e = match e.desc with
          | EPi    ((_, e1), _, None) | ELam   ((_, e1), _, None)
          | ESigma ((_, e1), _, None) -> find_loc_inner id e1
          | EPi    (_, e1, Some _) | ELam   (_, e1, Some _)
          | ESigma (_, e1, Some _) -> find_loc_inner id e1
  in if b
  then None
  else match go_to_inner e2 with
      | Some p -> Some p
      | None -> assert false

let rec find_highest priorityMaping = function
  | [] -> None
  | ({desc = EVar id; _} as evar)::tl -> begin
    match SMap.find_opt id priorityMaping, find_highest priorityMaping tl with
      | None, None -> None
      | None, Some (prio, assoc, e, (h1, h2)) -> Some (prio, assoc, e, (evar::h1, h2))
      | Some (prio1, assoc1), Some (prio2, assoc2, e, (h1, h2)) when prio1 < prio2 ->
        Some (prio1, assoc1, e, (evar::h1, h2))
      | Some (prio1, assoc1), Some (prio2, assoc2, e, (h1, h2)) when prio1 > prio2 ->
        Some (prio2, assoc2, evar, ([], tl))
      | Some (prio, Left), Some (_, Left, e, (h1, h2)) ->
        Some (prio, Left, e, (evar::h1, h2))
      | Some (prio, Right), Some (_, Right, e, (h1, h2)) ->
        Some (prio, Right, evar, ([], tl))
      | _, _ -> assert false
    end
  | hd::tl -> begin
    match find_highest priorityMaping tl with
      | Some (prio, assoc, e, (h1, h2)) -> Some (prio, assoc, e, (hd::h1, h2))
      | None -> None
  end

let rec rewrite = function
  | [] -> assert false
  | [hd] -> hd
  | hd::tl -> let e = rewrite tl in {desc = EApp (hd, e); loc = combine_locs hd.loc e.loc }

let rec build_priority prioMap el =
  match find_highest prioMap el with
    | None -> rewrite el
    | Some (_, _, {desc = EVar " arrow"; _}, (l1, l2)) ->
      let e1 = build_priority prioMap l1 in
      let e2 = build_priority prioMap l2 in
      { desc = EPi (("_", e1), e2, None); loc = combine_locs e1.loc e2.loc }
    | Some (_, _, eop, (l1, l2)) ->
        let e1 = build_priority prioMap l1 in
        let e2 = build_priority prioMap l2 in
        let a1 = { desc = EApp (eop, e1); loc = combine_locs eop.loc e1.loc } in
        { desc = EApp (a1, e2); loc = combine_locs a1.loc e2.loc }


let rec expr_of_parsed_expr cstSet prioMap pe = 
  let desc = match pe.desc with
    | PVar id when SSet.mem id cstSet -> EConst id
    | PVar id -> EVar id
    | PPair ((e1, e2), None) ->
      EPair ((expr_of_parsed_expr cstSet prioMap e1, expr_of_parsed_expr cstSet prioMap e2), None)
    | PPair ((e1, e2), Some e3) ->
      EPair ((expr_of_parsed_expr cstSet prioMap e1, expr_of_parsed_expr cstSet prioMap e2), Some (expr_of_parsed_expr cstSet prioMap e3))
    | PApp peL ->
      let eL = List.map (expr_of_parsed_expr cstSet prioMap) peL in
      (build_priority prioMap eL).desc
    | PLam ((id, _), _, _) | PPi ((id, _), _, _)
    | PSigma ((id, _), _, _) when SSet.mem id cstSet ->
      assert false
    | PLam ((id, e1), e2, Explicit) ->
      let e1 = expr_of_parsed_expr cstSet prioMap e1 in
      let e2 = expr_of_parsed_expr cstSet prioMap e2 in
      ELam ((id, e1), e2, None)
    | PPi ((id, e1), e2, Explicit) ->
      let e1 = expr_of_parsed_expr cstSet prioMap e1 in
      let e2 = expr_of_parsed_expr cstSet prioMap e2 in
      EPi ((id, e1), e2, None)
    | PSigma ((id, e1), e2, Explicit) ->
      let e1 = expr_of_parsed_expr cstSet prioMap e1 in
      let e2 = expr_of_parsed_expr cstSet prioMap e2 in
      ESigma ((id, e1), e2, None)
    | _ -> assert false
  in { desc; loc = pe.loc }

let prioDefault =
  let l = []
  in List.fold_left (fun m (id, p) -> SMap.add id p m) SMap.empty l
let cstDefault =
  let l = [] in
  List.fold_left (fun m id -> SSet.add id m) SSet.empty l
  


let expr_of_parsed_expr_default =
  expr_of_parsed_expr cstDefault prioDefault
