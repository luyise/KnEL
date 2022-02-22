open Ast
open Environment

exception Unknown_ident
exception Typing_error

let rec is_well_formed_context : ctx -> bool
= match ctx with
  | [] -> true
  | (id , exp) :: ctx' ->
      match search_for_term id ctx' with
        | None -> is_well_formed ctx'
        | Some _ -> false

(* La fonction is_well_formed véfifie qu'une expression forme un type
  dans un context donné *)

let rec is_well_formed_type : ctx -> expr -> bool
= fun ctx exp ->
  match exp with
    | EPi ((id , exp1) , exp2) ->
      is_well_formed_type ((id , exp1) :: ctx) exp2
    | ESigma ((id , exp1) , exp2) ->
      is_well_formed_type ((id , exp1) :: ctx) exp2
    | _ -> false
