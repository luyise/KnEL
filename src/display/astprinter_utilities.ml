open Ast

exception PPrinter_internal_error

let rec unfold_app l = function
  | EApp (e1, e2) -> unfold_app (e2::l) e1
  | expr -> expr :: l

let rec unfold_pi b l = function
  | EPi ((id, typ), exp) when b = (id = "_") -> unfold_pi b ((id,typ)::l) exp
  | exp -> ("_", exp)::l

let rec unfold_sigma b l = function
  | ESigma ((id, typ), exp) when b = (id = "_") -> unfold_pi b ((id,typ)::l) exp
  | exp -> ("_", exp)::l

let rec unfold_lam l = function
  | ELam (p, exp) -> unfold_lam (p::l) exp
  | exp -> ("_",exp)::l

let rec unfold_pair = function
  | EPair ((e1, e2), _) -> e1::unfold_pair e2
  | exp -> [exp]

let rec fold_pair_list = function
 | [(id, typ)] -> [[id], typ]
 | [] -> raise PPrinter_internal_error
 | (id, typ)::tl ->
    let (idl, typ2)::l = fold_pair_list tl in
    if typ = typ2 then
        (id::idl, typ2)::l
    else
      ([id], typ)::(idl, typ2)::l

let rec pp_list pp fmt = function
  | [] -> raise PPrinter_internal_error
  | [x] -> pp fmt x
  | x::tl -> Format.fprintf fmt "%a %a" pp x (pp_list pp) tl

let rec pp_list_sep pp pp_sep fmt = function
  | [] -> raise PPrinter_internal_error
  | [x] -> pp fmt x
  | x::tl -> Format.fprintf fmt "%a%a%a" pp x pp_sep () (pp_list_sep pp pp_sep) tl

type struct_element =
  | STop
  | STypeBind
  | SPair
  | SApp
  | SLam
  | SPi
  | SSigma
  | SArrow
  | SProd
  | SProj

let needs_par above here = match above, here with
  | STop, _ | SPair, _ -> false
  | SPi, _ | SSigma, _ -> false
  | STypeBind, _ -> false
  | SArrow, SApp -> false
  | _, _ -> true