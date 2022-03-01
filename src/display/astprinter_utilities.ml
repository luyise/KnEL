open Ast

exception PPrinter_internal_error

let rec unfold_app l = function
  | EApp (e1, e2) -> unfold_app (e2::l) e1
  | expr -> expr :: l

let rec unfold_pi b l = function
  | EPi ((id, typ), exp) when b = (id = "_") -> unfold_pi b ((id,typ)::l) exp
  | exp -> ("_", exp)::l

let rec unfold_sigma b l = function
  | ESigma ((id, typ), exp) when b = (id = "_") -> unfold_sigma b ((id,typ)::l) exp
  | exp -> ("_", exp)::l

let rec unfold_lam l = function
  | ELam (p, exp) -> unfold_lam (p::l) exp
  | exp -> ("_",exp)::l

let rec unfold_pair = function
  | EPair ((e1, e2), _) -> e1::unfold_pair e2
  | exp -> [exp]

let rec fold_pair_list = function
 | [] -> []
 | (id, typ)::tl ->
    begin match fold_pair_list tl with
      | (idl, typ2)::l when typ = typ2 -> (id::idl, typ2)::l
      | l -> ([id], typ)::l
    end

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
  | SNeg

let needs_par above here = match above, here with
  | STop, _ | SPair, _ -> false
  | SPi, _ | SSigma, _ -> false
  | STypeBind, _ -> false
  | SArrow, SApp -> false
  | SNeg, SNeg -> false
  | _, _ -> true