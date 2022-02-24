open Ast

let pp_ident fmt ident = Format.fprintf fmt "%s" ident

let rec pp_expr fmt (exp : expr) =
  match exp with
    | EConst id -> Format.fprintf fmt "%a"
        pp_ident id
    | EVar id -> Format.fprintf fmt "%a"
        pp_ident id
    | ELam ((id , exp1) , exp2) -> Format.fprintf fmt "(λ (%a : %a) → %a)"
        pp_ident id
        pp_expr exp1
        pp_expr exp2
    | EApp (exp1 , exp2) -> Format.fprintf fmt "%a %a"
        pp_expr exp1
        pp_expr exp2
    | EPi ((id , exp1) , exp2) ->
        if id = "_" then
          Format.fprintf fmt "(%a → %a)"
          pp_expr exp1
          pp_expr exp2
        else
          Format.fprintf fmt "(Π (%a : %a) %a)"
          pp_ident id
          pp_expr exp1
          pp_expr exp2
    | EPair ((exp1 , exp2) , _) -> Format.fprintf fmt "(%a , %a)"
        pp_expr exp1
        pp_expr exp2
    | EFst exp1 -> Format.fprintf fmt "(fst %a)"
        pp_expr exp1
    | ESnd exp1 -> Format.fprintf fmt "(snd %a)"
        pp_expr exp1
    | ESigma ((id , exp1) , exp2) -> 
        if id = "_" then
          Format.fprintf fmt "(%a × %a)"
          pp_expr exp1
          pp_expr exp2
        else
          Format.fprintf fmt "(Σ (%a : %a) %a)"
          pp_ident id
          pp_expr exp1
          pp_expr exp2
    | ETaggedExpr (exp1 , _) -> Format.fprintf fmt "%a"
        pp_expr exp1

let pp_context fmt (ctx : context) =
  List.iter
    (fun (id , exp) -> 
      Format.fprintf fmt "\t%s : %a\n" 
        id
        pp_expr exp
    ) ctx
