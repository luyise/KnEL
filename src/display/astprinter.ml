open Ast

let pp_ident fmt ident = Format.fprintf fmt "%s" ident

let rec pp_expr fmt (exp : expr) =
  match exp with
    | EConst id -> Format.fprintf fmt "%a"
        pp_ident id
    | EVar id -> Format.fprintf fmt "%a"
        pp_ident id
    | ELam ((id , exp1) , exp2) -> Format.fprintf fmt "(\x1B[38;5;130mλ\x1B[39m (%a \x1B[38;5;130m:\x1B[39m %a) \x1B[38;5;130m→\x1B[39m %a)"
        pp_ident id
        pp_expr exp1
        pp_expr exp2
    | EApp (exp1 , exp2) -> Format.fprintf fmt "(%a %a)"
        pp_expr exp1
        pp_expr exp2
    | EPi ((id , exp1) , exp2) ->
        if id = "_" then
          Format.fprintf fmt "(%a \x1B[38;5;130m→\x1B[39m %a)"
          pp_expr exp1
          pp_expr exp2
        else
          Format.fprintf fmt "(\x1B[38;5;130mΠ\x1B[39m (%a \x1B[38;5;130m:\x1B[39m %a)\x1B[38;5;130m,\x1B[39m %a)"
          pp_ident id
          pp_expr exp1
          pp_expr exp2
    | EPair ((exp1 , exp2) , _) -> Format.fprintf fmt "(%a \x1B[38;5;130m,\x1B[39m %a)"
        pp_expr exp1
        pp_expr exp2
    | EFst exp1 -> Format.fprintf fmt "(\x1B[38;5;130mfst\x1B[39m %a)"
        pp_expr exp1
    | ESnd exp1 -> Format.fprintf fmt "(\x1B[38;5;130msnd\x1B[39m %a)"
        pp_expr exp1
    | ESigma ((id , exp1) , exp2) -> 
        if id = "_" then
          Format.fprintf fmt "(%a \x1B[38;5;130m×\x1B[39m %a)"
          pp_expr exp1
          pp_expr exp2
        else
          Format.fprintf fmt "(\x1B[38;5;130mΣ\x1B[39m (%a \x1B[38;5;130m:\x1B[39m %a)\x1B[38;5;130m,\x1B[39m %a)"
          pp_ident id
          pp_expr exp1
          pp_expr exp2
    | ETaggedExpr (exp1 , _) -> Format.fprintf fmt "%a"
        pp_expr exp1

let pp_context fmt (ctx : context) =
  let f =
    if !Config.html_view
    then
      (fun (name, s) -> 
        Format.fprintf fmt "<p style=\"text-indent:20px;\">%s : %a</p>"
          name
          pp_expr s)
    else
      (fun (name, s) ->
        Format.fprintf fmt "\t%s : %a\n" 
          name
          pp_expr s)
  in
  List.iter f ctx
