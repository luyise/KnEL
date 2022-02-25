open Ast

type coloration =
  | CLR_elm   (* couleur des éléments, tels que →, Π, λ, Σ, , ...*)
  | CLR_par   (* couleur des parenthèses *)
  | CLR_cst   (* couleur des constantes, telles que Type, ⊥, Unit... *)
  | CLR_var   (* couleur des variables liées *)
  | CLR_nam  (* couleur des noms définis par l'utilisateurs : noms de théorèmes, définition, hypothèses etc *)
  | CLR_def   (* couleur par défaut *)

let ansi_escape_code clr = match clr with
  | CLR_elm -> "\x1B[38;5;179m"     (* orange, pâle *)
  | CLR_par -> "\x1B[38;5;242m"     (* gris, terne *)
  | CLR_cst -> "\x1B[38;5;181m"     (* ocre, pâle *)
  | CLR_var -> "\x1B[38;5;109m"     (* vert, pâle *)
  | CLR_nam -> "\x1B[38;5;183m"     (* lavande, pâle *)
  | CLR_def -> "\x1B[39m"      (* gris, très pâle *)

let pp_ident clr fmt ident =
  let pref = ansi_escape_code clr in
  let suff = ansi_escape_code CLR_def in
  Format.fprintf fmt "%s%s%s" pref ident suff

let rec pp_expr fmt (exp : expr) =
  match exp with
    | EConst id -> Format.fprintf fmt "%a"
        (pp_ident CLR_cst)
        (match id with
          | "Void" -> "⊥"
          | _ -> id
        )
    | EVar id -> Format.fprintf fmt "%a"
        (pp_ident CLR_var) id
    | ELam ((id , exp1) , exp2) -> Format.fprintf fmt "%a%a %a%a %a %a%a %a %a%a" (* "(λ (%a : %a) → %a)" *)
        (pp_ident CLR_par) "("
        (pp_ident CLR_elm) "λ"
        (pp_ident CLR_par) "("
        (pp_ident CLR_var) id
        (pp_ident CLR_elm) ":"
        pp_expr exp1
        (pp_ident CLR_par) ")"
        (pp_ident CLR_elm) "→"
        pp_expr exp2
        (pp_ident CLR_par) ")"
    | EApp (exp1 , exp2) -> Format.fprintf fmt "%a%a %a%a" (* "(%a %a)" *)
        (pp_ident CLR_par) "("
        pp_expr exp1
        (pp_ident CLR_par) ")"
        pp_expr exp2
    | EPi ((id , exp1) , exp2) ->
        if id = "_" then              (* "(%a → %a)" *)
          Format.fprintf fmt "%a%a %a %a%a"
          (pp_ident CLR_par) "("
          pp_expr exp1
          (pp_ident CLR_elm) "→" 
          pp_expr exp2
          (pp_ident CLR_par) ")"
        else                          (* "(Π (%a : %a), %a)"*)
          Format.fprintf fmt "%a%a %a%a %a %a%a%a %a%a"
          (pp_ident CLR_par) "("
          (pp_ident CLR_elm) "Π"
          (pp_ident CLR_par) "("
          (pp_ident CLR_var) id
          (pp_ident CLR_elm) ":"
          pp_expr exp1
          (pp_ident CLR_par) ")"
          (pp_ident CLR_elm) ","
          pp_expr exp2
          (pp_ident CLR_par) ")"
    | EPair ((exp1 , exp2) , _) -> Format.fprintf fmt "%a%a %a %a%a"    (* "(%a , %a)" *)
        (pp_ident CLR_par) "("
        pp_expr exp1
        (pp_ident CLR_elm) ","
        pp_expr exp2
        (pp_ident CLR_par) ")"
    | EFst exp1 -> Format.fprintf fmt "%a%a %a%a"       (* "(fst %a)" *)
        (pp_ident CLR_par) "("
        (pp_ident CLR_cst) "fst"
        pp_expr exp1
        (pp_ident CLR_par) ")"
    | ESnd exp1 -> Format.fprintf fmt "%a%a %a%a"       (* "(snd %a)" *)
        (pp_ident CLR_par) "("
        (pp_ident CLR_cst) "snd"
        pp_expr exp1
        (pp_ident CLR_par) ")"
    | ESigma ((id , exp1) , exp2) -> 
        if id = "_" then              (* "(%a × %a)" *)
          Format.fprintf fmt "%a%a %a %a%a"
          (pp_ident CLR_par) "("
          pp_expr exp1
          (pp_ident CLR_elm) "×" 
          pp_expr exp2
          (pp_ident CLR_par) ")"
        else                          (* "(Σ (%a : %a), %a)"*)
          Format.fprintf fmt "%a%a %a%a %a %a%a%a %a%a"
          (pp_ident CLR_par) "("
          (pp_ident CLR_elm) "Σ"
          (pp_ident CLR_par) "("
          (pp_ident CLR_var) id
          (pp_ident CLR_elm) ":"
          pp_expr exp1
          (pp_ident CLR_par) ")"
          (pp_ident CLR_elm) ","
          pp_expr exp2
          (pp_ident CLR_par) ")"
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
        Format.fprintf fmt "\t%a : %a\n" 
          (pp_ident CLR_var) name
          pp_expr s)
  in
  List.iter f ctx
