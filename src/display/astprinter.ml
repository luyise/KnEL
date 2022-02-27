open Ast
open Astprinter_utilities

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
  | CLR_nam -> "\x1B[38;5;174m"     (* lavande, pâle *)
  | CLR_def -> "\x1B[39m"      (* gris, très pâle *)

let html_left_tag clr = match clr with
  | CLR_elm -> "<font color = \"#f6c266\">"     (* orange, pâle *)
  | CLR_par -> "<font color = \"#505050\">"     (* gris, terne *)
  | CLR_cst -> "<font color = \"#F5B7B1\">"     (* ocre, pâle *)
  | CLR_var -> "<font color = \"#96ab9c\">"     (* vert, pâle *)
  | CLR_nam -> "<font color = \"#d98880\">"     (* lavande, pâle *)
  | CLR_def -> "<font color = \"#F2F3F4\">"     (* gris, très pâle *)

let pp_ident clr fmt ident =
  let pref = 
    if !Config.html_view then
      html_left_tag clr
    else
      ansi_escape_code clr
  in
  let suff = 
    if !Config.html_view then
      "</font>"
    else
      ansi_escape_code CLR_def
  in
  Format.fprintf fmt "%s%s%s" pref ident suff

let rec pp_expr_inner above fmt (exp : expr) =
  match exp with
    | EConst id -> Format.fprintf fmt "%a"
        (pp_ident CLR_cst)
        (match id with
          | "Void" -> "⊥"
          | _ -> id
        )
    | EVar id -> Format.fprintf fmt "%a"
        (pp_ident CLR_var) id
    | ELam (_, _) ->
      let (hd, tl) = match unfold_lam [] exp with
        | (_, hd)::tl -> (hd, List.rev tl)
        | _ -> raise PPrinter_internal_error
      in Format.fprintf fmt "%a%a %a %a %a%a" (* "(λ (%a : %a) → %a)" *)
        (pp_ident CLR_par) (if needs_par above SLam then "(" else "")
        (pp_ident CLR_elm) "λ"
        (pp_list (fun fmt (idl, exp) ->
          Format.fprintf fmt "%a%a %a %a%a"
            (pp_ident CLR_par) "("
            (pp_list (pp_ident CLR_var)) idl
            (pp_ident CLR_elm) ":"
            (pp_expr_inner STypeBind) exp
            (pp_ident CLR_par) ")"
        )) (fold_pair_list tl)
        (pp_ident CLR_elm) "→"
        (pp_expr_inner SLam) hd
        (pp_ident CLR_par) (if needs_par above SLam then ")" else "")
    | EApp (_ , _) ->
        let expL = unfold_app [] exp in
        Format.fprintf fmt "%a%a%a" (* "(%a %a)" *)
        (pp_ident CLR_par) (if needs_par above SApp then "(" else "")
        (pp_list (pp_expr_inner SApp)) expL
        (pp_ident CLR_par) (if needs_par above SApp then ")" else "")
    | EPi (("_", _) , _) ->
        Format.fprintf fmt "%a%a%a" (* "(%a → %a)" *)
          (pp_ident CLR_par) (if needs_par above SArrow then "(" else "")
          (pp_list_sep
            (fun fmt (id, expr) -> pp_expr_inner SArrow fmt expr)
            (fun fmt () -> pp_ident CLR_elm fmt " → ")) (List.rev (unfold_pi true [] exp))
          (pp_ident CLR_par) (if needs_par above SArrow then ")" else "")
    | EPi (_, _) ->
        let (exp, tl) = match unfold_pi false [] exp with
          | (_,exp)::tl -> exp, List.rev tl
          | _ -> raise PPrinter_internal_error
        in
          Format.fprintf fmt "%a%a %a%a %a%a" (* "(Π (%a : %a), %a)"*)
          (pp_ident CLR_par) (if needs_par above SPi then "(" else "")
          (pp_ident CLR_elm) "Π"
          (pp_list (fun fmt (idl, exp1) ->
            Format.fprintf fmt "%a%a %a %a%a"
            (pp_ident CLR_par) "("
            (pp_list (pp_ident CLR_var)) idl
            (pp_ident CLR_elm) ":"
            (pp_expr_inner STypeBind) exp1
            (pp_ident CLR_par) ")"
          )) (fold_pair_list tl)
          (pp_ident CLR_elm) ","
          (pp_expr_inner SPi) exp
          (pp_ident CLR_par) (if needs_par above SPi then ")" else "")
    | ESigma (("_", _) , _) ->
        Format.fprintf fmt "%a%a%a" (* "(%a × %a)" *)
          (pp_ident CLR_par) (if needs_par above SProd then "(" else "")
          (pp_list_sep
            (fun fmt (id, expr) -> pp_expr_inner SProd fmt expr)
            (fun fmt () -> pp_ident CLR_elm fmt " × ")) (List.rev (unfold_sigma true [] exp))
          (pp_ident CLR_par) (if needs_par above SProd then ")" else "")
    | ESigma (_, _) ->
        let (exp, tl) = match unfold_sigma false [] exp with
          | (_,exp)::tl -> exp, List.rev tl
          | _ -> raise PPrinter_internal_error
        in
          Format.fprintf fmt "%a%a %a%a %a%a" (* "(Π (%a : %a), %a)"*)
          (pp_ident CLR_par) (if needs_par above SSigma then "(" else "")
          (pp_ident CLR_elm) "Σ"
          (pp_list (fun fmt (idl, exp1) ->
            Format.fprintf fmt "%a%a %a %a%a"
            (pp_ident CLR_par) "("
            (pp_list (pp_ident CLR_var)) idl
            (pp_ident CLR_elm) ":"
            (pp_expr_inner STypeBind) exp1
            (pp_ident CLR_par) ")"
          )) (fold_pair_list tl)
          (pp_ident CLR_elm) ","
          (pp_expr_inner SSigma) exp
          (pp_ident CLR_par) (if needs_par above SSigma then ")" else "")
    | EPair (_, _) ->
      Format.fprintf fmt "%a%a%a"    (* "(%a, %a)" *)
        (pp_ident CLR_par) "("
        (pp_list_sep (pp_expr_inner SPair) (fun fmt () -> pp_ident CLR_elm fmt ", ")) (unfold_pair exp)
        (pp_ident CLR_par) ")"
    | EFst exp1 -> Format.fprintf fmt "%a%a %a%a"       (* "(fst %a)" *)
        (pp_ident CLR_par) (if needs_par above SProj then "(" else "")
        (pp_ident CLR_cst) "fst"
        (pp_expr_inner SProj) exp1
        (pp_ident CLR_par) (if needs_par above SProj then ")" else "")
    | ESnd exp1 -> Format.fprintf fmt "%a%a %a%a"       (* "(snd %a)" *)
        (pp_ident CLR_par) (if needs_par above SProj then "(" else "")
        (pp_ident CLR_cst) "snd"
        (pp_expr_inner SProj) exp1
        (pp_ident CLR_par) (if needs_par above SProj then ")" else "")
    | ETaggedExpr (exp1 , _) -> Format.fprintf fmt "%a"
        (pp_expr_inner above) exp1

let pp_expr = pp_expr_inner STop

let pp_context fmt (ctx : context) =
  if !Config.html_view then begin
    Format.fprintf fmt "<br><br>";
    let f =
      (fun (name, s) ->
        Format.fprintf fmt "<p style = \"margin-top: -12px; margin-left: 30px; text-indent: -15px\" >";
        Format.fprintf fmt "%a %a %a"
          (pp_ident CLR_nam) name
          (pp_ident CLR_def) ":"
          pp_expr s;
        Format.fprintf fmt "</p>"
      )
    in
    List.iter f (List.rev ctx)
  end else begin
    let f =
      (fun (name, s) ->
        Format.fprintf fmt "\t%a %a %a\n" 
          (pp_ident CLR_nam) name
          (pp_ident CLR_def) ":"
          pp_expr s)
    in
    List.iter f (List.rev ctx)
  end
  
