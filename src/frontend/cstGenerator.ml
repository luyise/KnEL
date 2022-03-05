open Parse
open Ast

let rec pp_expr fmt e = match e.desc with
  | EVar n -> Format.fprintf fmt "mk_loc (EVar \"%s\")" n
  | EPi ((id, p1), p2) ->
    Format.fprintf fmt "mk_loc (EPi ((\"%s\", %a), %a))"
      id pp_expr p1 pp_expr p2
  | ESigma ((id, p1), p2) ->
    Format.fprintf fmt "mk_loc (ESigma ((\"%s\", %a), %a))"
      id pp_expr p1 pp_expr p2
  | ELam ((id, p1), p2) ->
    Format.fprintf fmt "mk_loc (ELam ((\"%s\", %a), %a))"
      id pp_expr p1 pp_expr p2
  | ETaggedExpr (p1, p2) ->
    Format.fprintf fmt "mk_loc (ETaggedExpr (%a, %a))"
      pp_expr p1 pp_expr p2
  | EPair ((p1, p2), None) ->
    Format.fprintf fmt "mk_loc (EPair ((%a, %a), None))"
      pp_expr p1 pp_expr p2
  | EPair ((p1, p2), Some p3) ->
    Format.fprintf fmt "mk_loc (EPair ((%a, %a), Some (%a)))"
      pp_expr p1 pp_expr p2 pp_expr p3
  | EFst p1 ->
    Format.fprintf fmt "mk_loc (EFst (%a))"
      pp_expr p1
  | ESnd p1 ->
    Format.fprintf fmt "mk_loc (ESnd (%a))"
      pp_expr p1
  | EApp (p1, p2) ->
    Format.fprintf fmt "mk_loc (EApp (%a, %a))"
      pp_expr p1 pp_expr p2
  | EConst id ->
    Format.fprintf fmt "mk_loc (EConst \"%s\")" id

let rec pp_cst fmt (id, e) =
  Format.fprintf fmt "(\"%s\", %a)" id pp_expr e

let rec pp_list pp_item fmt = function
  | [] -> ()
  | h::tl ->
    Format.fprintf fmt "\t%a;\n%a"
      pp_item h
      pp_list tl;;

let rec pp_in_expr fmt e = match e.desc with
  | EVar n when String.starts_with ~prefix:"'" n -> Format.fprintf fmt "%s" (String.sub n 1 (String.length n - 1))
  | EVar n -> Format.fprintf fmt "{desc = EVar \"%s\"; _ }" n
  | EPi ((id, p1), p2) ->
    Format.fprintf fmt "{ desc = EPi ((\"%s\", %a), %a); _ }"
      id pp_expr p1 pp_expr p2
  | ESigma ((id, p1), p2) ->
    Format.fprintf fmt "{ desc = ESigma ((\"%s\", %a), %a); _ }"
      id pp_expr p1 pp_expr p2
  | ELam ((id, p1), p2) ->
    Format.fprintf fmt "{ desc = ELam ((\"%s\", %a), %a); _ }"
      id pp_expr p1 pp_expr p2
  | ETaggedExpr (p1, p2) ->
    Format.fprintf fmt "{ desc = ETaggedExpr (%a, %a); _ }"
      pp_expr p1 pp_expr p2
  | EPair ((p1, p2), None) ->
    Format.fprintf fmt "{ desc = EPair ((%a, %a), None); _ }"
      pp_expr p1 pp_expr p2
  | EPair ((p1, p2), Some p3) ->
    Format.fprintf fmt "{ desc = EPair ((%a, %a), Some (%a)); _ }"
      pp_expr p1 pp_expr p2 pp_expr p3
  | EFst p1 ->
    Format.fprintf fmt "{ desc = EFst (%a); _ }"
      pp_expr p1
  | ESnd p1 ->
    Format.fprintf fmt "{ desc = ESnd (%a); _ }"
      pp_expr p1
  | EApp (p1, p2) ->
    Format.fprintf fmt "{ desc = EApp (%a, %a); _ }"
      pp_expr p1 pp_expr p2
  | EConst id ->
    Format.fprintf fmt "{ desc = EConst \"%s\"; _ }" id


let pp_bred fmt (a, b) =
  Format.fprintf fmt "function | %a -> Some (%a) | _ -> None" pp_in_expr a pp_out_expr b


let fdesc = open_in "kernel/primitives.knl" in
let lex = Lexing.from_channel fdesc in
let (cst, beta_red, defs) = Parser.primitives Lexer.next_token lex in
let () = close_in fdesc in
(*let () = assert (beta_red = []) in *)
let fdesc = open_out "constants.ml" in
let () = Format.fprintf (Format.formatter_of_out_channel fdesc) "
open Parse
open Ast
open Location

let mk_loc e = {desc = e; loc = none}

let constants: context =
[
%a]

let beta_red: Ast.expr -> Ast.expr option =
[
%a]
" (pp_list pp_cst) cst (pp_list pp_bred) beta_red
in close_out fdesc