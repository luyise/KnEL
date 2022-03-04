open Ast
open Renaming

(* alpha_compare test si deux expression β-réduites sont α-équivalentes  *)

let rec alpha_compare : ident list -> expr -> expr -> bool
= fun idl exp1 exp2 ->
  match exp1.desc , exp2.desc with
    | EConst c1 , EConst c2 -> c1 = c2
    | EVar x1 , EVar x2 -> x1 = x2
    | ELam ((y1 , typ1) , term_of_y1) , ELam ((y2 , typ2) , term_of_y2) ->
        if y1 = y2 then
          alpha_compare idl typ1 typ2
          && alpha_compare (y1 :: idl) term_of_y1 term_of_y2
        else begin
          let typ1' = rename idl y2 y1 typ2 in
          let term_of_y1' = rename idl y2 y1 term_of_y2 in
          alpha_compare idl typ1 typ1'
          && alpha_compare (y1 :: idl) term_of_y1 term_of_y1'
        end
    | EApp (u1 , v1) , EApp (u2 , v2) -> 
        alpha_compare idl u1 u2 && alpha_compare idl v1 v2
    | EPi ((y1 , typ1) , term_of_y1) , EPi ((y2 , typ2) , term_of_y2) ->
        if y1 = y2 then
          alpha_compare idl typ1 typ2
          && alpha_compare (y1 :: idl) term_of_y1 term_of_y2
        else begin
          let typ1' = rename idl y2 y1 typ2 in
          let term_of_y1' = rename idl y2 y1 term_of_y2 in
          alpha_compare idl typ1 typ1'
          && alpha_compare (y1 :: idl) term_of_y1 term_of_y1'
        end
    | EPair ((u1 , v1) , _) , EPair ((u2 , v2) , _) ->
        alpha_compare idl u1 u2 && alpha_compare idl v1 v2
    | EFst u1 , EFst u2 -> alpha_compare idl u1 u2
    | ESnd u1 , ESnd u2 -> alpha_compare idl u1 u2
    | ESigma ((y1 , typ1) , term_of_y1) , ESigma ((y2 , typ2) , term_of_y2) ->
        if y1 = y2 then
          alpha_compare idl typ1 typ2
          && alpha_compare (y1 :: idl) term_of_y1 term_of_y2
        else begin
          let typ1' = rename idl y2 y1 typ2 in
          let term_of_y1' = rename idl y2 y1 term_of_y2 in
          alpha_compare idl typ1 typ1'
          && alpha_compare (y1 :: idl) term_of_y1 term_of_y1'
        end
    | ETaggedExpr (u1 , _) , _ -> alpha_compare idl u1 exp2
    | _ , ETaggedExpr (u2 , _) -> alpha_compare idl exp1 u2
    | _ -> false
