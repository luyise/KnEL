open Ast
open Environment
open Renaming
open Substitution

(* Prend en argument une liste d'ident déjà utilisés par l'environnement courant, 
  et beta-réduit un terme passé en paramètre *)

let rec beta_reduce : ident list -> expr -> expr
= fun idl exp ->
  match exp with
    | EConst c -> EConst c
    | EVar x -> EVar x
    | ELam ((y , typ) , term_of_y) ->
        ELam ((y , beta_reduce idl typ) , beta_reduce (y :: idl) term_of_y)
    | EApp (u , v) ->
        let u' = beta_reduce idl u in
        let v' = beta_reduce idl v in
        begin match u' with
          | ELam ((x , typ) , term_of_x) ->
              beta_reduce idl (substitute idl x v' term_of_x)
          | _ -> EApp (u' , v')
        end
    | EPi ((y , typ) , term_of_y) ->
        EPi ((y , beta_reduce idl typ) , beta_reduce (y :: idl) term_of_y)
    | EPair ((exp1 , exp2) , Some typ) ->
        EPair ((beta_reduce idl exp1 , beta_reduce idl exp2) , Some (beta_reduce idl typ))
    | EPair ((exp1 , exp2) , None) ->
        EPair ((beta_reduce idl exp1 , beta_reduce idl exp2) , None)
    | EFst exp1 -> EFst (beta_reduce idl exp1)
    | ESnd exp1 -> ESnd (beta_reduce idl exp1) 
    | ESigma ((y , typ) , term_of_y) ->
        ESigma ((y , beta_reduce idl typ) , beta_reduce (y :: idl) term_of_y)
    | ETaggedExpr (exp1 , typ) ->
        ETaggedExpr (beta_reduce idl exp1 , beta_reduce idl typ)