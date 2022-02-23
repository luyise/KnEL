open Ast
open Constants
open Environment

exception Unknown_ident
exception Ident_colision
exception Type_error
exception Invalid_context
exception Unable_to_infer_type

let rec compute_type_of_term : context -> expr -> expr
= fun ctx term ->
  match term with
    | EConst id ->
        begin match
        (Array.find_opt 
          (function
            | id' , Some _ when id = id' -> true
            | _ -> false
          ) constants
        ) with
          | Some (_ , typ) -> typ
          | None -> raise Unknown_ident
        end
    | EVar id ->
        begin match in_context_opt id ctx
        ) with
          | Some typ -> typ
          | _ -> Unknown_ident
        end
    | ELam ((id , id_typ) , exp_of_id) ->
        begin match in_context_opt id ctx with
          | Some _ -> raise Ident_colision
          | None ->
            begin match
                compute_type_of_term
                  ctx
                  id_typ ,
                compute_type_of_term 
                  ((id , id_typ) :: ctx)
                  exp_of_id
              with
                | EConst "Type" ,
                  typ_of_exp_of_id ->
                    EPi ((id , id_typ) , typ_of_exp_of_id)
            end
        end
    | EApp (exp1 , exp2) ->
        begin match
          compute_type_of_term ctx exp1 ,
          compute_type_of_term ctx exp2
        with
          | EPi ((id , id_typ) , typ_of_exp_of_id) , exp2_typ
            when id_typ = exp2_typ -> exp2_typ
          | _ -> raise Type_error
        end
    | EPi ((id , typ_a) , exp) ->
        begin match in_context_opt id ctx with
          | Some _ -> raise Ident_colision
          | None ->
              match
                compute_type_of_term
                  ctx
                  typ_a ,
                compute_type_of_term 
                  ((id , typ_a) :: ctx)
                  exp
              with
                | EConst "Type" , 
                  EConst "Type" ->
                    EConst "Type"
        end
    | EPair (term1 , term2) * Some (ELam ((id , typ_a) , exp)) ->
        begin match in_context_opt id ctx with
          | Some _ -> raise Ident_colision
          | None ->
              match
                compute_type_of_term
                  ctx
                  term1 ,
                compute_type_of_term
                  ((id , typ_a) :: ctx)
                  exp ,
                compute_type_of_term
                  ctx
                  term2
              with
                | typ_a' , EConst "Type" , exp'
                  when typ_a = typ_a' && exp = exp' (*(en b)* !!!!!!!!!!*)
                  -> ESigma ((id , typ_a) , exp)
    | EPair (term1 , term2) * Some exp ->
        begin match compute_type_of_term ctx exp with
          | EPi ((_ , typ_a) , _)) ->
              begin match compute_type_of_term ctx term1 with
                | typ when typ = typ_a -> raise Unable_to_infer_type
                | _ -> raise Type_error
              end
          | _ -> raise Type_error
        end
    | EPair _ -> raise Type_error
    | EFst term ->
        begin match compute_type_of_term ctx term with
          | ESigma ((_ , typ_a) , _) -> typ_a
          | _ -> raise Type_error
        end
    | ESnd term ->
        begin match compute_type_of_term ctx term with
          | ESigma ((id , typ_a) , exp) -> exp (* en EFst term !! *)
          | _ -> raise Type_error
        end
    | ESigma ((id , typ_a) , exp) ->
        begin match in_context_opt id ctx with
            | Some _ -> raise Ident_colision
            | None ->
                match
                  compute_type_of_term
                    ctx
                    typ_a ,
                  compute_type_of_term 
                    ((id , typ_a) :: ctx)
                    exp
                with
                  | EConst "Type" , 
                    EConst "Type" ->
                      EConst "Type"
        end
    | ETaggedExpr (term , exp) ->
        if compute_type_of_term ctx term = exp then exp
        else raise Type_error
                