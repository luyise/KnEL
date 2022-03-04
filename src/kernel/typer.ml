open Parse
open Ast
open Constants
open Environment
open Renaming
open Substitution
open Alpha_renaming
open Beta_red

exception Unknown_ident
exception Type_error
exception Invalid_context
exception Unable_to_infer_type

(* /!\ la fonction compute_type_if_term doit être appellée avec l'ident list contenant le List.map fst du context *)

let rec compute_type_of_term : context -> ident list -> expr -> expr
= fun ctx idl term ->
  let desc = 
  match term.desc with
    | EConst c ->
        begin match
        (List.find_opt
          (function
            | c' , _ when c = c' -> true
            | _ -> false
          ) constants
        ) with
          | Some (_ , typ) -> typ.desc
          | None -> raise Unknown_ident
        end
    | EVar x ->
        begin match in_context_opt x ctx
        with
          | Some typ -> typ.desc
          | _ -> raise Unknown_ident
        end
    | ELam ((x , x_typ) , exp_of_x) ->
        begin match in_context_opt x ctx with
          | Some _ ->
              let z = get_unused_ident idl in
              let exp_of_z = rename idl x z exp_of_x in
              (compute_type_of_term ctx idl { desc = ELam ((z , x_typ) , exp_of_z) ; loc = term.loc }).desc
          | None ->
            let (ctx' , idl') =
              if x = "_" then (ctx , idl) 
              else (((x , x_typ) :: ctx) , (x :: idl)) 
            in
            begin match
                (compute_type_of_term ctx idl x_typ).desc ,
                compute_type_of_term ctx' idl' exp_of_x
              with
                | _ , typ_of_exp_of_x ->
                    EPi ((x , x_typ) , typ_of_exp_of_x)
            end
        end
    | EApp (exp1 , exp2) ->
        begin match
          (beta_reduce idl (compute_type_of_term ctx idl exp1)).desc ,
          beta_reduce idl (compute_type_of_term ctx idl exp2)
        with
          | EPi ((id , id_typ) , typ_of_exp_of_id) , exp2_typ
            when
              alpha_compare idl id_typ exp2_typ 
              -> (substitute idl id exp2 typ_of_exp_of_id).desc
          | _ -> raise Type_error
        end
    | EPi ((id , typ_a) , exp) ->
        begin match in_context_opt id ctx with
          | Some _ ->
              let z = get_unused_ident idl in
              let exp_of_z = rename idl id z exp in
              (compute_type_of_term ctx idl { desc = EPi ((z , typ_a) , exp_of_z) ; loc = term.loc }).desc
          | None ->
              let (ctx' , idl') = 
                if id = "_" then (ctx , idl) 
                else (((id , typ_a) :: ctx) , (id :: idl)) 
              in
              match
                (beta_reduce idl (compute_type_of_term ctx idl typ_a)).desc ,
                (beta_reduce idl (compute_type_of_term ctx' idl' exp)).desc
              with
                | EApp ({ desc = EConst "Type" ; loc = Location.none } 
                    , { desc = EVar x ; loc = Location.none }) , 
                  EApp ({ desc = EConst "Type" ; loc = Location.none } 
                    , { desc = EVar y ; loc = Location.none }) 
                  when x = y ->
                    EApp ({ desc = EConst "Type" ; loc = Location.none } 
                    , { desc = EVar x ; loc = Location.none })
                | _ -> raise Type_error
        end
    | EPair ((term1 , term2) , Some typ) ->
        let typ' = beta_reduce idl typ in
        begin match typ'.desc with
          | ELam ((id , typ_a) , exp) ->
            begin match in_context_opt id ctx with
              | Some _ ->
                  let z = get_unused_ident idl in
                  let exp_of_z = rename idl id z exp in
                  (compute_type_of_term ctx idl 
                    { desc = EPair ((term1 , term2) , Some { desc = ELam ((z , typ_a) , exp_of_z) ; loc = term.loc })
                    ; loc = term.loc }).desc
              | None ->
                  let (ctx' , idl') = 
                    if id = "_" then (ctx , idl) 
                    else (((id , typ_a) :: ctx) , (id :: idl))
                  in
                  match
                    beta_reduce idl (compute_type_of_term ctx idl term1) ,
                    (beta_reduce idl' 
                      (compute_type_of_term ctx' idl' exp)).desc ,
                    beta_reduce idl (compute_type_of_term ctx idl term2)
                  with
                    | typ_a' , EConst "Type" , exp'
                      when alpha_compare idl typ_a typ_a'
                      && alpha_compare idl
                            exp'
                            (beta_reduce idl 
                              (substitute idl id term1 exp)
                            ) 
                      -> ESigma ((id , typ_a) , exp)
                    | _ -> raise Type_error
            end
          | _ ->
            begin match (beta_reduce idl (compute_type_of_term ctx idl term)).desc with
              | EPi ((_ , typ_a) , _) ->
                  begin match beta_reduce idl (compute_type_of_term ctx idl term1) with
                    | typ when alpha_compare idl typ typ_a -> raise Unable_to_infer_type
                    | _ -> raise Type_error
                  end
              | _ -> raise Type_error
            end
        end
    | EPair _ -> raise Unable_to_infer_type
    | EFst term ->
        begin match (compute_type_of_term ctx idl term).desc with
          | ESigma ((_ , typ_a) , _) -> typ_a.desc
          | _ -> raise Type_error
        end
    | ESnd term ->
        begin match (compute_type_of_term ctx idl term).desc with
          | ESigma ((id , _) , exp) -> (substitute idl id { desc = EFst term ; loc = term.loc } exp).desc
          | _ -> raise Type_error
        end
    | ESigma ((id , typ_a) , exp) ->
        begin match in_context_opt id ctx with
            | Some _ ->
                let z = get_unused_ident idl in
                let exp_of_z = rename idl id z exp in
                (compute_type_of_term ctx idl { desc = ESigma ((z , typ_a) , exp_of_z) ; loc = term.loc }).desc
            | None ->
                let (ctx' , idl') = 
                  if id = "_" then (ctx , idl) 
                  else (((id , typ_a) :: ctx) , (id :: idl)) 
                in
                match
                  (beta_reduce idl (compute_type_of_term ctx idl typ_a)).desc ,
                  (beta_reduce idl' 
                    (compute_type_of_term ctx' idl' exp)).desc
                with
                  | EConst "Type" , EConst "Type" -> EConst "Type"
                  | _ -> raise Type_error
        end
    | ETaggedExpr (term , exp) ->
        if alpha_compare idl 
          (beta_reduce idl (compute_type_of_term ctx idl term))
          (beta_reduce idl exp)
          then exp.desc
        else raise Type_error
  in
  if !Config.verbose then begin
    Format.eprintf "type of %a is %a\n"
      Astprinter.pp_expr term
      Astprinter.pp_expr { desc = desc ; loc = Location.none }
  end;
  { desc = desc
  ; loc = term.loc
  }