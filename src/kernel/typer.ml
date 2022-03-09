open Parse
open Ast
open Constants
open Environment
open Renaming
open Substitution
open Alpha_renaming
open Beta_red

exception Unknown_ident of ident
exception Type_error
exception Invalid_context
exception Unable_to_infer_type

let rec get_info_from_path : expr_path -> expr -> expr =
fun path typ ->
  match path , typ.desc with
    | [] , _ -> typ
    | PFunSource :: path_tail , 
      EPi ((_ , y_typ) , _ , _)
      -> get_info_from_path path_tail y_typ
    | PFunNonDepTarget :: path_tail ,
      EPi (("_" , _) , targ_typ , _)
      -> get_info_from_path path_tail targ_typ
    | PFunDepTarget :: path_tail , 
      EPi ((y , y_typ) , y_targ_typ , path_op)
      -> get_info_from_path path_tail ({ desc = ELam ((y , y_typ) , y_targ_typ , path_op) ; loc = typ.loc })
    | PSigFst :: path_tail ,
      ESigma ((_ , y_typ) , _ , _)
      -> get_info_from_path path_tail y_typ
    | PSigNonDepSnd :: path_tail ,
      ESigma (("_" , _) , targ_typ , _)
      -> get_info_from_path path_tail targ_typ
    | PSigDepSnd :: path_tail , 
      ESigma ((y , y_typ) , y_targ_typ , path_op)
      -> get_info_from_path path_tail ({ desc = ELam ((y , y_typ) , y_targ_typ , path_op) ; loc = typ.loc })
    | _ -> raise Unable_to_infer_implicit_argument

(* /!\ la fonction compute_type_if_term doit être appellée avec l'ident list contenant le List.map fst du context *)

let rec compute_type_of_term : context -> beta_rule_type list -> ident list -> expr -> expr
= fun ctx brl idl term ->
  let desc =
  match term.desc with
    | EConst c ->
        compute_type_EConst c
    | EVar x ->
        compute_type_EVar x ctx
    | ELam ((x , x_typ) , exp_of_x , path_op) ->
        compute_type_ELam term x x_typ exp_of_x path_op ctx brl idl
    | EApp ({ desc = ELam ((x , _ ), term_of_x , Some path) ; loc = _ } , v) ->
        infer_implicit_argument x path term_of_x v ctx brl idl
    | EApp (exp1 , exp2) ->
        compute_type_EApp exp1 exp2 ctx brl idl
    | EPi ((id , typ_a) , exp , path_op) ->
        compute_type_EPi term id typ_a exp path_op ctx brl idl
    | EPair ((term1 , term2) , Some typ) ->
        compute_type_EPair_Some term term1 term2 typ ctx brl idl
    | EPair _ ->
        raise Unable_to_infer_type
    | EFst term1 ->
        compute_type_EFst term1 ctx brl idl
    | ESnd term1 ->
        compute_type_ESnd term term1 ctx brl idl
    | ESigma ((id , typ_a) , exp , path_op) ->
        compute_type_ESigma term id typ_a exp path_op ctx brl idl
  in
  if !Config.verbose then begin
    Format.eprintf "type of %a is %a\n"
      Astprinter.pp_expr term
      Astprinter.pp_expr { desc = desc ; loc = Location.none }
  end;
  { term with desc }

and compute_type_EConst : ident -> expr_desc
= fun c ->
  match
    (List.find_opt
      (function
        | c' , _ when c = c' -> true
        | _ -> false
      ) constants
    ) with
      | Some (_ , typ) -> typ.desc
      | None -> raise (Unknown_ident c)

and compute_type_EVar : ident -> context -> expr_desc
= fun x ctx ->
  match in_context_opt x ctx
    with
      | Some typ -> typ.desc
      | _ -> raise (Unknown_ident x)

and infer_implicit_argument :
     ident
  -> expr_path
  -> expr
  -> expr
  -> context
  -> beta_rule_type list
  -> ident list
  -> expr_desc
= fun x path term_of_x v ctx brl idl ->
  let extracted_term = get_info_from_path path (compute_type_of_term ctx brl idl v) in
  (substitute idl x extracted_term term_of_x).desc

and compute_type_ELam :
     expr
  -> ident
  -> expr 
  -> expr
  -> expr_path option
  -> context
  -> beta_rule_type list
  -> ident list
  -> expr_desc
= fun term x x_typ exp_of_x path_op ctx brl idl ->
  match in_context_opt x ctx with
    | Some _ ->
        let z = get_unused_ident idl in
        let exp_of_z = rename idl x z exp_of_x in
        (compute_type_of_term ctx brl idl { desc = ELam ((z , x_typ) , exp_of_z , path_op) ; loc = term.loc }).desc
    | None ->
      let (ctx' , idl') =
        if x = "_" then (ctx , idl) 
        else (((x , x_typ) :: ctx) , (x :: idl)) 
      in
      begin match
          (compute_type_of_term ctx brl idl x_typ).desc ,
          compute_type_of_term ctx' brl idl' exp_of_x
        with
          | _ , typ_of_exp_of_x ->
              EPi ((x , x_typ) , typ_of_exp_of_x , path_op)
      end

and compute_type_EApp : expr -> expr -> context -> beta_rule_type list -> ident list -> expr_desc
= fun exp1 exp2 ctx brl idl ->
  match
    (beta_reduce idl brl (compute_type_of_term ctx brl idl exp1)).desc ,
    beta_reduce idl brl (compute_type_of_term ctx brl idl exp2)
  with
    | EPi ((id , id_typ) , typ_of_exp_of_id , _) , exp2_typ
      when
        alpha_compare idl id_typ exp2_typ 
        -> (substitute idl id exp2 typ_of_exp_of_id).desc
    | _ -> raise Type_error

and compute_type_EPi : 
     expr 
  -> ident
  -> expr
  -> expr
  -> expr_path option
  -> context
  -> beta_rule_type list
  -> ident list
  -> expr_desc 
= fun term id typ_a exp path_op ctx brl idl ->
  match in_context_opt id ctx with
    | Some _ ->
        let z = get_unused_ident idl in
        let exp_of_z = rename idl id z exp in
        (compute_type_of_term ctx brl idl { desc = EPi ((z , typ_a) , exp_of_z , path_op) ; loc = term.loc }).desc
    | None ->
        let (ctx' , idl') = 
          if id = "_" then (ctx , idl) 
          else (((id , typ_a) :: ctx) , (id :: idl)) 
        in
        match
          (beta_reduce idl brl (compute_type_of_term ctx brl idl typ_a)).desc ,
          (beta_reduce idl brl (compute_type_of_term ctx' brl idl' exp)).desc
        with
          | EApp ({ desc = EConst "Type" ; _ }
              , { desc = EVar x ; _ }) ,
            EApp ({ desc = EConst "Type" ; _ }
              , { desc = EVar y ; _ })
            when x = y ->
              EApp ({ desc = EConst "Type" ; loc = Location.none } 
              , { desc = EVar x ; loc = Location.none })
          | EConst "Type_∞",  (* A modifier... *)
            EConst "Type_∞"
            -> EConst "Type_∞"
          | EConst "Type_∞",  (* A modifier... *)
            EVar "_"
            -> EVar "_"
          | EVar "_",  (* A modifier... *)
            EConst "Type_∞"
            -> EVar "_"
          | EVar "_",  (* A modifier... *)
            EVar "_"
            -> EVar "_"
          | _ -> raise Type_error

and compute_type_EPair_Some : 
     expr 
  -> expr
  -> expr
  -> expr
  -> context
  -> beta_rule_type list
  -> ident list
  -> expr_desc
= fun term term1 term2 typ ctx brl idl ->
  let typ' = beta_reduce idl brl typ in
  match typ'.desc with
    | ELam ((id , typ_a) , exp , None) ->
      begin match in_context_opt id ctx with
        | Some _ ->
            let z = get_unused_ident idl in
            let exp_of_z = rename idl id z exp in
            (compute_type_of_term ctx brl idl
              { desc = EPair ((term1 , term2) , Some { desc = ELam ((z , typ_a) , exp_of_z , None) ; loc = term.loc })
              ; loc = term.loc }).desc
        | None ->
            let (ctx' , idl') =
              if id = "_" then (ctx , idl) 
              else (((id , typ_a) :: ctx) , (id :: idl))
            in
            match
              beta_reduce idl brl (compute_type_of_term ctx brl idl term1) ,
              (compute_type_of_term ctx' brl idl' exp) ,
              beta_reduce idl brl (compute_type_of_term ctx brl idl term2)
            with
              | typ_a' ,
                _ ,
                exp'
                when alpha_compare idl typ_a typ_a'
                && alpha_compare idl
                      exp'
                      (beta_reduce idl brl 
                        (substitute idl id term1 exp)
                      ) 
                -> ESigma ((id , typ_a) , exp , None)
              | _ -> raise Type_error
      end
    | _ ->
      begin match (beta_reduce idl brl (compute_type_of_term ctx brl idl term)).desc with
        | EPi ((_ , typ_a) , _ , _) ->
            begin match beta_reduce idl brl (compute_type_of_term ctx brl idl term1) with
              | typ when alpha_compare idl typ typ_a -> raise Unable_to_infer_type
              | _ -> raise Type_error
            end
        | _ -> raise Type_error
      end

and compute_type_EFst : expr -> context -> beta_rule_type list -> ident list -> expr_desc
= fun term1 ctx brl idl ->
  match (compute_type_of_term ctx brl idl term1).desc with
    | ESigma ((_ , typ_a) , _ , _) -> typ_a.desc
    | _ -> raise Type_error

and compute_type_ESnd : expr -> expr -> context -> beta_rule_type list -> ident list -> expr_desc
= fun term term1 ctx brl idl ->
  match (compute_type_of_term ctx brl idl term1).desc with
    | ESigma ((id , _) , exp , _) -> (substitute idl id { desc = EFst term1 ; loc = term.loc } exp).desc
    | _ -> raise Type_error

and compute_type_ESigma : 
     expr
  -> ident
  -> expr
  -> expr
  -> expr_path option
  -> context
  -> beta_rule_type list
  -> ident list
  -> expr_desc
= fun term id typ_a exp path_op ctx brl idl ->
    match in_context_opt id ctx with
      | Some _ ->
          let z = get_unused_ident idl in
          let exp_of_z = rename idl id z exp in
          (compute_type_of_term ctx brl idl { desc = ESigma ((z , typ_a) , exp_of_z , path_op) ; loc = term.loc }).desc
      | None ->
          let (ctx' , idl') = 
            if id = "_" then (ctx , idl) 
            else (((id , typ_a) :: ctx) , (id :: idl)) 
          in
          match
            (beta_reduce idl brl (compute_type_of_term ctx brl idl typ_a)).desc ,
            (beta_reduce idl' brl
              (compute_type_of_term ctx' brl idl' exp)).desc
          with
            | EApp ({ desc = EConst "Type" ; _ } 
              , { desc = EVar x ; _ }) ,
            EApp ({ desc = EConst "Type" ; _ }
              , { desc = EVar y ; _ })
            when x = y ->
              EApp ({ desc = EConst "Type" ; loc = Location.none } 
              , { desc = EVar x ; loc = Location.none })
            | EConst "Type_∞",  (* A modifier... *)
              EConst "Type_∞"
              -> EConst "Type_∞"
            | EConst "Type_∞",  (* A modifier... *)
              EVar "_"
              -> EVar "_"
            | EVar "_",  (* A modifier... *)
              EConst "Type_∞"
              -> EVar "_"
            | EVar "_",  (* A modifier... *)
              EVar "_"
              -> EVar "_"
            | _ -> raise Type_error