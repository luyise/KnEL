open Alpha_renaming
open Ast
open Beta_red
open Environment
open Renaming
open Substitution
open Typer

exception Invalid_tactic

let apply_base_tactic : env -> base_tactic -> env list
= fun e tac ->
  match tac , e.target with
    | IntroTac id , EPi ((x , typ) , typ_over_typ) ->
        begin match in_context_opt id e.context with
          | Some _ -> raise Invalid_tactic
          | None ->
              let typ_over_typ' = rename e.used_ident x id typ_over_typ in
              [ { context = (id , typ) :: e.context
                ; used_ident = id :: e.used_ident
                ; target = typ_over_typ' }
              ]
        end
    | ApplyTac f_term , typ -> begin
        match beta_reduce e.used_ident 
          (compute_type_of_term e.context e.used_ident f_term) 
          with
          | EPi ((x , s) , typ')
            when alpha_compare e.used_ident
              (beta_reduce e.used_ident typ) 
              (beta_reduce e.used_ident typ')
              && not (List.mem x (get_varlib [] typ')) -> 
              [ { context = e.context
                ; used_ident = e.used_ident
                ; target = s }
              ]
          | _ -> raise Invalid_tactic
        end
    | SplitTac term , ESigma ((x , typ) , typ_over_typ) ->
        let term_typ = beta_reduce e.used_ident 
          (compute_type_of_term e.context e.used_ident term) in
        let typ' = beta_reduce e.used_ident 
          (compute_type_of_term e.context e.used_ident typ) in
        if alpha_compare e.used_ident term_typ typ' then
          [ { context = e.context
            ; used_ident = e.used_ident
            ; target = (substitute e.used_ident x term typ_over_typ) }
          ]
        else raise Invalid_tactic
    | SigmaRecTac , EPi ((p , ESigma ((x , typ) , typ_over_typ)) , expr_of_p) ->
        let y = get_unused_ident (x :: e.used_ident) in
        [ { context = e.context
          ; used_ident = e.used_ident
          ; target = EPi ((x , typ) , EPi ((y , typ_over_typ), EApp (expr_of_p , (EPair ((EVar x , EVar y), Some (ESigma ((x , typ) , typ_over_typ))))))) }
        ]
    | ExactTac exp , t ->
        let typ = beta_reduce e.used_ident (compute_type_of_term e.context e.used_ident exp) in
        let t' = beta_reduce e.used_ident t in
        if alpha_compare e.used_ident t' typ then []
        else raise Invalid_tactic
    | _ -> raise Invalid_tactic

let rec apply_tactic : env -> tactic -> env list
= fun e tac ->
  match tac with
    | BaseTac tac' -> apply_base_tactic e tac'
    | TryTac tac' -> begin
        try apply_tactic e tac' with
          | Invalid_tactic
          | Type_error -> [ e ]
        end
    | DoTac (n , _) when n = 0 -> [ e ]
    | DoTac (n , tac') when n > 0 -> begin
        match apply_tactic e tac' with
          | [] -> raise Invalid_tactic
          | e0 :: e_tail -> (apply_tactic e0 (DoTac ((n-1) , tac'))) @ e_tail
        end
    | DoTac _ -> failwith "\x1B[38;5;196mKnEL internal error, expected a positive argument for DoTac\x1B[39m"
    | SeqTac (tac1 , tac2) -> begin
        match apply_tactic e tac1 with
          | [] -> raise Invalid_tactic
          | e0 :: e_tail -> (apply_tactic e0 tac2) @ e_tail
        end
    | OrTac (tac1 , tac2) -> begin
        try apply_tactic e tac1 with
          | Invalid_tactic
          | Type_error -> apply_tactic e tac2
        end  