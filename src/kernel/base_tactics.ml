open Parse
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
  let idl = e.used_ident in
  let brl = e.beta_rules in
  let ctx = e.context in
  match tac , e.target.desc with
    | IntroTac id , EPi ((x , typ) , typ_over_typ , _) ->
        begin match in_context_opt id ctx with
          | Some _ -> raise Invalid_tactic
          | None ->
              if id = "_" then raise Invalid_tactic
              else begin
                let typ_over_typ' = rename idl x id typ_over_typ in
                [ { context = (id , typ) :: ctx
                  ; definitions = e.definitions
                  ; beta_rules = brl
                  ; used_ident = id :: idl
                  ; target = typ_over_typ' }
                ]
              end
        end
    | ApplyTac f_term , _ -> begin
        match (beta_reduce idl brl
          (compute_type_of_term ctx brl idl f_term)).desc
          with
          | EPi ((x , s) , typ' , _)
            when alpha_compare idl
              (beta_reduce idl brl e.target)
              (beta_reduce idl brl typ')
              && not (List.mem x (get_varlib [] typ')) -> 
              [ { e with target = s } ]
          | _ -> raise Invalid_tactic
        end
    | SigmaRecTac , EPi ((id , { desc = ESigma ((x , typ) , typ_over_typ , None) ; _ }) , exp_of_p , _) ->
        let typ' = beta_reduce idl brl typ in
        let typ_over_typ' = beta_reduce idl brl typ_over_typ in
        let typ_of_exp_of_p = beta_reduce idl brl (compute_type_of_term ctx brl idl exp_of_p) in
        if (alpha_compare idl 
          { desc = EPi (("p", { desc = ESigma ((x , typ') , typ_over_typ' , None) ; loc = Location.none }) , { desc = EConst "Type" ; loc = Location.none } , None) 
          ; loc = Location.none } typ_of_exp_of_p) then begin
          if id = "_" then begin
            [ { e with 
                target = { desc = EPi (("_" , typ) , { desc = EPi (("_" , typ_over_typ), exp_of_p , None) ; loc = Location.none } , None) ; loc = Location.none }
            } ]
          end else begin
            let y = get_unused_ident (x :: idl) in
            [ { e with
                target = 
                { desc = EPi ((x , typ) , 
                  { desc = EPi ((y , typ_over_typ), 
                    { desc = EApp (exp_of_p , 
                      { desc = EPair (
                          ( { desc = EVar x ; loc = Location.none } ,
                            { desc = EVar y ; loc = Location.none }
                          ) ,
                          Some
                            { desc = ESigma ((x , typ) , typ_over_typ , None)
                            ; loc = Location.none
                            })
                      ; loc = Location.none
                      })
                    ; loc = Location.none
                    } , None )
                  ; loc = Location.none 
                  } , None )
                ; loc = Location.none
                }
            } ]
          end
      end else raise Invalid_tactic
    | ExactTac exp , _ ->
        let typ = beta_reduce idl brl (compute_type_of_term ctx brl idl exp) in
        let t' = beta_reduce idl brl e.target in
        if alpha_compare idl t' typ then []
        else raise Invalid_tactic
    | DefineTac (id, term, typ) , _ ->
        begin match in_context_opt id ctx with
          | Some _ -> raise Invalid_tactic
          | None ->
            let term_typ = beta_reduce idl brl (compute_type_of_term ctx brl idl term) in
            let typ' = beta_reduce idl brl typ in
            if alpha_compare idl term_typ typ' then
              [ { context = (id , typ') :: ctx
              ; definitions = (id , term) :: e.definitions
              ; beta_rules = brl
              ; used_ident = id :: idl
              ; target = e.target }
              ]
            else raise Type_error
        end
    | UnfoldTac id , _ ->
        let term = match in_definitions_opt id e.definitions
          with
            | Some term' -> term'
            | None -> raise Invalid_tactic
        in
        let rewritten_target = substitute idl id term e.target in
        [ { e with target = rewritten_target }
        ]
    | ReduceTac , _ ->
        let reduced_goal = beta_reduce idl brl e.target in
        [ { e with target = reduced_goal }
        ]
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