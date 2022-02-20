open Ast

type env =
  { context : (ident * sort) list
  ; target : sort
  }

type base_tactic =
  | IntroTac of ident             (* Former un terme de type s → t *)
  | ApplyTac of term              (* Passe d'un objectif t à un objectif s sachant
                                    l'existence de f : s → t dans le context *)
  | SplitTac                      (* Former un terme de type ×[ - ] *)
  | ProdRecTac of ident list      (* Appliquer le récurseur de ×, 
                                      pour introduire un terme du type ×[ - ] → t *)
  | ChooseTac of int              (* Former un terme de type +[ - ] *)
  | SumRecTac                     (* Appliquer le récurseur de +, 
                                    pour introduire un terme du type +[ - ] → t *)
  | ExactTac of term              (* Démontre un objectif en invoquant 
                                    une variable du contexte *)

type tactic =
  | SeqTac of tactic * tactic
  | OrTac of tactic * tactic
  | TryTac of tactic
  | RptTac of tactic
  | BaseTac of base_tactic

exception Invalid_tactic

let apply_tactic : env -> base_tactic -> env list
= fun e tac ->
  match tac , e.target with
    | IntroTac name , SFun (s , t) ->
        [ { context = (name , s) :: e.context
          ; target = t }
        ]
    | ApplyTac f_term , t -> begin
        match get_sort f_term e.context with
          | SFun (s , t') when t' = t -> 
              [ { context = e.context
                ; target = s }
              ]
          | _ -> raise Invalid_tactic
        end
    | SplitTac , SProd s_list ->
        List.map
          (fun s ->
            { context = e.context
            ; target = s }
          ) s_list
    | ProdRecTac names , SFun (SProd s_list , s') ->
        let rec ctx_extension s_list' names' acc =
          match s_list' , names' with
            | [] , [] -> acc
            | s :: s_tail , name :: names_tail ->
                ctx_extension s_tail names_tail ((name , s) :: acc)
            | _ -> raise Invalid_tactic
        in
        [ { context = (ctx_extension s_list names []) @ e.context
          ; target = s' }
        ]
    | ChooseTac n , SSum s_list ->
        let s = try List.nth s_list (n - 1) with
          | _ -> raise Invalid_tactic
        in
        [ { context = e.context
          ; target = s }
        ]
    | SumRecTac , SFun (SSum s_list , t) ->
        List.map 
          (fun s -> 
            { context = e.context
            ; target = SFun (s , t) }
          ) s_list
    | ExactTac expr , t ->
        if get_sort expr e.context = t then []
        else raise Invalid_tactic
    | _ -> raise Invalid_tactic
