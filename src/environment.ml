open Ast

type env =
  { context : (ident * sort) list
  ; target : sort
  }

type tactic =
  | IntroTac of ident             (* Former un terme de type s → t *)
  | ApplyTac of ident             (* Passe d'un objectif t à un objectif s sachant
                                    l'existence de f : s → t dans le context *)
  | SplitTac                      (* Former un terme de type ×[ - ] *)
  | ProductRecTac of ident list   (* Appliquer le récurseur de ×, 
                                      pour introduire un terme du type ×[ - ] → t *)
  | ChooseTac of int              (* Former un terme de type +[ - ] *)
  | SumRecTac                     (* Appliquer le récurseur de +, 
                                    pour introduire un terme du type +[ - ] → t *)
  | ExactTac of term              (* Démontre un objectif en invoquant 
                                    une variable du contexte *)

exception Invalid_tactic

let apply_tactic : env -> tactic -> env list
= fun e tac ->
  match tac , e.target with
    | IntroTac name , SFun (s , t) ->
        [ { context = (name , s) :: e.context
          ; target = t }
        ]
    | ApplyTac name , t ->
        match search_for_term name e.context with
          | Some (SFun (s , t')) when t' = t -> 
              [ { context = e.context
                ; target = s }
              ]
          | _ -> raise Invalid_tactic
    | SplitTac , SProd s_list ->
        List.map
          (fun s ->
            { context = e.context
            ; target = s }
          ) s_list
    | ProductRedTac names , SFun (SProd s_list , t) ->
        let rec ctx_extension s_list' names' acc =
          match s_list' , names' with
            | [] , [] -> acc
            | s :: s_tail , name :: names_tail ->
                ctx_extension s_tail names_tail ((s , name) :: acc)
            | _ -> raise Invalid_tactic
        in
        [ { context = (ctx_extension s_list names []) @ e.context
          ; target = s }
        ]
    | ChooseTac n , SSum s_list ->
        let s = try List.nth s_list n with
          | _ -> raise Invalid_tactic
        in
        [ { context = e.context
          ; target = s }
        ]
    | SumRecTac , SFun (SSum s_list , t) ->
        List.map 
          (fun s -> 
            [ { context = e.context
            ; target = SFun (s , t) }
            ]
          ) s_list
    | ExactTac expr , t ->
        if get_sort expr e.context = t then []
        else raise Invalid_tactic
    | _ -> assert false
