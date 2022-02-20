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

exception Invalid_tactic

let apply_base_tactic : env -> base_tactic -> env list
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

type tactic =
  | BaseTac of base_tactic
  | TryTac of tactic
  | DoTac of int * tactic
  | SeqTac of tactic * tactic
  | OrTac of tactic * tactic

let rec apply_tactic : env -> tactic -> env list
= fun e tac ->
  match tac with
    | BaseTac tac' -> apply_base_tactic e tac'
    | TryTac tac' -> begin
        try apply_tactic e tac' with
          | Invalid_tactic
          | Sort_error -> [ e ]
        end
    | DoTac (n , _) when n = 0 -> [ e ]
    | DoTac (n , tac') when n > 0 -> begin
        match apply_tactic e tac' with
          | [] -> raise Invalid_tactic
          | e0 :: e_tail -> (apply_tactic e0 (DoTac ((n-1) , tac'))) @ e_tail
        end
    | DoTac _ -> failwith "KnEL internal error, expected a positive argument for DoTac"
    | SeqTac (tac1 , tac2) -> begin
        match apply_tactic e tac1 with
          | [] -> raise Invalid_tactic
          | e0 :: e_tail -> (apply_tactic e0 tac2) @ e_tail
        end
    | OrTac (tac1 , tac2) -> begin
        try apply_tactic e tac1 with
          | Invalid_tactic
          | Sort_error -> apply_tactic e tac2
        end  