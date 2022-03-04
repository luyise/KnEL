open Parse
open Ast
open Environment
open Typer
open Base_tactics

type status =
  | AllDone
  | InProof
  | Error of string
  
type knel_state = 
  { global_context : context
  ; definitions : (ident * expr) list
  ; environments : env list
  ; status : status
  }

(* La fontion new_knel_state : unit -> knel_state 
  crée un knel state tout neuf, de contexte vide,
  sans objectifs courant *)

let new_knel_state : context -> (ident * expr) list -> knel_state
= fun ctx def ->
  { global_context = ctx
  ; definitions = def
  ; environments = []
  ; status = AllDone }

(* La fonction execute_tac_list applique, sous reserve qu'il n'y ait
  pas d'erreur déclanchée, toutes les tactiques de la liste fournie 
  depuis un knel_state, puis renvoie le knel_state obtenu *)

let rec execute_tac_list : knel_state -> tactic list -> knel_state
= fun state tac_list ->
  match state.status with 
    | Error (_) -> state
    | _ -> begin
      match state.environments , tac_list with
        | _ , [] -> state
        | e :: e_tail , (tac :: tac_tail) ->
            let generated_envs , st =
              try (apply_tactic e tac) , state.status with
                | Invalid_tactic ->
                    [ e ] , Error "Invalid tactic"
                | Unknown_ident ->
                    [ e ] , Error "Unknown ident"
                | Type_error ->
                    [ e ] , Error "Type error"
            in
            let new_env_list = (generated_envs @ e_tail) in
            begin match new_env_list with
              | [] ->
                  { global_context = state.global_context
                  ; definitions = state.definitions
                  ; environments = []
                  ; status = AllDone }
              | _ -> 
                  execute_tac_list 
                    { global_context = state.global_context
                    ; definitions = state.definitions
                    ; environments = new_env_list
                    ; status = st }
                    tac_tail
            end
        | [] , _ ->
            { global_context = state.global_context 
            ; definitions = state.definitions
            ; environments = [] 
            ; status = Error "No goal remaining" }
    end