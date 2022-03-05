open Parse
open Ast
open Environment
open Typer
open Base_tactics
open Beta_red
open Constants

type status =
  | AllDone
  | InProof
  | Error of string

type knel_state =
    (* contexte global, commun à tous les environnements de preuves *)
  { global_context : context
    (* liste des identifiants déjà utilisés, qu'il n'est pas souhaitable d'emprunter pour
      nommer de nouveaux termes ou variables *)
  ; used_ident : ident list
    (* liste de règles de β-réductions, déclarées par l'utilisateur ou natives *)
  ; beta_rules : beta_rule_type list
    (* liste de termes définis par l'utilisateur, avec leur λ-terme associé *)
  ; definitions : (ident * expr) list
    (* liste des environnement de preuves en cours d'utilisation *)
  ; environments : env list
    (* option permettant de savoir si on doit renvoyer de l'information à instant donné ou non *)
  ; prompt_enable : bool
    (* description synthétique de l'état du noyau :
      correspond à l'action en cours d'éxecution, ou à une erreur *)
  ; status : status
  }

(* La fontion new_knel_state : unit -> knel_state 
  crée un knel state tout neuf, de contexte vide,
  sans objectifs courant *)

let new_knel_state : context -> (ident * expr) list -> knel_state
= fun ctx def ->
  { global_context = ctx
  ; used_ident = (List.map fst ctx) @ (List.map fst constants)
  ; beta_rules = primitive_beta_rules
  ; definitions = def
  ; environments = []
  ; prompt_enabled = true
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
                  { state with 
                    environments = []
                  ; status = AllDone }
              | _ -> 
                  execute_tac_list 
                    { state with
                      environments = new_env_list
                    ; status = st }
                    tac_tail
            end
        | [] , _ ->
            { state with status = Error "No goal remaining" }
    end