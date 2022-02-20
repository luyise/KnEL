open Ast
open Environment

type status =
  | AllDone
  | InProof
  | Error
  
type knel_state = env list * status

let rec execute_tac_list : knel_state -> tactic list -> knel_state
= fun state tac_list ->
  if snd state = Error then state
  else begin
    match fst state , tac_list with
      | _ , [] -> state
      | (e :: e_tail) , (tac :: tac_tail) ->
          let generated_envs , st =
            try (apply_tactic e tac) , snd state with
              | Invalid_tactic
              | Unknown_variable
              | Sort_error ->
                  [ e ] , Error
          in
          let new_env_list = (generated_envs @ e_tail) in
          begin match new_env_list with
            | [] -> ([] , AllDone)
            | _ -> execute_tac_list (new_env_list , InProof) tac_tail
          end
      | [] , _ -> ([] , Error)
  end