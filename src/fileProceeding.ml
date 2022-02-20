open Ast
open Environment
open KnelState
open Envprinter
open Knelprinter

(* La fonction append_context prend en argument un contexte
    [ ctx : context ]
  et, sous reserve que le knel_state ne soit pas dans un
  état d'erreur ou de preuve, l'ajoute au contexte global *)

exception Wrong_declaration of string

let append_context : knel_state -> context -> knel_state
= fun state ctx ->
  match state.status with
    | AllDone ->
        { global_context = ctx @ state.global_context 
        ; environments = [] 
        ; status = AllDone }
    | InProof -> raise (Wrong_declaration "Didn't expect a variable declaration now.")
    | Error -> state

(* La fonction proceed_reasonment prend les données d'une section de raisonement
  i.e.
      -> le nom du raisonement, parmi
            Lemma, Theorem
      -> le nom à donner au terme créer si on souhaite le sauvegarder,
            c'est un identifiant
      -> la sorte du machin à obtenir
      -> la liste de tactique pour y parvenir
      -> un mot clef de fin de raisonement, parmi
            QED, Ongoing, Admitted

  Lorsque cette fonction est appelée, le knel_state devrait
  être dans l'état AllDone, ceci n'est pas vérifié lors de l'éxécution de cette fonction

             *)

let proceed_reasonment :
      knel_state 
  ->  beggining_tag 
  ->  ident option 
  ->  sort
  ->  tactic list 
  ->  ending_tag
  ->  knel_state
= fun state _ id_op goal_sort tacl end_tag ->
  let (goal_id : string) = match id_op with
    | None -> "unamed_goal"
    | Some id ->
        begin match search_for_term id state.global_context with
          | None -> id
          | Some _ -> raise 
            (Wrong_declaration 
            ("Cannot name your target with the already existing name " ^ id))
        end
  in
  let ready_to_reason_state =
    { global_context = state.global_context
    ; environments = [{ context = state.global_context ; target = goal_sort }]
    ; status = AllDone }
  in
  let final_state = execute_tac_list ready_to_reason_state tacl in
  match final_state.status with
      (* KnEL a rencontré un problème lors de la preuve, 
      il reste dans l'état courant *)
    | Error -> final_state
      (* l'utilisateur n'a pas atteint l'objectif,
        on regarde donc s'il souhaite l'admettre, 
        ou s'il considère que la preuve est en cours *)
    | InProof -> begin match end_tag , id_op with
        | QED , _ -> 
            Format.printf "while working on %s, the reasonment was not finished, but you wrote QED, last state before the keyword: \n%a"
              goal_id
              pp_knel_state final_state;
            raise (Wrong_declaration "The goal is not achieved !")
        | Ongoing , _ ->
            Format.printf "while working on %s, the reasonment was not finished, last state before giving up: \n%a"
              goal_id
              pp_knel_state final_state;
            { global_context = state.global_context
            ; environments = []
            ; status = AllDone }
        | Admitted , Some _ ->
            Format.printf "/!\ %s was admitted"
              goal_id;
            { global_context = (goal_id , goal_sort) :: state.global_context
            ; environments = []
            ; status = AllDone }
        | Admitted , None ->
            Format.printf "/!\ An unamed goal has been admitted, this is bad but will have no effect because you didn't named it";
            { global_context = state.global_context
            ; environments = []
            ; status = AllDone }
      end
    | AllDone -> begin match end_tag with
        | QED ->
            Format.printf "%s succesfully achieved"
              goal_id;
            begin match id_op with
              | Some _ ->
                { global_context = (goal_id , goal_sort) :: state.global_context
                ; environments = []
                ; status = AllDone }
              | None ->
                { global_context = state.global_context
                ; environments = []
                ; status = AllDone }
            end
        | Admitted ->
            Format.printf "/!\ %s was admitted, but it seems like you didn't need to..."
              goal_id;
            begin match id_op with
              | Some _ ->
                { global_context = (goal_id , goal_sort) :: state.global_context
                ; environments = []
                ; status = AllDone }
              | None ->
                { global_context = state.global_context
                ; environments = []
                ; status = AllDone }
            end
        | Ongoing ->
            Format.printf "while working on %s, the reasonment wasn't closed, but it seems like you could have type QED instead. The last context before Ongoing keyword was: \n%a"
              goal_id
              pp_knel_state final_state;
            { global_context = state.global_context
            ; environments = []
            ; status = AllDone }
      end

(* La fonction execute_section prend en entrée un knel_state, une knel_section, l'execute depuis
  l'état argument, et renvoie le knel_state résultant *)

let execute_section : knel_state -> knel_section -> knel_state
= fun state sec ->
  match state.status with
    | Error -> state
    | InProof -> failwith "KnEL internal error, asked to execute a section while being InProof"
    | AllDone -> begin match sec with
        | HypothesisSection ctx ->
            append_context state ctx
        | ReasoningSection (beg_tag , id_op , goal_sort , tacl , end_tag) ->
            proceed_reasonment state beg_tag id_op goal_sort tacl end_tag
      end

(* La fonction execute_file prend en argument un knel_file, i.e.
  une liste de sections se succédant dans le fichier .knl
  et l'execute *)

let execute_file : knel_file -> unit
= fun file ->
  let fresh_state = new_knel_state () in
  try
    let final_state =
      List.fold_left 
        execute_section 
        fresh_state 
        file
    in
    Format.printf "File succesfully read, state of KnEL when reached end of file: \n";
    Format.printf "Status: %a\n\n"
      pp_status final_state.status;
    Format.printf "Final context: \n%a\n"
      pp_context final_state.global_context
  with
    | Wrong_declaration message ->
        Format.printf "Something went wrong when reading your .knl file: \n%s"
          message
