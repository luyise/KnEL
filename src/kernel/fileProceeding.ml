open Ast
open Astprinter
open Constants
open Environment
open KnelState
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
    | Error _ -> state

(* La fonction proceed_reasonment prend les données d'une section de raisonement
  i.e.
      -> le nom du raisonement, parmi
            Lemma, Theorem
      -> le nom à donner au terme créer si on souhaite le sauvegarder,
            c'est un identifiant
      -> la sorte du machin à obtenir
      -> la liste de tactique pour y parvenir
      -> un mot clef de fin de raisonement, parmi
            Qed, Ongoing, Admitted

  Lorsque cette fonction est appelée, le knel_state devrait
  être dans l'état AllDone, ceci n'est pas vérifié lors de l'éxécution de cette fonction

             *)

let proceed_reasonment :
      knel_state 
  ->  beggining_tag 
  ->  ident option 
  ->  expr
  ->  tactic list 
  ->  ending_tag
  ->  knel_state
= fun state _ id_op goal_typ tacl end_tag ->
  let (goal_id : string) = match id_op with
    | None -> "unamed_goal"
    | Some id ->
        begin match in_context_opt id state.global_context with
          | None -> id
          | Some _ -> raise 
            (Wrong_declaration 
            ("Cannot name your target with the already existing name " ^ id))
        end
  in
  let ready_to_reason_state =
    { global_context = state.global_context
    ; environments = 
      [{ context = state.global_context
       ; used_ident = (List.map fst state.global_context) 
          @ (List.map fst constants)
       ; target = goal_typ }]
    ; status = InProof }
  in
  let final_state = execute_tac_list ready_to_reason_state tacl in
  match final_state.status with
      (* KnEL a rencontré un problème lors de la preuve, 
      il reste dans l'état courant *)
    | Error _ -> final_state
      (* l'utilisateur n'a pas atteint l'objectif,
        on regarde donc s'il souhaite l'admettre, 
        ou s'il considère que la preuve est en cours *)
    | InProof -> begin match end_tag , id_op with
        | Qed , _ -> 
            if !Config.html_view
            then
              Format.printf "<p style=\"color:#00FF00\">while working on %s, the reasonment was not finished, but you wrote QED, last state before the keyword: </p>\n%a\n"
              goal_id
              pp_knel_state final_state
            else
              Format.printf "\x1B[38;5;124mwhile working on %s, the reasonment was not finished, but you wrote QED, last state before the keyword: \x1B[39m\n%a\n"
              goal_id
              pp_knel_state final_state;
            raise (Wrong_declaration "The goal is not achieved !")
        | Ongoing , _ ->
            if !Config.html_view
            then
              Format.printf "<p>while working on %s, the reasonment was not finished, last state before giving up:</p>\n%a\n"
                goal_id
                pp_knel_state final_state
            else
              Format.printf "while working on %s, the reasonment was not finished, last state before giving up: \n%a\n"
                goal_id
                pp_knel_state final_state;
            { global_context = state.global_context
            ; environments = []
            ; status = AllDone }
        | Admitted , Some _ ->
            if !Config.html_view
            then
              Format.printf "<p style=\"color:#00FF00>\"/!\\ %s was admitted</p>\n"
                goal_id
            else
              Format.printf "\x1B[38;5;124m/!\\ %s was admitted\x1B[39m\n"
                goal_id;
            { global_context = (goal_id , goal_typ) :: state.global_context
            ; environments = []
            ; status = AllDone }
        | Admitted , None ->
            if !Config.html_view
            then
              Format.printf "<p style=\"color:#00FF00\">/!\\ An unamed goal has been admitted, this is bad but will have no effect because you didn't named it</p>\n"
            else
              Format.printf "\x1B[38;5;124m/!\\ An unamed goal has been admitted, this is bad but will have no effect because you didn't named it\x1B[39m\n";
            { global_context = state.global_context
            ; environments = []
            ; status = AllDone }
      end
    | AllDone -> begin match end_tag with
        | Qed ->
            if !Config.html_view
            then
              Format.printf "<p>%s succesfully achieved</p>\n"
                goal_id
            else
              Format.printf "%s succesfully achieved\n"
                goal_id;
            begin match id_op with
              | Some _ ->
                { global_context = (goal_id , goal_typ) :: state.global_context
                ; environments = []
                ; status = AllDone }
              | None ->
                { global_context = state.global_context
                ; environments = []
                ; status = AllDone }
            end
        | Admitted ->
            if !Config.html_view
            then
              Format.printf "<p style=\"color:#00FF00>/!\\ %s was admitted, but it seems like you didn't need to...</p>\n"
                goal_id
            else
              Format.printf "\x1B[38;5;124m/!\\ %s was admitted, but it seems like you didn't need to...\x1B[39m\n"
                goal_id;
            begin match id_op with
              | Some _ ->
                { global_context = (goal_id , goal_typ) :: state.global_context
                ; environments = []
                ; status = AllDone }
              | None ->
                { global_context = state.global_context
                ; environments = []
                ; status = AllDone }
            end
        | Ongoing ->
            if !Config.html_view
            then
              Format.printf "<p>while working on %s, the reasonment wasn't closed, but it seems like you could have type Qed instead. The last context before Ongoing keyword was:</p>\n%a\n"
                goal_id
                pp_knel_state final_state
            else
              Format.printf "while working on %s, the reasonment wasn't closed, but it seems like you could have type Qed instead. The last context before Ongoing keyword was: \n%a\n"
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
    | Error _ -> state
    | InProof -> failwith "\x1B[38;5;196mKnEL internal error, asked to execute a section while being InProof\x1B[39m"
    | AllDone -> begin match sec with
        | HypothesisSection ctx ->
            append_context state ctx
        | ReasoningSection (beg_tag , id_op , goal_typ , tacl , end_tag) ->
            proceed_reasonment state beg_tag id_op goal_typ tacl end_tag
      end

(* La fonction execute_file prend en argument un knel_file, i.e.
  une liste de sections se succédant dans le fichier .knl
  et l'execute *)

let execute_file : ?show:bool -> knel_file -> unit
= fun ?(show=true) file ->
  let fresh_state = new_knel_state () in
  try
    let final_state =
      List.fold_left 
        execute_section 
        fresh_state
        file
    in
    if show
    then
      if !Config.html_view
      then begin
        Format.printf "<p>File succesfully read, state of KnEL when reached end of file: </p>";
        Format.printf "<p><b style=\"color:#652A0E\">Status:</b> %a</p>\n\n"
          pp_status final_state.status;
        Format.printf "<h4 style=\"color:#9B673C\">Final context:</h4> \n%a\n"
          pp_context final_state.global_context
      end else begin
        Format.printf "File succesfully read, state of KnEL when reached end of file: \n\n";
        Format.printf "\x1B[38;5;130mStatus:\x1B[39m %a\n\n"
          pp_status final_state.status;
        Format.printf "\x1B[38;5;130mFinal context:\x1B[39m \n%a\n"
          pp_context final_state.global_context
      end;
  with
    | Wrong_declaration message ->
        if !Config.html_view
        then
          Format.fprintf Format.err_formatter "<p style=\"color:#FF0000\">Something went wrong when reading your .knl file: \n%s\n</p>"
            message
        else 
          Format.fprintf Format.err_formatter "\x1B[38;5;124mSomething went wrong when reading your .knl file: \n%s\n\x1B[39m"
            message