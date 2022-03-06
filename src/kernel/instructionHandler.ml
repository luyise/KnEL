open Parse

open Alpha_renaming
open Ast
open Base_tactics
open Beta_red
open Environment
open KnelState
open Typer

(* Fonctions auxiliaires *)
(* Ajoute un terme au contexte courant *)
let append_context : knel_state -> (ident * expr) -> knel_state
= fun state (id , exp) ->
  if List.mem id state.used_ident then
    { state with status = Error (id^" is already used!") }
  else begin try
    let _ = compute_type_of_term state.global_context state.beta_rules state.used_ident exp in
    { state with
      global_context = (id , exp) :: state.global_context
    ; used_ident = id :: state.used_ident }
  with
    | Unknown_ident ->
      { state with status = Error ("Unknown ident when type checking "^id^" declaration") }
    | Type_error ->
      { state with status = Error ("Type error occured when type checking "^id) }
  end

(* Vérification de l'admissibilité d'une commande par le noyau *)

let check_valid_instruction : knel_state -> instruction -> knel_state
= fun state inst ->
  match inst , state.status with
    | IDefine _ , InProof -> { state with status = Error "Cannot start a definition while beeing in proof" }
    | ITacDecl _ , InProof -> { state with status = Error "Cannot accept a tactic definition while beeing in proof" }
    | IHypothesis _ , InProof -> { state with status = Error "Cannot accept an hypothesis section while beeing in proof" }
    | IOpen _ , InProof -> { state with status = Error "Cannot open a .knl file while beeing in proof" }
    | IBackward , _ -> { state with status = Error "KnEL wasn't supposed to receive this command..." }
    | IBeginProof _ , InProof -> { state with status = Error "Cannot start a new proof while beeing in proof" }
    | ITactic _ , AllDone -> { state with status = Error "Cannot apply a tactic while not proving something" }
    | IDropProof , AllDone -> { state with status = Error "Cannot drop a proof, because there is no proof now" }
    | IFullProof _ , InProof -> { state with status = Error "Cannot read a proof while beeing in proof" }
    | IBetaRuleDecl _ , InProof -> { state with status = Error "Cannot accept a beta-rule declaration while beeing in proof" }
    | _ , _ -> state

(* Gestion de chaque commande par le noyau *)

(* Définit un nouveau terme et l'ajoute à l'environnement global *)
let execute_IDefine : knel_state -> ident -> expr -> expr -> knel_state 
= fun state name term typ ->
  if List.mem name state.used_ident then
    { state with status = Error (name^" is already used!") }
  else begin try
    let typ' = beta_reduce state.used_ident state.beta_rules
      (compute_type_of_term state.global_context state.beta_rules state.used_ident term)
    in
    if alpha_compare state.used_ident typ' typ then begin
      if state.prompt_enabled then begin
        if !Config.html_view then begin
          Format.printf "%s was defined<br>"
            name
        end else begin
          Format.printf "%s was defined\n"
            name
        end
      end;
      { state with
        global_context = (name , typ) :: state.global_context
      ; used_ident = name :: state.used_ident
      ; definitions = (name , term) :: state.definitions
      }
    end else { state with status = Error ("Incompatible types when defining "^name) }
  with
    | Unknown_ident ->
      { state with status = Error ("Unknown ident when type checking "^name^" definition") }
    | Type_error ->
      { state with status = Error ("Type error occured when type checking "^name) }
  end

(* Défini une nouvelle tactique *)
let execute_ITacDecl : knel_state -> knel_state
= fun state -> state (* TODO *)

let rec execute_IHypothesis : knel_state -> context -> knel_state
= fun state ctx ->
  match ctx with
    | [] -> state
    | id_and_expr :: ctx_tail ->
        let state' = append_context state id_and_expr in 
        begin match state'.status with
          | Error _ -> state'
          | _ -> execute_IHypothesis state' ctx_tail
        end

let execute_IOpen : knel_state -> knel_state
= fun state -> state (* TODO *)

let execute_IBackward : knel_state -> knel_state
= fun state -> state (* TODO *)

let execute_IBeginProof : 
     knel_state
  -> ident option
  -> expr
  -> knel_state
= fun state id_op goal_typ ->
  begin try
    let _ = match id_op with
      | Some id when List.mem id state.used_ident ->
          raise (Ident_conflict id)
      | _ -> ()
    in
    let _ = compute_type_of_term
      state.global_context
      state.beta_rules
      state.used_ident
      goal_typ
    in
    let fresh_envl =
      [ { context = state.global_context
        ; definitions = state.definitions
        ; beta_rules = state.beta_rules
        ; used_ident = state.used_ident
        ; target = goal_typ
        } ]
    in
    { state with
      environments = fresh_envl
    ; status = InProof
    }
  with
    | Ident_conflict id ->
      { state with status = Error (id^" is already used!") }
    | Unknown_ident ->
      { state with status = Error ("Unknown ident when type checking goal") }
    | Type_error ->
      { state with status = Error ("Type error occured when type checking goal") }
  end

let execute_ITactic : knel_state -> tactic -> knel_state
= fun state tac ->
  match state.environments with
    | e :: e_tail ->
      begin try
        let generated_envs = apply_tactic e tac in
        { state with environments = generated_envs @ e_tail }
      with
        | Invalid_tactic -> 
            { state with status = Error ("Invalid tactic") }
        | Unknown_ident ->
            { state with status = Error ("Unknown ident when executing tactic") }
        | Type_error ->
            { state with status = Error ("Type error when executing tacting") }
      end
    | [] -> { state with status = Error ("Cannot execute a tactic, because there is no more goal") }

let execute_IDropProof : knel_state -> knel_state
= fun state ->
  if state.prompt_enabled then begin
    if !Config.html_view then
      Format.printf "proof abborted!<br>"
    else
      Format.printf "proof abborted!\n"
  end;
  { state with
    environments = []
  ; status = AllDone }

let execute_IFullProof :
     knel_state
  -> beggining_tag
  -> ident option
  -> expr
  -> tactic list
  -> ending_tag
  -> knel_state
= fun state _ id_op goal_typ tacl end_tag ->
  let ready_to_reason_state = execute_IBeginProof state id_op goal_typ in
  begin try
    let (goal_id : string) = match id_op with
      | None -> "unamed_goal"
      | Some id ->
          if List.mem id state.used_ident then
            raise (Ident_conflict id)
          else id
    in
  match ready_to_reason_state.status with
    | AllDone -> failwith "KnEL internal error: wasn't supposed to get a AllDone status after starting a proof section"
    | Error _ ->
        begin if !Config.html_view then
          Format.printf "an error occured while beggining the proof %s!<br>"
            goal_id
        else
          Format.printf "an error occured while beggining the proof %s!\n"
            goal_id
        end;
        { state with prompt_enabled = false }
    | InProof ->
        let final_state =
          List.fold_left
            execute_ITactic
            ready_to_reason_state
            tacl
        in 
        begin match final_state.status , final_state.environments , end_tag with
          | AllDone , _ , _ -> failwith "KnEL internal error: wasn't supposed to get a AllDone status after processed a tactic list"
          | Error _ , _ , _ ->
              begin if !Config.html_view then
                Format.printf "an error occured while checking the proof of %s!<br>"
                  goal_id
              else
                Format.printf "an error occured while checking the proof of %s!\n"
                  goal_id
              end;
              state
          | InProof , _ , Ongoing ->
              if state.prompt_enabled then begin
                if !Config.html_view then
                  Format.printf "proof aborted<br>"
                else
                  Format.printf "proof aborted\n"
              end;
              state
          | InProof , [] , Qed ->
              if state.prompt_enabled then begin
                if !Config.html_view then begin
                  Format.printf "%s succesfully achieved<br>"
                    goal_id
                end else begin
                  Format.printf "%s succesfully achieved\n"
                    goal_id
                end
              end;
              begin match id_op with
                | Some _ ->
                  { state with
                    global_context = (goal_id , goal_typ) :: state.global_context
                  ; used_ident = goal_id :: state.used_ident
                  ; definitions = state.definitions
                  ; status = AllDone
                  }
                | None -> state
              end
          | InProof , _ , Qed ->
              begin if !Config.html_view then begin
                  Format.printf "<p style=\"color:#922B21\">while working on %s, the reasonment was not finished, but you wrote QED</p><br>"
                    goal_id
                end else begin
                  Format.printf "\x1B[38;5;124mwhile working on %s, the reasonment was not finished, but you wrote QED, last state before the keyword: \x1B[39m\n"
                    goal_id
                end
              end;
              { state with status = Error "Cannot close the proof" }
          | InProof , _ , Admitted ->
              begin  if !Config.html_view then
                  Format.printf "<p style=\"color:#922B21\">/!\\ A goal has been admitted</p>\n"
                else
                  Format.printf "\x1B[38;5;124m/!\\ A goal has been admitted\x1B[39m\n"
              end;
              begin match id_op with
                | Some _ ->
                  { state with
                    global_context = (goal_id , goal_typ) :: state.global_context
                  ; used_ident = goal_id :: state.used_ident
                  ; definitions = state.definitions
                  ; status = AllDone
                  }
                | None -> state
              end
        end
  with
    | Ident_conflict id -> { state with status = Error (id^" is already used!") }
  end

let execute_IBetaRuleDecl : knel_state -> beta_rule_type -> knel_state
= fun state rule ->
  { state with beta_rules = rule :: state.beta_rules }

(* execute_instruction prend en entrée un knel_state, une instruction,
  exécute l'instruction en appellant la fonction de gestion associée, 
  et renvoie le knel_state obtenu après exécution de l'instruction. *)

let execute_instruction : knel_state -> instruction -> knel_state
= fun state inst ->
  (* On vérifie si l'instruction donnée est recevable en l'état *)
  let state = check_valid_instruction state inst in
  match state.status with 
    | Error _ -> state 
    | _ ->
        begin match inst with
          | IDefine (name , typ , term)
            -> execute_IDefine state name term typ
          | ITacDecl (_ , _ , _)
            -> let _ = execute_ITacDecl state in failwith "TO_DO"
          | IHypothesis ctx
            -> execute_IHypothesis state ctx
          | IOpen (_ , _ , _)
            -> let _ = execute_IOpen state in failwith "TO_DO"
          | IBackward
            -> let _ = execute_IBackward state in failwith "TO_DO"
          | IBeginProof (id_op , goal_typ)
            -> execute_IBeginProof state id_op goal_typ
          | ITactic tac
            -> execute_ITactic state tac
          | IDropProof
            -> execute_IDropProof state
          | IFullProof (beg_tag , id_op , goal_typ , tacl , end_tag)
            -> execute_IFullProof state beg_tag id_op goal_typ tacl end_tag
          | IBetaRuleDecl rule
            -> execute_IBetaRuleDecl state rule
        end
