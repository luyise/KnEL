open Parse

open Alpha_renaming
open Ast
open Astprinter
open Beta_red
open Constants
open Environment
open Envprinter
open InstructionHandler
open KnelState
open Knelprinter
open Typer

let execute_section : knel_state -> knel_section -> knel_state
= fun state sec -> 
match sec with
  | HypothesisSection ctx ->
      execute_instruction state (IHypothesis ctx)
  | ReasoningSection (beg_tag , id_op , goal_typ , tacl , end_tag) ->
    begin match end_tag with
      | Ongoing ->
          let (goal_id : string) = match id_op with
            | None -> "unamed_goal"
            | Some id -> id
          in
          let final_state =
            List.fold_left 
              execute_instruction
              state
              ((IBeginProof (id_op , goal_typ))
              :: (List.map (fun tac -> ITactic tac) tacl))
          in
          if state.prompt_enabled then begin
            if !Config.html_view then begin
              Format.printf "reasoning about %s:<br>%a<br>"
                goal_id
                pp_knel_state final_state
            end else begin
              Format.printf "reasoning about %s:\n%a\n"
                goal_id
                pp_knel_state final_state
            end
          end;
          { state with prompt_enabled = false }
      | _ ->
          execute_instruction
            state
            (IFullProof (beg_tag , id_op , goal_typ , tacl , end_tag))
    end
  | DefinitionSection (name , exp , typ) ->
      execute_instruction state (IDefine (name , exp , typ))
  | BetaRuleDeclSection rule ->
      execute_instruction state (IBetaRuleDecl rule)
  | OpenSection (str1 , str2 , expl) ->
      execute_instruction state (IOpen (str1 , str2 , expl))
  | TacDeclSection (name , tac_term , tac_typ) ->
      execute_instruction state (ITacDecl (name , tac_term , tac_typ))

let rec execute_section_list : knel_state -> knel_file -> knel_state
= fun state file -> 
  match file with
    | [] -> state
    | sec :: file_tail ->
        let state' = execute_section state sec in
        begin match state'.status with
          | Error _ -> state'
          | _ -> execute_section_list state' file_tail
        end

let print_error_op : knel_state -> unit
= fun state ->
  match state.status with
    | Error str -> 
        if !Config.html_view then begin
          Format.printf "%s<br>" str
        end else begin
          Format.printf "%s\n" str
        end
    | _ -> ()

(* let execute_instruction_list : ?show:bool -> instruction list -> context -> (ident * expr) list -> unit
= fun ?(show=true) file ctx defs ->
  let fresh_state = new_knel_state ctx defs in
  try
    let final_state =
      List.fold_left 
        execute_instruction
        (fresh_state , true)
        file
    in
    if show && final_state.prompt_enabled then
      if !Config.html_view
      then begin
        Format.printf "<p>File succesfully read, state of KnEL when reached end of file: </p>";
        Format.printf "<br><br><p><b style=\"color:#af601a\">Status:</b> %a</p>"
          pp_status final_state.status;
        Format.printf "<b style=\"color:#af601a\">Final context:</b><br> %a"
          pp_context final_state.global_context;
        Format.printf "<br><br><b style=\"color:#af601a\">Terms defined:</b> \n%a\n"
          pp_def final_state.definitions
      end else begin
        Format.printf "File succesfully read, state of KnEL when reached end of file: \n\n";
        Format.printf "\x1B[38;5;130mStatus:\x1B[39m %a\n\n"
          pp_status final_state.status;
        Format.printf "\x1B[38;5;130mFinal context:\x1B[39m \n%a\n"
          pp_context final_state.global_context;
        Format.printf "\x1B[38;5;130mTerms defined:\x1B[39m \n%a\n"
          pp_def final_state.definitions
      end;
  with
    | Wrong_declaration message ->
        if !Config.html_view
        then
          Format.fprintf Format.err_formatter "<p style=\"color:#FF0000\">Something went wrong when reading your .knl file: \n%s\n</p>"
            message
        else
          Format.fprintf Format.err_formatter "\x1B[38;5;124mSomething went wrong when reading your .knl file: \n%s\n\x1B[39m"
            message *)