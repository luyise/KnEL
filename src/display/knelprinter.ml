open KnelState
open Envprinter

let pp_status fmt (st : status) =
  let str = 
    if !Config.html_view
    then match st with
      | AllDone -> "<b style=\"color:#1E8449\">All Done</b>"
      | InProof -> "<b style=\"color:#1F618D\">In Proof</b>"
      | Error str   -> "<b style=\"color:#922B21\">Error: "^str^"</b>"
    else match st with
      | AllDone -> "\x1B[38;5;106mAll Done\x1B[39m"
      | InProof -> "\x1B[38;5;62mIn Proof\x1B[39m"
      | Error str -> "\x1B[38;5;124mError: "^str^"\x1B[39m"
  in Format.fprintf fmt "%s" str

let pp_knel_state fmt (state : knel_state) =
  if !Config.html_view
  then begin
    Format.fprintf fmt "<b style=\"color:#af601a\">Status: %a</b>"
      pp_status state.status;
    (* Format.fprintf fmt "<h3>Global context:</h3>\n%a"
      pp_context state.global_context; *)
    match state.environments with
      | [] -> ()
      | e :: e_tail ->
          pp_env fmt e;
          Format.fprintf fmt "<b style=\"color:#af601a\">%d other goals remaining</b>"
            (List.length e_tail)
  end else begin
    Format.fprintf fmt "\n";
    Format.fprintf fmt "\x1B[1m\x1B[38;5;130mStatus:\x1B[24m\x1B[22m %a\n\n"
      pp_status state.status;
    (* Format.fprintf fmt "\x1B[38;5;130mGlobal context:\x1B[39m \n%a"
      pp_context state.global_context; *)
    match state.environments with
      | [] -> ()
      | e :: e_tail ->
          pp_env fmt e;
          Format.fprintf fmt "%d Other goals remaining\n"  
            (List.length e_tail)
  end
