open KnelState
open Envprinter

let pp_status fmt (st : status) =
  let str = 
    if !Config.html_view
    then match st with
      | AllDone -> "<b style=\"color:#00FF00\">All Done</b>"
      | InProof -> "<b style=\"color:#0000FF\">In Proof</b>"
      | Error str   -> "<b style=\"color:#FF0000\">Error: "^str^"</b>"
    else match st with
      | AllDone -> "\x1B[38;5;106mAll Done\x1B[39m"
      | InProof -> "\x1B[38;5;62mIn Proof\x1B[39m"
      | Error str -> "\x1B[38;5;124mError: "^str^"\x1B[39m"
  in Format.fprintf fmt "%s" str

let pp_knel_state fmt (state : knel_state) =
  if !Config.html_view
  then begin
    Format.fprintf fmt "<p>Status : %a</p>"
      pp_status state.status;
    (* Format.fprintf fmt "<h3>Global context:</h3>\n%a"
      pp_context state.global_context; *)
    match state.environments with
      | [] -> ()
      | e :: e_tail ->
          pp_env fmt e;
          Format.fprintf fmt "<p>%d Other goals remaining</p>"
            (List.length e_tail)
  end else begin
    Format.fprintf fmt "\n";
    Format.fprintf fmt "\x1B[38;5;130mStatus:\x1B[39m %a\n\n"
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
