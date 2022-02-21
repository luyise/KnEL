open KnelState
open Envprinter

let pp_status fmt (st : status) =
  let str = match st with
    | AllDone -> "\x1B[38;5;106mAll Done\x1B[39m"
    | InProof -> "\x1B[38;5;62mIn Proof\x1B[39m"
    | Error -> "\x1B[38;5;124mError\x1B[39m"
  in Format.fprintf fmt "%s" str

let pp_knel_state fmt (state : knel_state) =
  Format.fprintf fmt "\n";
  Format.fprintf fmt "\x1B[38;5;130mStatus:\x1B[39m %a\n\n"
    pp_status state.status;
  Format.fprintf fmt "\x1B[38;5;130mGlobal context:\x1B[39m \n%a"
    pp_context state.global_context;
  match state.environments with
    | [] -> ()
    | e :: e_tail ->
        pp_env fmt e;
        Format.fprintf fmt "%d Other goals remaining\n"  
          (List.length e_tail)
