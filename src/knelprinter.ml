open KnelState
open Envprinter

let pp_status fmt (st : status) =
  let str = match st with
    | AllDone -> "All Done"
    | InProof -> "In Proof"
    | Error -> "Error"
  in Format.fprintf fmt "%s" str

let pp_knel_state fmt (state : knel_state) =
  Format.fprintf fmt "\n";
  Format.fprintf fmt "Status: %a\n\n"
    pp_status state.status;
  Format.fprintf fmt "Global context:\n%a"
    pp_context state.global_context;
  match state.environments with
    | [] -> ()
    | e :: e_tail ->
        pp_env fmt e;
        Format.fprintf fmt "%d Other goals remaining\n"  
          (List.length e_tail)
