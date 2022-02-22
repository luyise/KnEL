open Ast

type env =
  { context : context
  ; target : sort
  }

let rec search_for_term : ident -> context -> expr option
= fun id ctx ->
  match ctx with
    | [] -> None
    | (id' , exp) :: _ when id = id' -> Some exp
    | _ :: ctx_tail -> search_for_term id ctx_tail
    