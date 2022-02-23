open Ast

type env =
  { context : context
  ; used_ident : ident list
  ; target : sort
  }

let rec in_context_opt : ident -> context -> expr option
= fun id ctx ->
  match ctx with
    | [] -> None
    | (id' , exp) :: _ when id = id' -> Some exp
    | _ :: ctx_tail -> in_context_opt id ctx_tail