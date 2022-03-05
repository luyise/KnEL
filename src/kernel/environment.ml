open Parse
open Ast

(* Les définitions sont des identifiants qui pointent vers un lambda term déjà défini,
il permettent de rendre les termes plus concis et plus lisibles, ainsi qu'à introduire des notions 
Il devrait toujours y avoir pour chaque définition, un élément du context qui lui associe un type !*)

type env =
  { context : context
  ; definitions : (ident * expr) list
  ; used_ident : ident list
  ; target : expr
  }

let rec in_context_opt : ident -> context -> expr option
= fun id ctx ->
  match ctx with
    | [] -> None
    | (id' , exp) :: _ when id = id' -> Some exp
    | _ :: ctx_tail -> in_context_opt id ctx_tail

let rec in_definitions_opt : ident -> (ident * expr) list -> expr option
= fun id defs ->
  match defs with
    | [] -> None
    | (id' , term) :: _ when id = id' -> Some term
    | _ :: defs_tail -> in_definitions_opt id defs_tail
