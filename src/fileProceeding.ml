open Ast
open Environment
open KnelState
open Knelprinter

(* La fonction make_knel_state prend en argument un contexte 
    [ ctx : (ident * sort) list ] 
  et une sorte en option représentant un éventuel théorème à montrer 
    [ goal : sort option ]
  et renvoie un knel_state neuf,
  prêt à executer une liste de tactique *)

let make_knel_state : (ident * sort) list -> sort option -> knel_state
= fun ctx goal ->
  match goal with
    | None -> [] , AllDone
    | Some tgt ->
        [{ context = ctx
        ; target = tgt }] ,
        InProof

(* La fonction execite_file prend en argument un contexte 
    [ ctx : (ident * sort) list ],
  une sorte en option représentant un éventuel théorème à montrer 
    [ goal : sort option ],
  et une liste de tactique à executer pour montrer le résultat
  et tente de prouver goal, à partir d'un nouveau knel_state *)

let execute_file : (ident * sort) list 
  -> sort option -> tactic list -> unit
= fun ctx goal tacl ->
  let fresh_state = make_knel_state ctx goal in
  let final_state = execute_tac_list fresh_state tacl in
  pp_knel_state 
    Format.std_formatter
    final_state
