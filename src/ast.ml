(* module type ID =
sig
  type ident
  val pp_ident : ident -> unit
end
  
module StdIdent : ID =
struct
  type ident = string
  let pp_ident : ident -> unit = print_endline
end *)

(* open StdIdent *)

type ident = string
[@@deriving show]
(* pp_ident *)

type sort =
  | SVar of ident          (* Variable représentant une sorte *)
  | SFun of sort * sort    (* Sorte A → B où A et B sont des sortes *)
  | SProd of sort list     (* Sorte ×[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)
  | SSum of sort list      (* Sorte +[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)
[@@deriving show]
(* pp_sort *)

type term =
  | TVar of ident                           (* Variable représentant un term *)
  | TLam of (ident * sort) * term           (* λ - abstraction *)
  | TApp of term * term                     (* Application de fonction *)
  | TProdConstr of term list                (* Uplet de termes *)
  | TSumConstr of int * term * sort list    (* i-ème injection *)
[@@deriving show]
(* pp_term *)

exception Unknown_variable
exception Sort_error

let rec search_for_term : ident -> (ident * sort) list -> sort option
= fun id ctx ->
  match ctx with
    | [] -> None
    | (id' , t) :: _ when id = id' -> Some t
    | _ :: ctx_tail -> search_for_term id ctx_tail

let rec get_sort : term -> (ident * sort) list -> sort
= fun t ctx ->
  match t with
    | TVar id -> begin
        match search_for_term id ctx with
          | Some s -> s
          | None -> raise Unknown_variable
        end
    | TLam ((id , s) , t') ->
        SFun (s, get_sort t' ((id , s) :: ctx))
    | TApp (t' , t'') -> begin
        match get_sort t' ctx , get_sort t'' ctx with
          | SFun (a , s) , b when b = a -> s
          | _ -> raise Sort_error
        end
    | TProdConstr t_list ->
        SProd (List.map (fun t' -> get_sort t' ctx) t_list)
    | TSumConstr (n , t' , s_list) ->
        if get_sort t' ctx = List.nth s_list n then
          SSum s_list
        else raise Sort_error