
type ident = string

type sort =
  | SVar of ident          (* Variable représentant une sorte *)
  | SFun of sort * sort    (* Sorte A → B où A et B sont des sortes *)
  | SProd of sort list     (* Sorte ×[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)
  | SSum of sort list      (* Sorte +[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)

type term =
  | TVar of ident                           (* Variable représentant un term *)
  | TLam of (ident * sort) * term           (* λ - abstraction *)
  | TApp of term * term                     (* Application de fonction *)
  | TProdConstr of term list                (* Uplet de termes *)
  | TSumConstr of int * term * sort list    (* i-ème injection *)

type context = (ident * sort) list

exception Unknown_variable
exception Sort_error

let rec search_for_term : ident -> context -> sort option
= fun id ctx ->
  match ctx with
    | [] -> None
    | (id' , t) :: _ when id = id' -> Some t
    | _ :: ctx_tail -> search_for_term id ctx_tail

let rec get_sort : term -> context -> sort
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
        if get_sort t' ctx = List.nth s_list (n-1) then
          SSum s_list
        else raise Sort_error


type base_tactic =
  | IntroTac of ident             (* Former un terme de type s → t *)
  | ApplyTac of term              (* Passe d'un objectif t à un objectif s sachant
                                    l'existence de f : s → t dans le context *)
  | SplitTac                      (* Former un terme de type ×[ - ] *)
  | ProdRecTac of ident list      (* Appliquer le récurseur de ×, 
                                      pour introduire un terme du type ×[ - ] → t *)
  | ChooseTac of int              (* Former un terme de type +[ - ] *)
  | SumRecTac                     (* Appliquer le récurseur de +, 
                                    pour introduire un terme du type +[ - ] → t *)
  | ExactTac of term              (* Démontre un objectif en invoquant 
                                    une variable du contexte *)

type tactic =
  | BaseTac of base_tactic
  | TryTac of tactic
  | DoTac of int * tactic
  | SeqTac of tactic * tactic
  | OrTac of tactic * tactic

type beggining_tag =
  | Lemma
  | Theorem

type ending_tag =
  | Qed
  | Admitted
  | Ongoing

type knel_section =
  | HypothesisSection of context
  | ReasoningSection of 
      (beggining_tag * 
        ident option * 
        sort *
        tactic list *
      ending_tag)

type knel_file = knel_section list