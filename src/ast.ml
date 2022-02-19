type ident = string

type sort =
  | SVar of ident             (* Variable représentant une sorte *)
  | SFun of sort * sort    (* Sorte A → B où A et B sont des sortes *)
  | SProd of sort list     (* Sorte ×[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)
  | SSum of sort list      (* Sorte +[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)

type term =
  | TVar of ident * sort
  | TLam of (ident * sort) * (term * sort)
  | TApp of (term * sort) * (term * sort)
  | TProdConstr of (term * sort) list
  | TSumConstr of int * term * sort list

(* type place =
  | NamedPlace of ident
  (* | VoidPlace *)
  (* | UnitPlace *)
  | ProdPlace of place list
  | SumPlace of place list
  | PathPlace of place * place

(* Conventions de nommage :
  les lieux sont représentés par des symbole
    s , t
  s'ils sont vus comme source ou but d'un chemin
  et a , b , c , x , y , z ou l dans le cas général *)

type wayIn =
  (* | UnitWayIn *)
  | ProdWayIn of place * (place list)
  | PathWayIn of place * place

type wayOut =
  (* | VoidWayOut *)
  | SumWayOut of (place list) * place
  | PathWayOut of place * place

type path =
  | NamedPath of place * place * ident
  | ComposedPath of path * path
  | ProjectionPath of place list * place
  | InclusionPath of place list * place
  | InPath of path list * wayIn
  | OutPath of path list * wayOut

(* Conventions de nommage :
  les chemins sont représentés par des symboles
  p , q , r *)

exception Composition_dismatch
exception Product_dismatch
exception Sum_dismatch

(* La fonction check_composition vérifie si deux
  chemins sont composables *)

let rec check_composition : path -> path -> bool
= fun p q ->
  target p = source q

(* La fonction check_product vérifie si une liste
  de chemins possède une même source correspondant à un lieu donné
  et des buts cohérents avec une liste de lieux donnés *)

and check_product : path list -> place -> place list -> bool
= fun p_list s t_list ->
  match p_list , t_list with
    | [] , [] -> true
    | p :: p_tail , t :: t_tail ->
        source p = s &&
        target p = t &&
        check_product p_tail s t_tail
    | _ -> false

(* La fonction check_sum vérifie si une liste
  de chemins possède des sources cohérentes avec une liste
  de lieux donnés *)

and check_sum : path list -> place list -> place -> bool
= fun p_list s_list t ->
  match p_list , s_list with
    | [] , [] -> true
    | p :: p_tail , s :: s_tail -> 
        source p = s &&
        target p = t &&
        check_sum p_tail s_tail t
    | _ -> false

(* Les fonctions ends, source et target
  calculent les lieux extrémaux d'une flèche,
  tout en vérifiant si la flèche est bien formée *)

and ends : path -> place * place =
fun p ->
  match p with
  | NamedPath (s , t , _) -> (s , t)
  | ComposedPath (p1 , p2) ->
      if check_composition p1 p2 then (source p1 , target p2)
      else raise Composition_dismatch
  | InPath (p_list , ProdWayIn (s , t_list)) ->
      if check_product p_list s t_list then (s , ProdPlace t_list)
      else raise Product_dismatch
  | OutPath (p_list , SumWayOut (s_list , t)) ->
      if check_sum p_list s_list t then (SumPlace s_list , t)
      else raise Sum_dismatch
  | _ -> failwith "TO_DO"

and source : path -> place =
fun p ->
  fst ((ends p) : place * place)

and target : path -> place =
fun p ->
  snd (ends p)

  *)

(*

let rec in_env : ident -> env -> sort option
= fun x e ->
  match e with
    | EEmpty -> None
    | EAdd (y, t, _) when y = x -> Some t
    | EAdd (_, _, e') -> in_env x e'

*)

(*

  ------ Empty x
  x ∉ []

  y <> x     x ∉ Γ
  ---------------- Add π1 π2
  x ∉ (y : τ) :: Γ



  ----------------------- Add x τ Γ
  x ∈ (x : τ) :: Γ with τ

  y <> x      x ∈ Γ with τ₀
  ------------------------- Ext π1 π2 τ₁
  x ∈ (y : τ₁) :: Γ with τ₀



  --------- Unit
  Γ ⊢ * : 1

  x ∈ Γ with τ
  ------------ Ctx
    Γ ⊢ x : τ

  Γ ⊢ T : τ₀        x ∉ Γ
  ------------------------ Wkn
   (x : τ₁) :: Γ ⊢ T : τ₀

    (x : τ₀) :: Γ ⊢ T₁ : τ₁
  ----------------------------- Lam
  Γ ⊢ λ (x : τ₀) . T₁ : τ₀ → τ₁

  Γ ⊢ T₀ : τ₀ → τ₁   Γ ⊢ T₁ : τ₀
  ------------------------------ App
           T₀ T₁ : τ₁

*)
