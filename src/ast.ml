type ident = string

type place =
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
  | ProdWayIn of place list
  | PathWayIn of place * place

type wayOut =
  (* | VoidWayOut *)
  | SumWayOut of place list
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
        target p = t && 
        source p = s &&
        check_product p_tail s t_tail
    | _ -> false

(* La fonction check_sum vérifie si une liste
  de chemins possède des sources cohérentes avec une liste
  de lieux donnés *)

let check_sum : path_list -> place list -> bool
= fun p_list x_list ->
  match p_list , x_list with
    | [] , [] -> true
    | 

(* Les fonctions source et target
  calculent les lieux extrémaux d'une flèche,
  tout en vérifiant si la flèche est bien formée *)

let rec source : path -> place =
fun p ->
  match p with
  | NamedPath (s , _ , _) -> s
  | ComposedPath (p1 , p2) ->
      let t1 = target p1 in
      let s2 = source p2 in
      if t1 = s2 then source p1
      else raise Composition_dismatch
  | InPath ([] , ProdWayIn []) -> SumPlace [] (* void place *)
  | InPath (p_list , ProdWayIn )

and target : path -> place =
fun p ->
  match p with
  | NamedPath (_ , t , _) -> t
  | VoidPath t -> t
  | UnitPath _ -> UnitPlace
  | ComposedPath (_ , p2) -> target p2
  | ProductPath (p1 , p2) -> ProductPlace (target p1 , target p2)
  | SumPath (p1 , p2) ->
      let t1 , t2 = target p1 , target p2 in
      if t1 = t2 then t1
      else raise (Sum_dismatch (p1 , t1 , p2 , t2))

let ends : path -> place * place =
fun p ->
  (source p , target p)

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
