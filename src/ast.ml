type ident = string

type place =
  | NamedPlace of ident
  | VoidPlace
  | UnitPlace
  | ProductPlace of place * place
  | SumPlace of place * place
  | PathPlace of place * place

(* Conventions de nommage :
  les lieux sont représentés par des symbole
    s , t
  s'ils sont vus comme source ou but d'un chemin
  et a , b , c , x , y , z ou l dans le cas général *)

(* type way =  *)

type path =
  | NamedPath of place * place * ident
  | ComposedPath of path * path
  | InPath of path list * way
  | OutPath of path list * way
(* Conventions de nommage :
  les chemins sont représentés par des symboles
  p , q , r *)

exception Product_dismatch of path * place * path * place
exception Sum_dismatch of path * place * path * place

let rec source : path -> place =
fun p ->
  match p with
  | NamedPath (s , _ , _) -> s
  | VoidPath _ -> VoidPlace
  | UnitPath s -> s
  | ComposedPath (p1 , _) -> source p1
  | ProductPath (p1 , p2) ->
      let s1 , s2 = source p1 , source p2 in
      if s1 = s2 then s1
      else raise (Product_dismatch (p1 , s1 , p2 , s2))
  | SumPath (p1 , p2) -> SumPlace (source p1 , source p2)

let rec target : path -> place =
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

type sort =
  | SEmpty : sort
  | SUnit : sort
  | SFun : sort * sort -> sort
  | SProd : sort * sort -> sort
  | SSum : sort * sort -> sort

type term =
  | TIt
  | TVar : ident * sort -> term
  | TLam : ident * sort * term * sort -> term
  | TApp : term * sort * term * sort -> term
  | TPair : term * sort * term * sort -> term
  | Tinl : term * sort * sort -> term
  | Tinr : term * sort * sort -> term

type env =
  | EEmpty
  | EAdd : ident * sort * env -> env

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
