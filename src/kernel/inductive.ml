(* 
exception Not_strictly_positive

let rec check_strictly_positive : ident -> ident list -> expr -> bool =
fun name idl exp -> match exp.desc with
  | EConst _ -> true
  | EVar _ -> true
  | E






(* data Nat : Type where
  | O : Nat
  | S : Nat -> Nat

(P : Nat → Type), P O → Π (n : Nat) (P n → P (S n))
  → Π (n : Nat) P n

data Tree : Type -> Type where
  | Nil : {A : Type} → Tree A
  | Node : {A : Type} → (a : A) → Tree A → Tree A → Tree A

Π (A : Type), Π (P : Tree A → Type),
     P leaf
  → (Π (a : A) (t₁ : Tree A) (P t₁) (t₂ : Tree A) (P t₂), P (Node a t₁ t₂))
  → (Π (t : Tree A), P t).

Π (A : Type) Π (Z : Type),
     Z
  → (A → (Tree A) → Z → (Tree A) → Z → Z)
  → (Tree A → Z)

data ΛTerm where
  | Var : Nat → ΛTerm
  | Λ : Nat → ΛTerm → ΛTerm
  | App : ΛTerm → ΛTerm → ΛTerm

Π (Z : Type),
    (Nat → Z)
  → (Nat → ΛTerm → Z → Z)
  → (ΛTerm → Z → ΛTerm → Z → Z)
  → (ΛTerm → Z)

Π (P : ΛTerm → Type),
    (Π (n : Nat), P (Var n))
  → (Π (n : Nat), Π (t : ΛTerm), P t → P (Λ n t))
  → (Π (t₁ : ΛTerm), P t₁ → Π (t₂ : ΛTerm), P t₂ → P (App t₁ t₂))
  → (Π (t : ΛTerm), P t)

data ProofTree (A : Type) (P : A → Type) where
  | Leaf : ProofTree A P
  | Node : Π (a : A), (P a) → (ProofTree A P) → (ProofTree A P) → (ProofTree A P)

Π (Z : Type),
     Z
  → ((Π (a : A), Π (_ : P a), Π (t₁ : ProofTree A P), Π (_ : Z), Π (t₂ : ProofTree A P), Π (_ : Z), Z)
  → (ProofTree A P → Z)

Π (P' : ProofTree → Type),
     P' Leaf
  → ((Π (a : A), Π (p : P a), Π (t₁ : ProofTree A P), Π (_ : P' t₁), Π (t₂ : ProofTree A P), (Π _ : P' t₂), P' (Node a p t₁ t₂))
  → (Π (t : ProofTree A P), P' t)

data Acc (R : A → A → Type) : A → Type where
  | AccIntro : Π (b : A), (Π (a : A), R a b → Acc a) → Acc b.

Π (Z : Type),
  (Π (b : A), Π (f : Π (a : A), Π (_ : R a b), Π (_ : Acc a), Z), Z)
  → (Π (a : A), Π (_ : Acc A), Z

Π (P : Π (a : A) (acc : Acc A), Type),
  (Π (b : A), Π (f : Π (a : A), Π (r : R a b), Π (acc : Acc a), P a (acc a)), P b (AccIntro b f))
  → (Π (a : A), Π (p : Acc A), P a p












 *)


let rec check_strictly_positive : ident -> ident list -> expr -> bool
= fun name idl exp -> match exp.desc with
  | EConst _ -> true
  | EVar _ -> true
  | ELam _ -> false
  | EApp (name , ?)
  | EApp (exp1 , exp2) ->
      (not (List.mem name (get_varlib idl typ)))
  | EPi ((id , typ) , typ_over_typ) when id = "_" ->
      check_strictly_positive idl typ
      && check_strictly_positive idl typ'
  | EPi ((id , typ) , typ_over_typ) ->
      (not (List.mem name (get_varlib idl typ)))
      && check_strictly_positive (id :: idl) typ_over_typ
  | EPair _ -> false
  | ESigma ((id , typ) , typ_over_typ) when id = "_" ->
      check_strictly_positive idl typ
      && check_strictly_positive idl typ'
  | ESigma ((id , typ) , typ_over_typ) ->
      (not (List.mem name (get_varlib idl typ)))
      && check_strictly_positive (id :: idl) typ_over_typ

exception Invalid_constructor_shape

let rec check_head : ident -> expr -> bool
= fun id exp -> match exp.desc with
  | EConst _ -> false
  | EVar id' when id' = id -> true
  | EVar _ -> false
  | ELam _ -> false
  | EApp (EVar id , exp) -> true
  | EApp _ -> false
  | EPi ((id' , typ) , typ_over_typ) when id' = id -> false
  | EPi (_ , typ_over_typ) -> check_head id typ_over_typ
  | EPair _ -> false
  | ESigma ((id' , typ) , typ_over_typ) when id' = id -> false
  | ESigma (_ , typ_over_typ) -> check_head id typ_over_typ
  | ETaggedExpr (exp1 , _) -> check_head exp1 *)