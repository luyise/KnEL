
type ident = string

(* type sort =
  | SVar of ident          (* Variable représentant une sorte *)
  | SFun of sort * sort    (* Sorte A → B où A et B sont des sortes *)
  | SProd of sort list     (* Sorte ×[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)
  | SSum of sort list      (* Sorte +[ A₀ , ... , Aₙ ] où les Aᵢ sont des sortes *)

type term =
  | TVar of ident                           (* Variable représentant un term *)
  | TLam of (ident * sort) * term           (* λ - abstraction *)
  | TApp of term * term                     (* Application de fonction *)
  | TProdConstr of term list                (* Uplet de termes *)
  | TSumConstr of int * term * sort list    i-ème injection *)

type expr =
    (* Représente une constante, a priori déjà connue *)
  | EConst of ident
    (* Représente une variable, on ne présume pas, 
    et d'ailleurs on ne souhaite pas qu'elle existe dans le contexte *)
  | EVar of ident
    (* Lambda abstraction, dont l'expression à droite possède a priori un "type" 
    dépendant du paramètre EVar *)
  | ELam of (ident * expr) * expr
    (* Aplication d'une expression à une autre *)
  | EApp of expr * expr
    (* Type des applications dépendantes *)
  | EPi of (ident * expr) * expr
    (* Paire dépendante : le deuxième argument peut avoir un type dépendant du premier *)
  | EPair of (expr * expr) * (expr option)
    (* Les deux éliminateurs pour une paire *)
  | EFst of expr
  | ESnd of expr
    (* Type des paires dépendantes *)
  | ESigma of (ident * expr) * expr
    (* Correspond à une expression dont le type a été forcé par l'utilisateur *)
  | ETaggedExpr of expr * expr

type context = (ident * expr) list

type base_tactic =
  | IntroTac of ident             (* Former un terme de type Π (a : A) (B a) *)
  | ApplyTac of term              (* Passe d'un objectif B à un objectif A sachant
                                    l'existence de f : Π (_ : A) B dans le context *)
  | SplitTac of term              (* Former un terme de type Σ (a : A) (B a), demande le premier argument *)
  (* | SigmaIndTac                   (* Appliquer le récurseur non dépendant de Σ (a : A) (B a),  *)
                                      pour introduire un terme du type (Σ (a : A) (B a)) → C,
                                      i.e. demande de montrer Π (a : A) (B a) → C *)
  | SigmaRecTac                   (* Appliquer le récurseur dépendant de Σ (a : A) (B a), 
                                      pour introduire un terme du type Π (p : (Σ (a : A) (B a))) → C p,
                                      i.e. demande de montrer Π (a : A) (b : (B a)) → C (a , b) *)
  (* | ChooseTac of int              Former un terme de type +[ - ] *)
  (* | SumRecTac                     (* Appliquer le récurseur de +, 
                                    pour introduire un terme du type +[ - ] → t *) *)
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