
type ident = string

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
  | ApplyTac of expr              (* Passe d'un objectif B à un objectif A sachant *)
                                  (*  l'existence de f : Π (_ : A) B dans le context *)
  | SplitTac of expr              (* Former un terme de type Σ (a : A) (B a), demande le premier argument *)
  (* | SigmaIndTac                    Appliquer le récurseur non dépendant de Σ (a : A) (B a),  *)
                                  (*    pour introduire un terme du type (Σ (a : A) (B a)) → C,   *)
                                  (*    i.e. demande de montrer Π (a : A) (B a) → C *)            
  | SigmaRecTac                   (* Appliquer le récurseur dépendant de Σ (a : A) (B a), 
                                      pour introduire un terme du type Π (p : (Σ (a : A) (B a))) → C p,
                                      i.e. demande de montrer Π (a : A) (b : (B a)) → C (a , b) *)
  (* | ChooseTac of int              Former un terme de type +[ - ] *)
  (* | SumRecTac                     Appliquer le récurseur de +, 
                                    pour introduire un terme du type +[ - ] → t *)
  | ExactTac of expr             (* Démontre un objectif en invoquant 
                                    une variable du contexte *)
  | DefineTac of ident * expr * expr      (* Défini un term à partir des éléments du contexte courant : correspond à un let in. *)
  | UnfoldTac of ident

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
        expr *
        tactic list *
      ending_tag)
  | DefinitionSection of
      (ident * expr * expr)
      (* nom de la définition, son type, son lambda term *)

type knel_file = knel_section list