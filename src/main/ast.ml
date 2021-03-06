
type ident = string
exception Ident_conflict of ident
exception Unable_to_infer_implicit_argument

module SMap = Map.Make(String)
module SSet = Set.Make(String)
module IMap = Map.Make(Int)

type expr_loc =
  | PFunSource
  | PFunNonDepTarget
  | PFunDepTarget
  | PSigFst
  | PSigNonDepSnd
  | PSigDepSnd

type expr_path = expr_loc list

type 'a located =
  { desc : 'a;
    loc : Location.t
  }

type type_of_arg =
  | Explicit
  | Implicit

type parsed_expr = parsed_expr_desc located
and parsed_expr_desc =
  | PVar of ident
  | PLam   of ((ident * parsed_expr) * parsed_expr * type_of_arg)
  | PPi    of ((ident * parsed_expr) * parsed_expr * type_of_arg)
  | PSigma of ((ident * parsed_expr) * parsed_expr * type_of_arg)
  | PPair  of (parsed_expr * parsed_expr) * (parsed_expr option)
  | PApp of parsed_expr list


type expr = expr_desc located

and expr_desc =
    (* Représente une constante, a priori déjà connue *)
  | EConst of ident
    (* Représente une variable, on ne présume pas, 
    et d'ailleurs on ne souhaite pas qu'elle existe dans le contexte *)
  | EVar of ident
    (* Lambda abstraction, dont l'expression à droite possède a priori un "type" 
    dépendant du paramètre EVar *)
  | ELam of (ident * expr) * expr * (expr_path option)
    (* Aplication d'une expression à une autre *)
  | EApp of expr * expr
    (* Type des applications dépendantes, le exp_path option correspond à la location d'un argument implicite éventuel *)
  | EPi of (ident * expr) * expr * (expr_path option)
    (* Paire dépendante : le deuxième argument peut avoir un type dépendant du premier *)
  | EPair of (expr * expr) * (expr option)
    (* Les deux éliminateurs pour une paire *)
  | EFst of expr
  | ESnd of expr
    (* Type des paires dépendantes *)
  | ESigma of (ident * expr) * expr * (expr_path option)

type context = (ident * expr) list
type parsed_context = (ident * parsed_expr) list

type tactic_expr = parsed_expr

type base_tactic =
  | IntroTac of ident             (* Former un terme de type Π (a : A) (B a) *)
  | ApplyTac of expr              (* Passe d'un objectif B à un objectif A sachant *)
                                  (*  l'existence de f : Π (_ : A) B dans le context *)
  (* | SplitTac of expr              Former un terme de type Σ (a : A) (B a), demande le premier argument *)
  (* | SigmaIndTac                    Appliquer le récurseur non dépendant de Σ (a : A) (B a),  *)
                                  (*    pour introduire un terme du type (Σ (a : A) (B a)) → C,   *)
                                  (*    i.e. demande de montrer Π (a : A) (B a) → C *)            
  | SigmaRecTac                   (* Appliquer le récurseur dépendant de Σ (a : A) (B a), 
                                      pour introduire un terme du type Π (p : (Σ (a : A) (B a))) → C p,
                                      i.e. demande de montrer Π (a : A) (b : (B a)) → C (a , b) *)
  (* | ChooseTac of int              Former un terme de type +[ - ] *)
  (* | SumRecTac                     Appliquer le récurseur de +, 
                                    pour introduire un terme du type +[ - ] → t *)
  | ExactTac of expr              (* Démontre un objectif en invoquant 
                                    une variable du contexte *)
  | DefineTac of ident * expr * expr      (* Défini un term à partir des éléments du contexte courant : correspond à un let in. *)
  | UnfoldTac of ident
  | ReduceTac

type tactic =
  | BaseTac of base_tactic
  | TryTac of tactic
  | DoTac of int * tactic
  | SeqTac of tactic * tactic
  | OrTac of tactic * tactic

type tactic_type =
  | TExpr
  | TInt
  | TIdent
  | TTac
  | TArrow of tactic_type * tactic_type
  | TUnknown

type beggining_tag =
  | Lemma
  | Theorem

type ending_tag =
  | Qed
  | Admitted
  | Ongoing

type beta_rule_type = ident list -> expr_desc -> expr_desc option

(* le type instruction correspond aux différentes commandes pouvant être donnée par le mode intéractif,
  elle correspondent à une action que doit exécuter le noyau *)

type instruction =
    (* Définition d'un λ-terme *)
  | IDefine of (ident * parsed_expr * parsed_expr)
    (* Déclaration d'une nouvelle tactique *)
  | ITacDecl of (string * parsed_expr)
    (* Déclaration d'une liste de varaiables à ajouter au contexte courant *)
  | IHypothesis of parsed_context
    (* Demande d'ouverture d'un fichier .knl *)
  | IOpen of string * string * (parsed_expr list)
    (* Demande de retour en arrière *)
  | IBackward
    (* Déclaration du début d'une nouvelle preuve *)
  | IBeginProof of (ident option * parsed_expr)
    (* Demande d'utilisation d'une tactique pour faire avancer l'état de la preuve *)
  | ITactic of parsed_expr
    (* Demande de jeter la preuve en cours *)
  | IDropProof
    (* Demande de vérifier une preuve entière, et de l'ajouter au contexte global *)
  | IFullProof of (beggining_tag * (ident option) * parsed_expr * (parsed_expr list) * ending_tag)
    (* Introduit une nouvelle règle de β-réduction *)
  | IBetaRuleDecl of beta_rule_type

type knel_section =
  | HypothesisSection of parsed_context
  | ReasoningSection of 
      (beggining_tag *
        ident option *
        parsed_expr *
        tactic_expr list *
      ending_tag)
  | DefinitionSection of
      (ident * parsed_expr * parsed_expr)
  | BetaRuleDeclSection of
      beta_rule_type
  | OpenSection of
      (string * string * (parsed_expr list))
  | TacDeclSection of
      (string * tactic_expr)
      (* nom de la définition, son type, son lambda term *)
  (* | InductiveSection of
      ident (* nom de la famille inductive à définir *)
      * expr (* type de la famille inductive à définir *)
      * context famille de constructeurs définis avec la famille de type inductif *)

type knel_file = knel_section list


type assoc =
  | Left
  | Right

type priority_ctxt = (int * assoc) SMap.t