%{
    open Ast
    open Environment
%}

%token ADMITTED     (* Admitted *)
%token ALL          (* ∀ ! *)
%token AMPERAMPER   (* && *)
%token APPLY        (* Apply *)
%token ARROW        (* -> → *)
%token DEFINITION   (* Definition *)
%token CHOOSE       (* Choose *)
%token COLON        (* : *)
%token COMMA        (* , *)
%token DIV          (* / *)
%token END          (* End *)
%token EOF
%token EQ           (* = *)
%token EQUIV        (* <=> ⇔ *)
%token EXACT        (* Exact *)
%token EXISTS       (* ∃ ? *)
%token GREATER      (* > *)
%token GREATEREQ    (* >= ⩾ *)
%token <Ast.ident> IDENT
%token IMPLIES      (* => ⇒ *)
%token IN           (* In *)
%token <int> INT
%token INTRO
%token INDUCTIVE    (* Inductive *)
%token LAMBDA       (* lam λ *)
%token LBRACKET     (* { *)
%token LEMMA        (* Lemma *)
%token LET          (* let *)
%token LOWER        (* < *)
%token LOWEREQ      (* <= ⩽ *)
%token LPAREN       (* ( *)
%token LSBRACKET    (* [ *)
%token MAPSTO       (* mapsto ↦ *)
%token MINUS        (* - *)
%token NEG          (* neg ¬ *)
%token PLUS         (* + *)
%token PROD
%token PRODREC      (* ProdRec *)
%token PROOF        (* Proof *)
%token QED          (* Qed *)
%token RBRACKET     (* } *)
%token RPAREN       (* ) *)
%token RPT          (* rpt *)
%token RSBRACKET    (* ] *)
%token SEMICOLON    (* ; *)
%token SPLIT        (* Split *)
%token STAR         (* * *)
%token SUMREC       (* SumRec *)
%token THEOREM      (* Theorem *)
%token TRY          (* try *)
%token UNIT         (* Unit ⊤ *)
%token VARIABLES    (* Variables *)
%token VERT         (* | *)
%token VERTVERT     (* || *)
%token VOID         (* Void ⊥ *)

%start file

%nonassoc NEG
%left AMPERAMPER
%left VERTVERT
%right ARROW IMPLIES EQUIV

%left COMMA
%left EQ GREATER GREATEREQ LOWER LOWEREQ
%left PLUS MINUS
%left DIV STAR PROD
%nonassoc RPT TRY

%type <(string * sort) list * (ident * sort * (base_tactic list * string)) list> file

%%

file:
    | var_def_bloc list(decl) EOF { ($1, $2) }
;

var_def_bloc:
    | VARIABLES EQ LBRACKET separated_list(COMMA, var_def) RBRACKET { $4 }
;

var_def:
    | IDENT COLON statement  { ($1, $3) }
;

type_binding:
    | (* TODO *)   { assert false }
;

decl:
    | definition    { assert false }
    | inductive     { assert false }
    | theorem       { $1 }
;

definition:
    | DEFINITION IDENT COLON def_bloc END { $2 }
;

def_bloc:
    | (* EMPTY *) { () }
;

inductive:
    | INDUCTIVE IDENT COLON type_decl EQ list(induc_bloc) END { $2 }
;

induc_bloc:
    | VERT IDENT COLON prop { ($1, $3) }
;

theorem:
    | thm_keyword IDENT COLON statement PROOF proof { ($2, $4, $6) }
;

thm_keyword:
    | LEMMA     { "lemma" }
    | THEOREM   { "theorem" }
;

statement:
    | IDENT                     { SVar $1 }
    | VOID                      { SSum [] }
    | UNIT                      { SProd [] }
    | statement PROD statement 
        { match $3 with
            | SProd l   -> SProd ($1::l)
            | stmt      -> SProd [$1; stmt]
        }
    | statement PLUS statement
        { match $3 with
            | SSum l    -> SSum ($1::l)
            | stmt      -> SSum [$1; stmt]
        }
    | statement IMPLIES statement   { SFun ($1, $3) }
    | LPAREN statement RPAREN       { $2 }
    | NEG statement                 { SFun ($2, SSum [])}
;

proof:
    | tactic SEMICOLON proof { ($1::fst $3, snd $3) }
    | tactic proof_end      { [$1], $2 }
    | proof_end             { [], $1 }
;

tactic:
    | base_tactic           { $1 }
    | LPAREN tactic RPAREN  { $2 }
    | tactic GREATER tactic { assert false }
    | tactic VERTVERT tactic{ assert false }
    | TRY tactic            { assert false }
    | RPT tactic            { assert false }
    | IDENT term            { assert false }
;

base_tactic:
    | INTRO IDENT           { IntroTac $2 }
    | APPLY term            { ApplyTac $2 }
    | SPLIT                 { SplitTac }
    | PRODREC LSBRACKET separated_list(COMMA, IDENT)  RSBRACKET
        { ProdRecTac $3 }
    | CHOOSE INT            { ChooseTac $2 }
    | SUMREC                { SumRecTac }
    | EXACT term            { ExactTac $2 }
;

proof_end:
    | ADMITTED  { "Admitted" }
    | QED       { "Qed" }
;

type_decl:
    | type_decl ARROW type_decl { () }
    | LPAREN type_decl RPAREN   { () }
    | type_decl STAR type_decl  { () }
    | IDENT                     { () }
;

prop:
    | prop binop_prop prop  { () }
    | NEG prop              { () }
    | IDENT                 { () }
    | LPAREN prop RPAREN    { () }
;

term:
    | term term_no_app  { TApp ($1, $2) }
    | term_no_app       { $1 }
    | LAMBDA IDENT COLON statement ARROW term
        { TLam ($2, $4, $6) }
    | IDENT COLON statement MAPSTO term
        { TLam ($1, $3, $5) }
;

term_no_app:
    | LPAREN l = separated_list(COMMA, term) RPAREN
        { match l with
            | [x] -> x
            | _ -> TProdConstr l }
    | IDENT
        { TVar $1 }
    | IN LBRACKET nonempty_list(statement) RBRACKET INT term_no_app
        { TSumConstr ($5, $6, $3) }
;

expr:
    | expr_in
    | expr COMMA expr       { () }
    | expr binop_expr expr  { () }
;

expr_in:
    | expr_in expr_bot { () }
    | expr_bot          { () }

expr_bot:
    | IDENT                 { () }
    | LPAREN expr RPAREN    { $2 }
;

%inline binop_prop:
    | IMPLIES   { () }
    | EQUIV     { () }
    | AMPERAMPER{ () }
    | VERTVERT  { () }
;

%inline binop_expr:
    | PLUS      { () }
    | MINUS     { () }
    | STAR      { () }
    | DIV       { () }
    | cmp_op    { $1 }
;

%inline cmp_op:
    | EQ        { () }
    | GREATER   { () }
    | GREATEREQ { () }
    | LOWER     { () }
    | LOWEREQ   { () }
;
