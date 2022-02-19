%{
    open Ast
%}

%token ADMITTED     (* Admitted *)
%token ALL          (* ∀ ! *)
%token AMPERAMPER   (* && *)
%token ARROW        (* -> → *)
%token DEFINITION   (* Definition *)
%token COLON        (* : *)
%token COMMA        (* , *)
%token DIV          (* / *)
%token END          (* End *)
%token EOF
%token EQ           (* = *)
%token EQUIV        (* <=> ⇔ *)
%token EXISTS       (* ∃ ? *)
%token GREATER      (* > *)
%token GREATEREQ    (* >= ⩾ *)
%token <Ast.ident> IDENT
%token IMPLIES      (* => ⇒ *)
%token INDUCTIVE    (* Inductive *)
%token LEMMA        (* Lemma *)
%token LET          (* let *)
%token LOWER        (* < *)
%token LOWEREQ      (* <= ⩽ *)
%token LPAREN       (* ( *)
%token MAPSTO       (* mapsto ↦ *)
%token MINUS        (* - *)
%token NEG          (* neg ¬ *)
%token PLUS         (* + *)
%token PROD
%token PROOF        (* Proof *)
%token QED          (* Qed *)
%token RPAREN       (* ) *)
%token STAR         (* * *)
%token THEOREM      (* Theorem *)
%token UNIT         (* Unit ⊤ *)
%token VARIABLES    (* Variables *)
%token VERT         (* | *)
%token VERTVERT     (* || *)
%token VOID         (* Void ⊥ *)

%start file

%nonassoc NEG
%left AMPERAMPER
%left VERTVERT
%left ARROW IMPLIES EQUIV

%left COMMA
%left EQ GREATER GREATEREQ LOWER LOWEREQ
%left PLUS MINUS
%left DIV STAR PROD

%type <(string * unit option) list * (ident * place * string) list> file

%%

file:
    | var_def_bloc list(decl) EOF { ($1, $2) }
;

var_def_bloc:
    | (* EMPTY *) { [] }
    | VARIABLES EQ separated_nonempty_list(COMMA, var_def) { $3 }
;

var_def:
    | IDENT { ($1, None) }
    | IDENT COLON type_binding  { ($1, Some $3) }
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
    | IDENT                     { NamedPlace $1 }
    | VOID                      { SumPlace [] }
    | UNIT                      { ProdPlace [] }
    | statement PROD statement 
        { match $3 with
            | ProdPlace l   -> ProdPlace ($1::l)
            | stmt          -> ProdPlace [$1; stmt]
        }
    | statement PLUS statement
        { match $3 with
            | SumPlace l    -> SumPlace ($1::l)
            | stmt          -> SumPlace [$1; stmt]
        }
    | statement IMPLIES statement { PathPlace ($1, $3) }
    | LPAREN statement RPAREN     { $2 }
;

proof:
    | proof_end { $1 }
;

proof_end:
    | ADMITTED  { "admitted" }
    | QED       { "qed" }
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
