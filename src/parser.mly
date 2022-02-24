%{
    open Ast
    open Tactic

%}

%token ADMITTED     (* Admitted *)
%token AS           (* as *)
%token ALL          (* ∀ ! *)
%token AMPERAMPER   (* && *)
%token ARROW        (* -> → *)
%token DEFINITION   (* Definition *)
%token COLON        (* : *)
%token COMMA        (* , *)
%token DIV          (* / *)
%token DOT          (* . *)
%token END          (* End *)
%token EOF
%token EQ           (* = *)
%token EQUIV        (* <=> ⇔ *)
%token EXISTS       (* ∃ ? *)
%token GREATER      (* > *)
%token GREATEREQ    (* >= ⩾ *)
%token <Ast.ident> IDENT
%token IMPLIES      (* => ⇒ *)
%token IN           (* in *)
%token <int> INT
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
%token ONGOING      (* Ongoing *)
%token OPEN         (* open *)
%token PLUS         (* + *)
%token PROD
%token PROOF        (* Proof *)
%token QED          (* QED *)
%token RBRACKET     (* } *)
%token RPAREN       (* ) *)
%token RSBRACKET    (* ] *)
%token SEMICOLON    (* ; *)
%token STAR         (* * *)
%token SUMIN        (* sum_in *)
%token TACTIC       (* Tactic *)
%token THEOREM      (* Theorem *)
%token UNIT         (* Unit ⊤ *)
%token VARIABLES    (* Variables *)
%token VERT         (* | *)
%token VERTVERT     (* || *)
%token VOID         (* Void ⊥ *)

%start file

%left AMPERAMPER
%left VERTVERT
%right ARROW IMPLIES EQUIV

%left COMMA
%left EQ GREATER LOWER LOWEREQ GREATEREQ
%left STAR PROD
%left PLUS MINUS
%left DIV
%nonassoc NEG

%type <(string * string) list * Tactic.raw_knel_file> file

%%

file:
    | list(opening) decl_list { $1, $2 }
;

opening:
    | OPEN parent separated_nonempty_list(DOT, IDENT) {
        (List.fold_left
            (fun name _ -> "../"^name)
            (List.fold_right (fun f1 f2 -> f1^"/"^f2) $3 "")
            $2,
        List.hd (List.rev $3))
    }
    | OPEN parent separated_nonempty_list(DOT, IDENT) AS IDENT {
        (List.fold_left
            (fun name _ -> "../"^name)
            (List.fold_right (fun f1 f2 -> f1^"/"^f2) $3 "")
            $2,
        $5)
    }
;

parent:
    | (* EMPTY *) { [] }
    | LOWER nonempty_list(MINUS) { $2 }

decl_list:
    | EOF                   { [] }
    | definition decl_list  { $2 }
    | inductive decl_list   { $2 }
    | theorem decl_list     { $1::$2 }
    | tactic_decl decl_list { $1::$2 }
    | hypothesis_intro decl_list { $1::$2 }
;

hypothesis_intro:
    | VARIABLES EQ LBRACKET separated_list(COMMA, var_def) RBRACKET { RawHypothesisSection $4 }
;

var_def:
    | IDENT COLON expr_no_comma  { ($1, $3) }
;

tactic_decl:
    | TACTIC IDENT tactic_arg_def_list { 
        RawTacticDeclSection ($2, $3) }
;

tactic_arg_def_list:
    | EQ tactic END { Tactic $2 }
    | tactic_arg_def tactic_arg_def_list { Arg (fst $1, snd $1, $2) }

tactic_arg_def:
    | LPAREN IDENT COLON tactic_arg_type RPAREN { ($2, $4) }
;

tactic_arg_type:
    | INT       { TInt }
    | TACTIC    { TTac }
    | IDENT     { assert ($1 = "ident"); TIdent }
    | tactic_arg_type ARROW tactic_arg_type { TArrow ($1, $3) }
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
    | thm_keyword IDENT? COLON expr PROOF proof { RawReasoningSection ($1, $2, $4, fst $6, snd $6) }
;

thm_keyword:
    | LEMMA     { Lemma }
    | THEOREM   { Theorem }
;

proof:
    | tactic SEMICOLON proof { $1::fst $3, snd $3 }
    | tactic proof_end      { [$1], $2 }
    | proof_end             { [], $1 }
;

tactic:
    | no_app_tactic             { $1 }
    | tactic_no_cmp no_app_tactic
        { PTacApp ($1, $2) }
    | tactic VERTVERT tactic    { PTacOr ($1, $3) }
    | tactic GREATER tactic     { PTacSeq ($1, $3) }
;

tactic_no_cmp:
    | no_app_tactic             { $1 }
    | tactic_no_cmp no_app_tactic { PTacApp ($1, $2)}
;

no_app_tactic:
    | IDENT                     { PTacVar $1 }
    | INT                       { PTacInt $1 }
    | LPAREN tactic RPAREN      { $2 }
    | LSBRACKET separated_list(SEMICOLON, IDENT) RSBRACKET
        { PTacList $2 }
;

proof_end:
    | ADMITTED  { Admitted }
    | QED       { Qed }
    | ONGOING   { Ongoing }
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

expr_no_comma:
    | expr_in   { $1 }
    | expr_no_comma binop_expr expr_no_comma
        { EApp (EApp(EConst $2, $1), $3) }
    | expr_no_comma PROD expr_no_comma
        { EPair (($1, $3), None) }
    | expr_no_comma IMPLIES expr_no_comma
        { EPi (("_", $1), $3) }
    | NEG expr_no_comma
        { EPi (("_", $2), EConst "Void") }
;

expr:
    | expr_in               { $1 }
    | expr COMMA expr       { EPair (($1, $3), None) }
    | expr binop_expr expr  { EApp (EApp(EConst $2, $1), $3) }
    | expr PROD expr        { EPair (($1, $3), None) }
    | expr IMPLIES expr     { EPi (("_", $1), $3) }
    | NEG expr              { EPi (("_", $2), EConst "Void") }
;

expr_in:
    | expr_in expr_bot  { EApp ($1, $2) }
    | expr_bot          { $1 }

expr_bot:
    | VOID                  { EConst "Void" }
    | UNIT                  { EConst "Unit" }
    | IDENT                 { EVar $1 }
    | LPAREN expr RPAREN    { $2 }
    | LPAREN expr COLON expr RPAREN    { ETaggedExpr ($2, $4) }
;

%inline binop_prop:
    | IMPLIES   { () }
    | EQUIV     { () }
    | AMPERAMPER{ () }
    | VERTVERT  { () }
;

%inline binop_expr:
    | PLUS      { "+" }
    | MINUS     { "-" }
    | STAR      { "*" }
    | DIV       { "/" }
    | cmp_op    { $1 }
;

%inline cmp_op:
    | EQ        { "=" }
    | GREATER   { ">" }
    | GREATEREQ { ">=" }
    | LOWER     { "<" }
    | LOWEREQ   { "<=" }
;
