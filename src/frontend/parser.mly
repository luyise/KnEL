%{
    open Ast
    open Tactic

let mk_sigma = List.fold_right (fun p e -> ESigma (p, e))
let mk_lam = List.fold_right (fun p e -> ELam (p, e))
let mk_pi = List.fold_right (fun p e -> EPi (p, e))

let mk_pair_list il t = List.map (fun i -> (i, t)) il

%}

%token ADMITTED     (* Admitted *)
%token AS           (* as *)
%token ALL          (* ∀ ! *)
%token AMPERAMPER   (* && *)
%token AND          (* and ∧ *)
%token ARROW        (* -> → *)
%token DEF          (* := *)
%token DEFINITION   (* Definition *)
%token COLON        (* : *)
%token COMMA        (* , *)
%token DIV          (* / *)
%token DOT          (* . *)
%token END          (* End *)
%token EOF
%token EQ           (* = *)
// %token EQUIV        (* <=> ⇔ *)
%token EXISTS       (* ∃ ? *)
%token FST          (* fst *)
%token GREATER      (* > *)
%token GREATEREQ    (* >= ⩾ *)
%token <Ast.ident> IDENT
// %token IMPLIES      (* => ⇒ *)
%token IN           (* in *)
%token <string> INT
// %token INDUCTIVE    (* Inductive *)
%token LAMBDA       (* lam λ *)
%token LBRACKET     (* { *)
%token LEMMA        (* Lemma *)
// %token LET          (* let *)
%token LOWER        (* < *)
%token LOWEREQ      (* <= ⩽ *)
%token LPAREN       (* ( *)
// %token LSBRACKET    (* [ *)
// %token MAPSTO       (* mapsto ↦ *)
%token MINUS        (* - *)
%token NEG          (* neg ¬ *)
%token ONGOING      (* Ongoing *)
%token OPEN         (* open *)
%token OR           (* or ∧ *)
%token PLUS         (* + *)
%token PROD
%token PROOF        (* Proof *)
%token QED          (* QED *)
%token RBRACKET     (* } *)
%token RPAREN       (* ) *)
// %token RSBRACKET    (* ] *)
%token SEMICOLON    (* ; *)
%token STAR         (* * *)
%token SND          (* snd *)
// %token SUMIN        (* sum_in *)
%token TACTIC       (* Tactic *)
%token THEOREM      (* Theorem *)
%token UNIT         (* Unit ⊤ *)
%token VARIABLES    (* Variables *)
// %token VERT         (* | *)
%token VERTVERT     (* || *)
%token VOID         (* Void ⊥ *)

%start file

%nonassoc EXISTS LAMBDA ALL
%left AMPERAMPER
%left VERTVERT
%right ARROW

%left COMMA
%left AND
%left OR
%left EQ GREATER LOWER LOWEREQ GREATEREQ
%left STAR PROD
%left PLUS MINUS
%left DIV
%nonassoc NEG SND FST

%type <(string * string) list * Tactic.raw_knel_file> file

%%

file:
    | list(opening) decl_list { $1, $2 }
;

opening:
    | OPEN parent IDENT {
        (List.fold_left
            (fun name _ -> "../"^name)
            (String.map (fun c -> if c = '.' then '/' else c) $3)
            $2,
        List.hd (List.rev (String.split_on_char '.' $3)))
    }
    | OPEN parent IDENT AS IDENT {
        (List.fold_left
            (fun name _ -> "../"^name)
            (String.map (fun c -> if c = '.' then '/' else c) $3)
            $2,
        $5)
    }
;

parent:
    | (* EMPTY *) { [] }
    | LOWER nonempty_list(MINUS) { $2 }

decl_list:
    | EOF                   { [] }
    | definition decl_list  { $1::$2 }
(*    | inductive decl_list   { $2 }*)
    | theorem decl_list     { $1::$2 }
    | tactic_decl decl_list { $1::$2 }
    | hypothesis_intro decl_list { $1::$2 }
;

hypothesis_intro:
    | VARIABLES EQ LBRACKET var_def_list { RawHypothesisSection $4 }
;

var_def_list:
    | var_def SEMICOLON var_def_list { $1::$3 }
    | var_def RBRACKET  { [$1] }
    | RBRACKET          { [] }
;

var_def:
    | IDENT COLON expr  { ($1, $3) }
;

tactic_decl:
    | TACTIC IDENT binding_list_ne EQ expr END
        { RawTacticDeclSection ($2, mk_lam $3 $5) }
;

// tac_arg_list_ne:
//     | LPAREN nonempty_list(IDENT) COLON expr RPAREN binding_list
//         { mk_pair_list $2 $4 @ $6 }
// ;

// tactic_arg_def_list:
//     | EQ expr END { $2 }
//     | tactic_arg_def tactic_arg_def_list { ELam ((fst $1, snd $1), $2) }

// tactic_arg_def:
//     | LPAREN IDENT COLON expr RPAREN { ($2, $4) }
// ;

// tactic_arg_type:
//     | INT       { TInt }
//     | TACTIC    { TTac }
//     | IDENT     { assert ($1 = "ident"); TIdent }
//     | tactic_arg_type ARROW tactic_arg_type { TArrow ($1, $3) }
// ;

definition:
    | DEFINITION IDENT binding_list COLON expr DEF expr END {
        let typ, expr = List.fold_right
            (fun (id, typ) (target_type, target_expr) ->
                EPi (("_", typ), target_type), ELam ((id, typ), target_expr))
            $3 ($5, $7)
        in
        RawDefinitionSection ($2, typ, expr) }
;
(*
inductive:
    | INDUCTIVE IDENT COLON type_decl EQ list(induc_bloc) END { $2 }
;

induc_bloc:
    | VERT IDENT COLON expr { ($2, $4) }
;
*)
theorem:
    | thm_keyword IDENT? COLON expr PROOF proof { RawReasoningSection ($1, $2, $4, fst $6, snd $6) }
;

thm_keyword:
    | LEMMA     { Lemma }
    | THEOREM   { Theorem }
;

proof:
    | expr SEMICOLON proof { $1::fst $3, snd $3 }
    | expr proof_end      { [$1], $2 }
    | proof_end             { [], $1 }
;

// tactic:
//     | no_app_tactic             { $1 }
// (*    | tactic_no_cmp LPAREN expr RPAREN { PTacApp ($1, PTacTerm $3) }
// *)
//     | tactic_no_cmp no_app_tactic
//         { PTacApp ($1, $2) }
//     | tactic VERTVERT tactic    { PTacOr ($1, $3) }
//     | tactic GREATER tactic     { PTacSeq ($1, $3) }
// ;

// tactic_no_cmp:
//     | no_app_tactic             { $1 }
//     | tactic_no_cmp no_app_tactic { PTacApp ($1, $2)}
// ;

// no_app_tactic:
//     | LSBRACKET expr RSBRACKET  { PTacExpr $2 }
//     | IDENT                     { PTacVar $1 }
//     | INT                       { PTacInt $1 }
//     | LPAREN tactic RPAREN      { $2 }
// (*    | LSBRACKET separated_list(SEMICOLON, IDENT) RSBRACKET
//         { PTacList $2 }*)
// ;

proof_end:
    | ADMITTED  { Admitted }
    | QED       { Qed }
    | ONGOING   { Ongoing }
;

// type_decl:
//     | type_decl ARROW type_decl { () }
//     | LPAREN type_decl RPAREN   { () }
//     | type_decl STAR type_decl  { () }
//     | IDENT                     { () }
// ;

expr:
    | ALL nonempty_list(IDENT) COLON expr COMMA expr %prec ALL 
        { mk_pi (mk_pair_list $2 $4) $6 }
    | EXISTS nonempty_list(IDENT) COLON expr COMMA expr %prec EXISTS
        { mk_sigma (mk_pair_list $2 $4) $6 }
    | LAMBDA nonempty_list(IDENT) COLON expr_no_arrow ARROW expr %prec LAMBDA
        { mk_lam (mk_pair_list $2 $4) $6 }
    | ALL binding_list_ne COMMA expr %prec ALL 
        { mk_pi $2 $4 }
    | EXISTS binding_list_ne COMMA expr %prec EXISTS
        { mk_sigma $2 $4 }
    | LAMBDA binding_list_ne ARROW expr %prec LAMBDA
        { mk_lam $2 $4 }
    | expr_in               { $1 }
    | expr binop_expr expr  { EApp (EApp(EConst $2, $1), $3) }
    | expr PROD expr        { ESigma (("_", $1), $3) }
    | expr ARROW expr     { EPi (("_", $1), $3) }
    | NEG expr              { EPi (("_", $2), EConst "Void") }
    | FST expr              { EFst $2 }
    | SND expr              { ESnd $2 }
;

expr_no_arrow:
    | ALL nonempty_list(IDENT) COLON expr DOT expr_no_arrow %prec ALL 
        { mk_pi (mk_pair_list $2 $4) $6 }
    | EXISTS nonempty_list(IDENT) COLON expr DOT expr_no_arrow %prec EXISTS
        { mk_sigma (mk_pair_list $2 $4) $6 }
    | LAMBDA nonempty_list(IDENT) COLON expr_no_arrow ARROW expr_no_arrow %prec LAMBDA
        { mk_lam (mk_pair_list $2 $4) $6 }
    | ALL binding_list_ne DOT expr_no_arrow %prec ALL 
        { mk_pi $2 $4 }
    | EXISTS binding_list_ne DOT expr_no_arrow %prec EXISTS
        { mk_sigma $2 $4 }
    | LAMBDA binding_list_ne ARROW expr_no_arrow %prec LAMBDA
        { mk_lam $2 $4 }
    | expr_in               { $1 }
    | expr_no_arrow COMMA expr_no_arrow       { EPair (($1, $3), None) }
    | expr_no_arrow binop_expr expr_no_arrow  { EApp (EApp(EConst $2, $1), $3) }
    | expr_no_arrow PROD expr_no_arrow        { ESigma (("_", $1), $3) }
    | NEG expr_no_arrow              { EPi (("_", $2), EConst "Void") }
    | FST expr_no_arrow              { EFst $2 }
    | SND expr_no_arrow              { ESnd $2 }
;

expr_in:
    | expr_in expr_bot  { EApp ($1, $2) }
    | expr_bot          { $1 }

expr_bot:
    | VOID                  { EConst "Void" }
    | UNIT                  { EConst "Unit" }
    | INT                   { EConst $1 }
    | IDENT                 { if $1 = "Type" then EConst "Type" else EVar $1 }
    | LPAREN expr COLON expr RPAREN    { ETaggedExpr ($2, $4) }
    | LPAREN expr RPAREN    { $2 }
    | LPAREN expr COMMA expr RPAREN     { EPair (($2, $4), None) }
    | LPAREN expr COMMA expr COMMA separated_nonempty_list(COMMA, expr) RPAREN
            { let lopt = List.fold_right (fun e1 e_tl -> match e_tl with
                | None -> Some e1
                | Some e2 -> Some (EPair ((e1, e2), None))) ($2::$4::$6) None
                in match lopt with
                    | None -> assert false
                    | Some e -> e }

    | LPAREN expr COMMA expr RPAREN IN expr_bot
        { EPair (($2, $4), Some $7) }
;

binding_list_ne:
    | LPAREN nonempty_list(IDENT) COLON expr RPAREN binding_list
        { mk_pair_list $2 $4 @ $6 }
;

binding_list:
    | LPAREN nonempty_list(IDENT) COLON expr RPAREN binding_list
        { mk_pair_list $2 $4 @ $6 }
    | (* EMPTY *) { [] }
;

%inline binop_expr:
    | PLUS      { "+" }
    | MINUS     { "-" }
    | STAR      { "*" }
    | DIV       { "/" }
    | EQ        { "=" }
    | GREATER   { ">" }
    | GREATEREQ { ">=" }
    | LOWER     { "<" }
    | LOWEREQ   { "<=" }
    | AND       { "and" }
    | OR        { "or" }
    | VERTVERT  { "||" }
    | AMPERAMPER {"&&" }
;
