%{

open Ast
open Tactic

let loc_of_pos (ps, pe) = {
    Location.loc_start = ps;
    Location.loc_end = pe;
    Location.loc_ghost = false;
}


let mk_expr p e = { desc = e; loc = loc_of_pos p }
let add_loc e = { desc = e; loc = Location.none }
let ch_loc p e = {desc = e.desc; loc = loc_of_pos p}

let mk_sigma = List.fold_right (fun p e -> add_loc (ESigma (p, e)))
let mk_lam = List.fold_right (fun p e -> add_loc (ELam (p, e)))
let mk_pi = List.fold_right (fun p e -> add_loc (EPi (p, e)))

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
%token LSBRACKET    (* [ *)
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
%token RSBRACKET    (* ] *)
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
%start primitives

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
%type <(ident * expr) list * (ident * expr * expr) list * Tactic.raw_knel_file> primitives

%%

file:
    | list(opening) decl_list { $1, $2 }
;

primitives:
    | EOF { ([], [], []) }
    | primitives_decl SEMICOLON primitives
        { let a, b, c = $3 in $1::a, b, c }
    | beta_rules SEMICOLON primitives
        { let a, b, c = $3 in a, $1::b, c }
    | definition SEMICOLON primitives
        { let a, b, c = $3 in a, b, $1::c }
;

primitives_decl:
    | IDENT COLON expr { ($1, $3) }
;

beta_rules:
    | LSBRACKET IDENT RSBRACKET expr_in EQ expr_in { ($2, $4, $6) }
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
                add_loc (EPi (("_", typ), target_type)), add_loc (ELam ((id, typ), target_expr)))
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
        { ch_loc $loc (mk_pi (mk_pair_list $2 $4) $6) }
    | EXISTS nonempty_list(IDENT) COLON expr COMMA expr %prec EXISTS
        { ch_loc $loc (mk_sigma (mk_pair_list $2 $4) $6) }
    | LAMBDA nonempty_list(IDENT) COLON expr_no_arrow ARROW expr %prec LAMBDA
        { ch_loc $loc (mk_lam (mk_pair_list $2 $4) $6) }
    | ALL binding_list_ne COMMA expr %prec ALL 
        { ch_loc $loc (mk_pi $2 $4) }
    | EXISTS binding_list_ne COMMA expr %prec EXISTS
        { ch_loc $loc (mk_sigma $2 $4) }
    | LAMBDA binding_list_ne ARROW expr %prec LAMBDA
        { ch_loc $loc (mk_lam $2 $4) }
    | expr_in               { $1 }
    | expr binop_expr expr  { mk_expr $loc (EApp (add_loc (EApp(add_loc (EConst $2), $1)), $3)) }
    | expr PROD expr        { mk_expr $loc (ESigma (("_", $1), $3)) }
    | expr ARROW expr       { mk_expr $loc (EPi (("_", $1), $3)) }
    | NEG expr              { mk_expr $loc (EPi (("_", $2), add_loc (EConst "Void"))) }
    | FST expr              { mk_expr $loc (EFst $2) }
    | SND expr              { mk_expr $loc (ESnd $2) }
;

expr_no_arrow:
    | ALL nonempty_list(IDENT) COLON expr DOT expr_no_arrow %prec ALL 
        { ch_loc $loc (mk_pi (mk_pair_list $2 $4) $6) }
    | EXISTS nonempty_list(IDENT) COLON expr DOT expr_no_arrow %prec EXISTS
        { ch_loc $loc (mk_sigma (mk_pair_list $2 $4) $6) }
    | LAMBDA nonempty_list(IDENT) COLON expr_no_arrow ARROW expr_no_arrow %prec LAMBDA
        { ch_loc $loc (mk_lam (mk_pair_list $2 $4) $6) }
    | ALL binding_list_ne DOT expr_no_arrow %prec ALL 
        { ch_loc $loc (mk_pi $2 $4) }
    | EXISTS binding_list_ne DOT expr_no_arrow %prec EXISTS
        { ch_loc $loc (mk_sigma $2 $4) }
    | LAMBDA binding_list_ne ARROW expr_no_arrow %prec LAMBDA
        { ch_loc $loc (mk_lam $2 $4) }
    | expr_in               { $1 }
    | expr_no_arrow COMMA expr_no_arrow       { mk_expr $loc (EPair (($1, $3), None)) }
    | expr_no_arrow binop_expr expr_no_arrow
        { mk_expr $loc (EApp (add_loc (EApp (add_loc (EConst $2), $1)), $3)) }
    | expr_no_arrow PROD expr_no_arrow        { mk_expr $loc (ESigma (("_", $1), $3)) }
    | NEG expr_no_arrow              { mk_expr $loc (EPi (("_", $2), add_loc (EConst "Void"))) }
    | FST expr_no_arrow              { mk_expr $loc (EFst $2) }
    | SND expr_no_arrow              { mk_expr $loc (ESnd $2) }
;

expr_in:
    | expr_in expr_bot  { mk_expr $loc (EApp ($1, $2)) }
    | expr_bot          { $1 }

expr_bot:
    | VOID                  { mk_expr $loc (EConst "Void") }
    | UNIT                  { mk_expr $loc (EConst "Unit") }
    | INT                   { mk_expr $loc (EConst $1) }
    | IDENT                 { mk_expr $loc (EVar $1) }
  (*  | LPAREN expr COLON expr RPAREN    { mk_expr $loc (ETaggedExpr ($2, $4)) } *)
    | LPAREN expr RPAREN    { $2 }
    | LPAREN expr COMMA expr RPAREN     { mk_expr $loc (EPair (($2, $4), None)) }
    | LPAREN expr COMMA expr COMMA separated_nonempty_list(COMMA, expr) RPAREN
            { let lopt = List.fold_right (fun e1 e_tl -> match e_tl with
                | None -> Some e1
                | Some e2 -> Some (add_loc (EPair ((e1, e2), None)))) ($2::$4::$6) None
                in match lopt with
                    | None -> assert false
                    | Some e -> e }

    | LPAREN expr COMMA expr RPAREN IN expr_bot
        { mk_expr $loc (EPair (($2, $4), Some $7)) }
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
