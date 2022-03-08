%{

open Ast
open Location

let loc_of_pos (ps, pe) = {
    Location.loc_start = ps;
    Location.loc_end = pe;
    Location.loc_ghost = false;
}


let merge_loc p1 p2 = {
    Location.loc_start = p1.loc_start;
    Location.loc_end = p2.loc_end;
    Location.loc_ghost = p1.loc_ghost && p2.loc_ghost;
}

let mk_expr p e = { desc = e; loc = loc_of_pos p }
let add_loc e = { desc = e; loc = Location.none }
let ch_loc p e = {desc = e.desc; loc = loc_of_pos p}

let mk_sigma = List.fold_right (fun (b, p) e -> add_loc (PSigma (p, e , b)))
let mk_lam   = List.fold_right (fun (b, p) e -> add_loc (PLam   (p, e , b)))
let mk_pi    = List.fold_right (fun (b, p) e -> add_loc (PPi    (p, e , b)))

let mk_pair_list : ('a * Location.t) list -> ('b * parsed_expr) -> ('b * ('a * parsed_expr)) list =
    fun il (b, t) ->
      List.map (fun (i, loc) -> (b, (i, { t with loc = merge_loc loc t.loc }))) il


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
// %token FST          (* fst *)
%token GREATER      (* > *)
%token GREATEREQ    (* >= ⩾ *)
%token HYPOTHESIS   (* Hypothesis *)
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
// %token SND          (* snd *)
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


%type <(ident * parsed_expr) list * knel_file> file
%type <(ident * parsed_expr) list * (ident * parsed_expr * parsed_expr) list * knel_file> primitives

%%

file:
    | variables_intro? decl_list
      {
        (match $1 with
            | None -> []
            | Some l -> l),
        $2
      }
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
        OpenSection (
            List.fold_left
                (fun name _ -> "../"^name)
                (String.map (fun c -> if c = '.' then '/' else c) $3)
                $2,
            List.hd (List.rev (String.split_on_char '.' $3)),
            [])
    }
    | OPEN parent IDENT AS IDENT {
        OpenSection (
            (List.fold_left
                (fun name _ -> "../"^name)
                (String.map (fun c -> if c = '.' then '/' else c) $3)
                $2,
            $5,
            [])
        )
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
    | opening decl_list     { $1::$2 }
;

hypothesis_intro:
    | HYPOTHESIS EQ LBRACKET var_def_list { HypothesisSection $4 }
;

variables_intro:
    | VARIABLES EQ LBRACKET var_def_list { $4 }
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
        { TacDeclSection ($2, mk_lam $3 $5) }
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
            (fun (b, (id, typ)) (target_type, target_expr) ->
                add_loc (PPi (("_", typ), target_type, b)), add_loc (PLam ((id, typ), target_expr, b)))
            $3 ($5, $7)
        in
        DefinitionSection ($2, typ, expr) }
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
    | thm_keyword IDENT? COLON expr PROOF proof { ReasoningSection ($1, $2, $4, fst $6, snd $6) }
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
    | expr_in               { $1 }
    | expr_not_in           { $1 }
;

expr_not_in:
    | ALL nonempty_list(id_loc) COLON expr COMMA expr
        { ch_loc $loc (mk_pi (mk_pair_list $2 (Explicit, $4)) $6) }
    | EXISTS nonempty_list(id_loc) COLON expr COMMA expr
        { ch_loc $loc (mk_sigma (mk_pair_list $2 (Explicit, $4)) $6) }
    | LAMBDA nonempty_list(id_loc) COLON expr_bot ARROW expr
        { ch_loc $loc (mk_lam (mk_pair_list $2 (Explicit, $4)) $6) }
    | ALL binding_list_ne COMMA expr
        { ch_loc $loc (mk_pi $2 $4) }
    | EXISTS binding_list_ne COMMA expr
        { ch_loc $loc (mk_sigma $2 $4) }
    | LAMBDA binding_list_ne ARROW expr
        { ch_loc $loc (mk_lam $2 $4) }
    | NEG expr              { mk_expr $loc (PPi (("_", $2), add_loc (PVar "Void"), Explicit)) }
;

expr_in:
    | nonempty_list(expr_bot) 
        { match $1 with
            | [x] -> x
            | _ -> mk_expr $loc (PApp $1)
        }
    | nonempty_list(expr_bot) expr_not_in
        { mk_expr $loc (PApp ($1@[$2]))
        }
;

expr_bot:
    | VOID                  { mk_expr $loc (PVar "Void") }
    | UNIT                  { mk_expr $loc (PVar "Unit") }
    | INT                   { mk_expr $loc (PVar $1) }
    | IDENT                 { mk_expr $loc (PVar $1) }
    | ope                   { mk_expr $loc (PVar $1) }
  (*  | LPAREN expr COLON expr RPAREN    { mk_expr $loc (ETaggedExpr ($2, $4)) } *)
    | LPAREN expr RPAREN    { $2 }
    | LPAREN expr COMMA expr RPAREN     { mk_expr $loc (PPair (($2, $4), None)) }
    | LPAREN expr COMMA expr COMMA separated_nonempty_list(COMMA, expr) RPAREN
            { let lopt = List.fold_right (fun e1 e_tl -> match e_tl with
                | None -> Some e1
                | Some e2 -> Some (add_loc (PPair ((e1, e2), None)))) ($2::$4::$6) None
                in match lopt with
                    | None -> assert false
                    | Some e -> e }

    | LPAREN expr COMMA expr RPAREN IN expr_bot
        { mk_expr $loc (PPair (($2, $4), Some $7)) }
;

%inline ope:
    | VERTVERT      { "||" }
    | ARROW         { "→" }
    | AMPERAMPER    { "&&" }
    | PROD          { "×" }
;

binding_list_ne:
    | LPAREN nonempty_list(id_loc) COLON expr RPAREN binding_list
        { mk_pair_list $2 (Explicit, $4) @ $6 }
    | LBRACKET nonempty_list(id_loc) COLON expr RBRACKET binding_list
        { mk_pair_list $2 (Implicit, $4) @ $6 }
;

binding_list:
    | LPAREN nonempty_list(id_loc) COLON expr RPAREN binding_list
        { mk_pair_list $2 (Explicit, $4) @ $6 }
    | LBRACKET nonempty_list(id_loc) COLON expr RBRACKET binding_list
        { mk_pair_list $2 (Implicit, $4) @ $6 }
    | (* EMPTY *) { [] }
;

%inline id_loc:
    | IDENT     { ($1, loc_of_pos $loc) }

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
