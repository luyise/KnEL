{
    open Ast
    open Parser

    exception UnknownChar

    let kwd = [
        ("Admitted", ADMITTED);
        ("Definition", DEFINITION);
        ("End", END);
        ("in", IN);
        ("Inductive", INDUCTIVE);
        ("lam", LAMBDA);
        ("Lemma", LEMMA);
        ("let", LET);
        ("mapsto", MAPSTO);
        ("neg", NEG);
        ("Ongoing", ONGOING);
        ("Proof", PROOF);
        ("QED", QED);
        ("sum_in", SUMIN);
        ("Tactic", TACTIC);
        ("Theorem", THEOREM);
        ("Unit", UNIT);
        ("Variables", VARIABLES);
        ("Void", VOID);
    ]

    let id_or_kwd =
        let h = Hashtbl.create 32 in
        List.iter (fun (s, tok) -> Hashtbl.add h s tok) kwd;
        fun s ->
            try 
                Hashtbl.find h s
            with Not_found -> IDENT s
}

let lower_case = ['a'-'z']
let upper_case = ['A'-'Z']
let digit = ['0'-'9']
let integer = digit+

let letter = lower_case | upper_case | '_'

let ident = letter (letter | digit)*

let comment_smp = "//" [^'\n']*

let space = ' ' | '\t' | comment_smp

let integer = digit+

rule next_tokens = parse
    | space         { next_tokens lexbuf }
    | '\n'          { Lexing.new_line lexbuf; next_tokens lexbuf }
    | ident as id   { id_or_kwd id }
    | integer as i  { INT (int_of_string i) }
    | "&&"          { AMPERAMPER }
    | '+'           { PLUS }
    | '-'           { MINUS }
    | '/'           { DIV }
    | ":"           { COLON }
    | '='           { EQ }
    | "=>" | "⇒"    { IMPLIES }
    | '<'           { LOWER }
    | "<="  | "⩽"   { LOWEREQ }
    | ">"           { GREATER }
    | ">="  | "⩾"   { GREATEREQ }
    | "<=>" | "⇔"   { EQUIV }
    | '('           { LPAREN }
    | ')'           { RPAREN }
    | '|'           { VERT }
    | "||"          { VERTVERT }
    | "->" | "→"    { ARROW }
    | '*'           { STAR }
    | "\u{00D7}"    { PROD } (* × *)
    | ','           { COMMA }
    | "\u{2200}"|'!'{ ALL } (* ∀ *)
    | "\u{2203}"|'?'{ EXISTS } (* ∃ *)
    | "\u{21A6}"    { MAPSTO } (* ↦ *)
    | "\u{00AC}"    { NEG } (* ¬ *)
    | "\u{22A4}"    { UNIT } (* ⊤ *)
    | "\u{22A5}"    { VOID } (* ⊥ *)
    | "{"           { LBRACKET }
    | "}"           { RBRACKET }
    | "["           { LSBRACKET }
    | "]"           { RSBRACKET }
    | ";"           { SEMICOLON }
    | "\u{033B}"    { LAMBDA } (* λ *)
    | eof           { EOF }
    | _             { raise UnknownChar }

{
    let next_token =
        next_tokens
}