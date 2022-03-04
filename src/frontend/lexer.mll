{
    open Parser

    exception UnknownChar of char

    let kwd = [
        ("Admitted", ADMITTED);
        ("as", AS);
        ("Definition", DEFINITION);
        ("End", END);
        ("fst", FST);
        ("in", IN);
        (* ("Inductive", INDUCTIVE); *)
        ("lam", LAMBDA);
        ("Lemma", LEMMA);
        (* ("let", LET); *)
        (* ("mapsto", MAPSTO); *)
        ("neg", NEG);
        ("Ongoing", ONGOING);
        ("open", OPEN);
        ("Proof", PROOF);
        ("QED", QED);
        ("snd", SND);
        (* ("sum_in", SUMIN); *)
        ("Tactic", TACTIC);
        ("Theorem", THEOREM);
        (* ("Unit", UNIT); *)
        ("Variables", VARIABLES);
        (* ("Void", VOID); *)
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
let grec_lc = "α" | "β" | "γ" | "δ" | "ε" | "ζ" | "η" | "θ" | "ι" | "κ"(* λ *)| "μ" | "ν" | "ξ" | "ο" | "π" | "ρ" | "ς" | "σ" | "τ" | "υ" | "φ" | "χ" | "ψ" | "ω"
let grec_uc = "Α" | "Β" | "Γ" | "Δ" | "Ε" | "Ζ" | "Η" | "Θ" | "Ι" | "Κ" | "Λ" | "Μ" | "Ν" | "Ξ" | "Ο"  (*Π*)| "Ρ" | "Ϛ"  (*Σ*)| "Τ" | "Υ" | "Φ" | "Χ" | "Ψ" | "Ω"

let other_char = "∞"

let special = grec_lc | grec_uc | other_char

let integer = digit+

let letter = lower_case | upper_case | '_' | special

let word_mid = (letter | digit) *

let word_end = '.' word_mid

let ident = letter word_mid word_end*

let comment_smp = "//" [^'\n']*

let space = ' ' | '\t' | comment_smp

let integer = digit+

rule next_tokens = parse
    | space         { next_tokens lexbuf }
    | '\n'          { Lexing.new_line lexbuf; next_tokens lexbuf }
    | ident as id   { id_or_kwd id }
    | integer as i  { INT i }
    | "&&"          { AMPERAMPER }
    | '+'           { PLUS }
    | '-'           { MINUS }
    | '/'           { DIV }
    | ":"           { COLON }
    | '='           { EQ }
    (* | "=>" | "⇒"    { IMPLIES } *)
    | '<'           { LOWER }
    | "<="  | "⩽"   { LOWEREQ }
    | ">"           { GREATER }
    | ">="  | "⩾"   { GREATEREQ }
    (* | "<=>" | "⇔"   { EQUIV } *)
    | '('           { LPAREN }
    | ')'           { RPAREN }
    (* | '|'           { VERT } *)
    | "||"          { VERTVERT }
    | "->" | "→"    { ARROW }
    | '*'           { STAR }
    | "\u{00D7}"    { PROD } (* × *)
    | ','           { COMMA }
    | "\u{2200}" | '!' | "\u{03A0}"
        { ALL } (* ∀ Π *)
    | "\u{2203}" | '?' | "\u{03A3}"
        { EXISTS } (* ∃ Σ *)
    (* | "\u{21A6}"    { MAPSTO } *)
    (* ↦ *)
    | "\u{00AC}"    { NEG } (* ¬ *)
    | "\u{22A4}"    { UNIT } (* ⊤ *)
    | "\u{22A5}"    { VOID } (* ⊥ *)
    | "∧"           { AND }
    | "∨"           { OR }
    | "{"           { LBRACKET }
    | "}"           { RBRACKET }
    | "["           { LSBRACKET }
    | "]"           { RSBRACKET }
    | ";"           { SEMICOLON }
    | ":="          { DEF }
    | "\u{03BB}"    { LAMBDA } (* λ *)
    | "."           { DOT }
    | "&&"          { AMPERAMPER }
    | "||"          { VERTVERT }
    | eof           { EOF }
    | _ as c        { raise (UnknownChar c) }

{
    let next_token =
        next_tokens
}