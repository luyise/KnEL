{
    open Parser

    let kwd = [
        ("Proof", PROOF);
        ("Theorem", THEOREM);
        ("Lemma", LEMMA);
        ("Definition", DEFINITION);
        ("mapsto", MAPSTO);
        ("let", LET);
        ("Qed", QED);
        ("Admitted", ADMITTED);
        ("Inductive", INDUCTIVE);
        ("End", END);
        ("neg", NEG);
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

let space = ' ' | '\t' | '\n' | comment_smp

rule next_tokens = parse
    | space         { next_tokens lexbuf }
    | ident as id   { id_or_kwd id }
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
    | '×'           { PROD }
    | ','           { COMMA }
 (*   | '∀' | '!'     { ALL } *)
(*    | '∃' | '?'     { EXISTS } 
    | '↦'           { MAPSTO }
    | '¬'           { NEG }*)
    | eof           { EOF }

{
    let next_token =
        next_token
}