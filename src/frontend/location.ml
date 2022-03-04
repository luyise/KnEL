type t =
  { loc_ghost : bool
  ; loc_start : Lexing.position
  ; loc_end : Lexing.position
  }

let none = {
  loc_ghost = false;
  loc_start = Lexing.dummy_pos;
  loc_end = Lexing.dummy_pos
}