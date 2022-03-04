open Ast

let constants : (ident * expr) list =
[ "Ord" , (EConst "_")
; "Void" , (EConst "Type")
; "void_ind" , (EPi (("C" , EConst "Type") , EPi (("_" , EConst "Void") , EVar "C")))
      (* Π (C : Type) ⊥ → C *)
]