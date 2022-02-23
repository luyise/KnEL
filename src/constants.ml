open Ast

let constants : (ident * expr) list =
[ "Type" , (EConst "Type")
; "Void" , (EConst "Type")
; "void_ind" , (EPi (("C" , EConst "Type") , EPi (("_" , EConst "Void") , EVar "C")))
      (* Π (C : Type) ⊥ → C *)
]