open Ast

let constants : (id * term) list =
[ "Type" * (EConst "Type")
; "Void" * (EConst "Type")
; "void_ind" * (EPi (("C" , EConst "Type") , EPi (("_" , EConst "Void") , Var "C")))
      (* Π (C : Type) ⊥ → C *)
]