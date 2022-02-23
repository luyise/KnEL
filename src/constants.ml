open Ast

let constants : (id * term option) array =
[| "Type" * None
 ; "Void" * Some (EConst "Type")
 ; "void_ind" * Some (EPi (("C" , EConst "Type") , EPi (("_" , EConst "Void") , Var "C")))
      (* Π (C : Type) ⊥ → C *)
|]