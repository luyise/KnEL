open Ast

let (myTarget : expr) =
EPi(("_" ,
  EPi(
    ("x" , EVar "X") ,
    ESigma(
      ("y" , EVar "Y") ,
      EApp (EApp (EVar "P" , EVar "x") , EVar "y")
    )
  )) ,
  ESigma(
    ("f" , EPi (("_" , EVar "X") , EVar "Y")) ,
    EPi(
      ("x" , EVar "X") ,
      EApp (EApp (EVar "P" , EVar "x") , EApp (EVar "f" , EVar "x"))
    )
  )
)

let (myBaseTacticList : base_tactic list) =
[ IntroTac "H" 
; SplitTac (
    ELam(
      ("x", EVar "X") ,
      EFst (
        EApp (
          EVar "H" , EVar "x"
        )
      )
    )
  )
; IntroTac "x"
; ExactTac(
    ESnd(
      EApp(
        EVar "H",
        EVar "x"
      )
    )
  )
]

let (mySectionDef : knel_section) =
HypothesisSection (
[ "X" , EConst "Type"
; "Y" , EConst "Type"
; "P" , EPi (("_" , EVar "X") , EPi(("_", EVar "Y") , EConst "Type"))
])

let (mySectionThm : knel_section) =
ReasoningSection(
  Theorem ,
  Some "Choice" ,
  myTarget ,
  (List.map (fun t -> BaseTac t) myBaseTacticList),
  Qed
)

let (myFile : knel_file) =
  [ mySectionDef ; mySectionThm ]