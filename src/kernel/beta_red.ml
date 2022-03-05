open Parse
open Ast
open Substitution

type beta_rule_type = ident_list -> expr_desc -> expr_desc option

let lam_red : beta_rule_type
= function
  | EApp ({ desc = ELam ((x , _) , term_of_x) ; loc = _ } , v) ->
      Some (substitute idl x v term_of_x).desc
  | _ -> None

let fst_red : beta_rule_type
= function
  | EFst ({ desc = EPair ((left_exp , _) , _) ; loc = _}) ->
      Some left_exp.desc
  | _ -> None

let fst_red : beta_rule_type
= function
  | ESnd ({ desc = EPair ((_ , right_exp) , _) ; loc = _}) ->
      Some right_exp.desc
  | _ -> None

let primitive_beta_rules : beta_rule_type list =
[ lam_red
; fst_red
; snd_red
]

(* 
La fonction try_beta_rules prend en argument :
    une liste d'identifiants déjà utilisés,
    une liste de règle de beta-réduction
et tente d'appliquer les règles de beta-réduction successivement
jusqu'à ce que l'une d'entre elles s'applique ou qu'elle n'ait plus
de possibilité 
*)

let rec try_beta_rules : ident list -> beta_rule_type list -> expr_desc -> expr_desc option
= fun idl beta_rules_list exp ->
  match beta_rules_list with
    | [] -> None
    | rule :: rules_tail ->
      begin match rule idl exp with
        | Some exp' -> Some exp'
        | None -> try_beta_rules idl rules_tail exp
      end

(* la fonction beta_reduce_n prend en argument 
  une liste d'identifants déjà utilisés,
  une liste de règles de beta-réductions admissibles,
  un nombre de β-réduction maximal à effectuer,
  le terme à β-réduire
  et tente d'effectuer n β-réductions, il renvoie ensuite le nombre de réductions éffectuées *)

let rec beta_reduce_n_inner : ident list -> beta_rule_type list -> int -> expr_desc -> expr_desc * int
= fun idl brl n exp ->
  if n < 0 then failwith "KnEL Internal Error : Can't reduce a negative number of time something!"
  else if n = 0 then (exp , 0)
  else match try_beta_rules idl brl exp with
    | Some exp' ->
        let final_exp , nb_of_red =
          beta_reduce_n_inner idl brl (n-1) exp'
        in (exp' , nb_of_red + 1)
    | None ->
      begin match exp with
        | EConst c -> (EConst c , 0)
        | EVar x -> (EVar x , 0)
        | ELam ((y , typ) , term_of_y) ->
            let typ' , k = beta_reduce_n_inner idl brl n typ in
            let term_of_y' , j = beta_reduce_n_inner (y :: idl) brl (n-k) term_of_y in
            (ELam ((y , typ') , term_of_y') , k + j)
        | EApp (u , v) ->
            let u' , k = beta_reduce_n_inner idl brl n u in
            let v' , j = beta_reduce_n_inner idl brl (n-k) v in
            (EApp (u' , v') , k + j)
        | EPi ((y , typ) , term_of_y) ->
            let typ' , k = beta_reduce_n_inner idl brl n typ in
            let term_of_y' , j = beta_reduce_n_inner (y :: idl) brl (n-k) term_of_y in
            (EPi ((y , typ') , term_of_y') , k + j)
        | EPair ((exp1 , exp2) , Some typ) ->
            let exp1' , k = beta_reduce_n_inner idl brl n exp1 in
            let exp2' , j = beta_reduce_n_inner idl brl (n-k) exp2 in
            let typ' , i = beta_reduce_n_inner idl brl (n-k-j) typ in
            (EPair ((exp1' , exp2') , Some typ') , k + j + i)
        | EPair ((exp1 , exp2) , None) ->
            let exp1' , k = beta_reduce_n_inner idl brl n exp1 in
            let exp2' , j = beta_reduce_n_inner idl brl (n-k) exp2 in
            (EPair ((exp1' , exp2') , None) , k + j + i)
        | EFst exp1 ->
            let exp1' , k = beta_reduce_n_inner idl brl n exp1 in
            (EFst exp1' , k)
        | ESnd exp1 ->
            let exp1' , k = beta_reduce_n_inner idl brl n exp1 in
            (EFst exp1' , k)
        | ESigma ((y , typ) , term_of_y) ->
            let typ' , k = beta_reduce_n_inner idl brl n typ in
            let term_of_y' , j = beta_reduce_n_inner (y :: idl) brl (n-k) term_of_y in
            (ESigma ((y , typ') , term_of_y') , k + j)
        | EAbs (_ , _) -> (exp , 0)
      end

let beta_reduce_n_desc : ident list -> beta_rule_type list -> int -> expr_desc -> expr_desc
= fun idl brl n exp -> fst (beta_reduce_n idl brl n exp)

let beta_reduce_n : ident list -> beta_rule_type list -> int -> expr -> expr
= fun idl brl n exp ->
  { exp with desc = beta_reduce_n_desc idl brl n exp.desc }

let rec beta_reduce_decl : ident list -> beta_rule_type list -> expr_desc -> expr_desc
= fun idl brl exp ->
  let exp' , n = beta_reduce_n idl brl 100 exp.desc in
  if n < 100 then exp'
  else beta_reduce_decl idl brl exp'
  
let beta_reduce : ident list -> beta_rule_type liste -> expr -> expr
= fun idl brl exp ->
  { exp with desc = beta_reduce_decl idl brl exp.desc }