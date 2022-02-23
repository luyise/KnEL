open Ast
open Environment

let get_unused_ident : (ident list) -> ident
= fun id_list ->
  let idents_starting_by_x = 
    List.filter_map
    (fun id -> 
      if id.[0] = 'x' then 
        Some (String.sub idp 1 (String.length id))
      else None
    ) id_list
  in
  let i = ref 0 in
  while (List.mem (string_of_int (! i)) idents_starting_by_x) do
    incr i
  done;
  ("x" ^ (string_of_int (! i)))

exception Cannot_rename_a_constant

(* rename prend en paramètre un environement de preuve courant, 
  deux identifiant x et y, un terme exp.
  La fonction vérifie que y n'est pas un identifiant existant ailleurs dans
  l'environnement puis renomme la variable x en y dans l'expression fournie.
  Enfin, elle renvoie le terme obtenu. *)

let rec rename : ident list -> ident -> ident -> expr -> expr
= fun idl x y exp ->
  if (List.mem y idl) then raise Ident_colision
  else begin match exp with
    | EConst z when z = x -> raise Cannot_rename_a_constant
    | EConst z -> exp

    | EVar z when z = x -> EVar y
    | EVar z -> exp

    | ELam ((z , typ) , term) when z = x -> exp
    | ELam ((z , typ) , term) when z = y ->
        let z' = get_unused_ident idl in
        let typ' = rename idl x y typ in
        let idl' = z' :: idl in
        let term' = rename idl' x y typ in
        ELam ((z' , typ') , term')
    | ELam ((z , typ) , term) ->
        let typ' = rename idl x y typ in
        let idl' = z :: idl in
        let term' = rename idl' x y typ in
        ELam ((z , typ') , term')
    | EApp (exp1 , exp2) ->
        EApp (rename idl x y exp1 , rename idl x y exp2)

    | EPi ((z , typ) , term) when z = x -> exp
    | EPi ((z , typ) , term) when z = y ->
        let z' = get_unused_ident idl in
        let typ' = rename idl x y typ in
        let idl' = z' :: idl in
        let term' = rename idl' x y typ in
        EPi ((z' , typ') , term')
    | EPi ((z , typ) , term) ->
        let typ' = rename idl x y typ in
        let idl' = z :: idl in
        let term' = rename idl' x y typ in
        EPi ((z , typ') , term')
      
    | EPair ((exp1 , exp2) , typ_op) ->
        let typ_op' =
          match typ_op with
            | Some typ -> rename idl x y typ
            | None -> None
        in
        EPair ((rename idl x y exp1 , rename idl x y exp2) , typ_op')

    | EFst term -> EFst (rename idl x y term)
    | ESnd term -> ESnd (rename idl x y term)

    | ESigma ((z , typ) , term) when z = x -> exp
    | ESigma ((z , typ) , term) when z = y ->
        let z' = get_unused_ident idl in
        let typ' = rename idl x y typ in
        let idl' = z' :: idl in
        let term' = rename idl' x y typ in
        ESigma ((z' , typ') , term')
    | ESigma ((z , typ) , term) ->
        let typ' = rename idl x y typ in
        let idl' = z :: idl in
        let term' = rename idl' x y typ in
        ESigma ((z , typ') , term')
      (* Correspond à une expression dont le type a été forcé par l'utilisateur *)
    | ETaggedExpr (term , typ) ->
        ETaggedExpr (rename idl x y term , rename idl x y typ)
  end