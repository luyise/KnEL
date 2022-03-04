open Ast

let get_unused_ident : (ident list) -> ident
= fun id_list ->
  let idents_starting_by_x = 
    List.filter_map
    (fun id -> 
      if id.[0] = 'x' then 
        Some (String.sub id 1 ((String.length id) - 1))
      else None
    ) id_list
  in
  let i = ref 0 in
  while (List.mem (string_of_int (! i)) idents_starting_by_x) do
    incr i
  done;
  ("x" ^ (string_of_int (! i)))

exception Cannot_rename_a_constant
exception Ident_colision

(* rename prend en paramètre un environement de preuve courant, 
  deux identifiant x et y, un terme exp.
  La fonction vérifie que y n'est pas un identifiant existant ailleurs dans
  l'environnement puis renomme la variable x en y dans l'expression fournie.
  Enfin, elle renvoie le terme obtenu. *)

let rec rename : ident list -> ident -> ident -> expr -> expr
= fun idl x y exp ->
  if (List.mem y idl) then raise Ident_colision
  else let desc : expr_desc =
  match exp.desc with
    | EConst z when z = x -> raise Cannot_rename_a_constant
    | EConst _ -> exp.desc

    | EVar z when z = x -> EVar y
    | EVar _ -> exp.desc

    | ELam ((z , _) , _) when z = x -> exp.desc
    | ELam ((z , typ) , term) when z = y ->
        let z' = get_unused_ident idl in
        let typ' = rename idl x y typ in
        let idl' = z' :: idl in
        let term' = rename idl' x y term in
        ELam ((z' , typ') , term')
    | ELam ((z , typ) , term) ->
        let typ' = rename idl x y typ in
        let idl' = if z = "_" then idl else (z :: idl) in
        let term' = rename idl' x y term in
        ELam ((z , typ') , term')

    | EApp (exp1 , exp2) ->
        EApp (rename idl x y exp1 , rename idl x y exp2)

    | EPi ((z , _) , _) when z = x -> exp.desc
    | EPi ((z , typ) , term) when z = y ->
        let z' = get_unused_ident idl in
        let typ' = rename idl x y typ in
        let idl' = z' :: idl in
        let term' = rename idl' x y term in
        EPi ((z' , typ') , term')
    | EPi ((z , typ) , term) ->
        let typ' = rename idl x y typ in
        let idl' = if z = "_" then idl else (z :: idl) in
        let term' = rename idl' x y term in
        EPi ((z , typ') , term')
      
    | EPair ((exp1 , exp2) , typ_op) ->
        let typ_op' =
          match typ_op with
            | Some typ -> Some (rename idl x y typ)
            | None -> None
        in
        EPair ((rename idl x y exp1 , rename idl x y exp2) , typ_op')

    | EFst term -> EFst (rename idl x y term)
    | ESnd term -> ESnd (rename idl x y term)

    | ESigma ((z , _) , _) when z = x -> exp.desc
    | ESigma ((z , typ) , term) when z = y ->
        let z' = get_unused_ident idl in
        let typ' = rename idl x y typ in
        let idl' = z' :: idl in
        let term' = rename idl' x y term in
        ESigma ((z' , typ') , term')
    | ESigma ((z , typ) , term) ->
        let typ' = rename idl x y typ in
        let idl' = if z = "_" then idl else (z :: idl) in
        let term' = rename idl' x y term in
        ESigma ((z , typ') , term')
        
    | ETaggedExpr (term , typ) ->
        ETaggedExpr (rename idl x y term , rename idl x y typ)
  in
  { desc = desc
  ; loc = exp.loc
  }