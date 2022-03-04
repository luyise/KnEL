
exception Not_strictly_positive

let rec check_strictly_positive : ident -> ident list -> expr -> bool
= fun name idl exp -> match exp with
  | EConst _ -> true
  | EVar _ -> true
  | ELam _ -> false
  | EApp (id , _)
  | EApp (exp1 , exp2) ->
      (not (List.mem name (get_varlib idl typ)))
  | EPi ((id , typ) , typ_over_typ) when id = "_" ->
      check_strictly_positive idl typ
      && check_strictly_positive idl typ'
  | EPi ((id , typ) , typ_over_typ) ->
      (not (List.mem name (get_varlib idl typ)))
      && check_strictly_positive (id :: idl) typ_over_typ
  | EPair _ -> false
  | ESigma ((id , typ) , typ_over_typ) when id = "_" ->
      check_strictly_positive idl typ
      && check_strictly_positive idl typ'
  | ESigma ((id , typ) , typ_over_typ) ->
      (not (List.mem name (get_varlib idl typ)))
      && check_strictly_positive (id :: idl) typ_over_typ
  | ETaggedExpr (exp1 , _) -> check_strictly_positive exp1 

exception Invalid_constructor_shape

let rec check_head : ident -> expr -> bool
= fun id exp -> match exp with
  | EConst _ -> false
  | EVar id' when id' = id -> true
  | EVar _ -> false
  | ELam _ -> false
  | EApp (EVar id , exp) -> true
  | EApp _ -> false
  | EPi ((id' , typ) , typ_over_typ) when id' = id -> false
  | EPi (_ , typ_over_typ) -> check_head id typ_over_typ
  | EPair _ -> false
  | ESigma ((id' , typ) , typ_over_typ) when id' = id -> false
  | ESigma (_ , typ_over_typ) -> check_head id typ_over_typ
  | ETaggedExpr (exp1 , _) -> check_head exp1