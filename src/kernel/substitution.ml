open Parse
open Ast
open Renaming

(* Le premier context correspond aux variables liées *)

let rec get_varlib : ident list -> expr -> ident list
= fun varlie term ->
  match term.desc with
    | EConst _ -> []
    | EVar x ->
        if List.mem x varlie then []
        else [ x ]
    | ELam ((x , typ) , term_of_x) ->
        if x = "_" then (get_varlib varlie typ) @ (get_varlib varlie term_of_x)
        else (get_varlib varlie typ) @ (get_varlib (x :: varlie) term_of_x)
    | EApp (exp1 , exp2) ->
        (get_varlib varlie exp1) @ (get_varlib varlie exp2)
    | EPi ((x , typ) , typ_over_typ) ->
        if x = "_" then (get_varlib varlie typ) @ (get_varlib varlie typ_over_typ)
        else (get_varlib varlie typ) @ (get_varlib (x :: varlie) typ_over_typ)
    | EPair ((exp1 , exp2) , Some typ) ->
        (get_varlib varlie exp1) @ (get_varlib varlie exp2) @ (get_varlib varlie typ)
    | EPair ((exp1 , exp2) , None) ->
        (get_varlib varlie exp1) @ (get_varlib varlie exp2)
    | EFst exp ->
        (get_varlib varlie exp)
    | ESnd exp ->
        (get_varlib varlie exp)
    | ESigma ((x , typ) , typ_over_typ) ->
        if x = "_" then (get_varlib varlie typ) @ (get_varlib varlie typ_over_typ)
        else (get_varlib varlie typ) @ (get_varlib (x :: varlie) typ_over_typ)
    | ETaggedExpr (exp , typ) ->
        (get_varlib varlie typ) @ (get_varlib varlie exp)
    

(* substitute idl varlib x term expr renvoie l'expression expr' dans laquelle les occurences libres de la variable
  x ont été remplacés par le terme term, idl contient le nom des variables déjà utilisées dans l'environment courant,
  varlib contient les variables libres de term, afin de ne pas engendrer de capture lors de la substition
  /!\ la fonction doit être appellée avec varlib inclus dans idl ! *)

let rec substitute_inner : ident list -> ident list -> ident -> expr -> expr -> expr
= fun idl varlib x term exp ->
  let desc = 
  match exp.desc with
    | EConst _ -> exp.desc

    | EVar y when y = x -> term.desc
    | EVar _ -> exp.desc

    | ELam ((y , typ) , term_of_y) when y = x ->
        if List.mem x varlib then begin
          let z = get_unused_ident (x :: idl) in
          let term_of_z = rename idl x z term_of_y in
          let typ' = substitute_inner (z :: idl) varlib x term typ in
          ELam ((z , typ') , term_of_z)
        end else begin
          let typ' = substitute_inner (x :: idl) varlib x term typ in
          ELam ((x , typ') , term_of_y)
        end
    | ELam ((y , typ) , term_of_y) ->
        if List.mem y varlib then begin
          let z = get_unused_ident (y :: idl) in
          let term_of_z = rename idl y z term_of_y in
          let typ' = substitute_inner (z :: idl) varlib x term typ in
          let term_of_z' = substitute_inner (z :: idl) varlib x term term_of_z in
          ELam ((z , typ') , term_of_z')
        end else begin
          let idl' = if y = "_" then idl else (y :: idl) in
          let typ' = substitute_inner idl' varlib x term typ in
          let term_of_y' = substitute_inner idl' varlib x term term_of_y in
          ELam ((y , typ') , term_of_y')
        end

    | EApp (exp1 , exp2) ->
        EApp (substitute_inner idl varlib x term exp1 , substitute_inner idl varlib x term exp2)

    | EPi ((y , typ) , term_of_y) when y = x ->
        if List.mem x varlib then begin
          let z = get_unused_ident (x :: idl) in
          let term_of_z = rename idl x z term_of_y in
          let typ' = substitute_inner (z :: idl) varlib x term typ in
          EPi ((z , typ') , term_of_z)
        end else begin
          let typ' = substitute_inner (x :: idl) varlib x term typ in
          EPi ((x , typ') , term_of_y)
        end
    | EPi ((y , typ) , term_of_y) ->
        if List.mem y varlib then begin
          let z = get_unused_ident (y :: idl) in
          let term_of_z = rename idl y z term_of_y in
          let typ' = substitute_inner (z :: idl) varlib x term typ in
          let term_of_z' = substitute_inner (z :: idl) varlib x term term_of_z in
          EPi ((z , typ') , term_of_z')
        end else begin
          let idl' = if y = "_" then idl else (y :: idl) in
          let typ' = substitute_inner idl' varlib x term typ in
          let term_of_y' = substitute_inner idl' varlib x term term_of_y in
          EPi ((y , typ') , term_of_y')
        end

    | EPair ((exp1 , exp2) , Some typ) ->
        let exp1' = substitute_inner idl varlib x term exp1 in
        let exp2' = substitute_inner idl varlib x term exp2 in
        let typ' = substitute_inner idl varlib x term typ in
        EPair ((exp1' , exp2') , Some typ')

    | EPair ((exp1 , exp2) , None) ->
        let exp1' = substitute_inner idl varlib x term exp1 in
        let exp2' = substitute_inner idl varlib x term exp2 in
        EPair ((exp1' , exp2') , None)

    | EFst exp1 -> EFst (substitute_inner idl varlib x term exp1)
    | ESnd exp1 -> ESnd (substitute_inner idl varlib x term exp1)

    | ESigma ((y , typ) , term_of_y) when y = x ->
        if List.mem x varlib then begin
          let z = get_unused_ident (x :: idl) in
          let term_of_z = rename idl x z term_of_y in
          let typ' = substitute_inner (z :: idl) varlib x term typ in
          ESigma ((z , typ') , term_of_z)
        end else begin
          let typ' = substitute_inner (x :: idl) varlib x term typ in
          ESigma ((x , typ') , term_of_y)
        end
    | ESigma ((y , typ) , term_of_y) ->
        if List.mem y varlib then begin
          let z = get_unused_ident (y :: idl) in
          let term_of_z = rename idl y z term_of_y in
          let typ' = substitute_inner (z :: idl) varlib x term typ in
          let term_of_z' = substitute_inner (z :: idl) varlib x term term_of_z in
          ESigma ((z , typ') , term_of_z')
        end else begin
          let idl' = if y = "_" then idl else (y :: idl) in
          let typ' = substitute_inner idl' varlib x term typ in
          let term_of_y' = substitute_inner idl' varlib x term term_of_y in
          ESigma ((y , typ') , term_of_y')
        end
      (* Correspond à une expression dont le type a été forcé par l'utilisateur *)
    | ETaggedExpr (exp1 , typ) ->
        let exp1' = substitute_inner idl varlib x term exp1 in
        let typ' = substitute_inner idl varlib x term typ in
        ETaggedExpr (exp1' , typ')
  in
  { desc = desc
  ; loc = exp.loc }

(* même que la précédente, mais dump les variables libres de term dans idl avant de calculer la substitution *)

let substitute : ident list -> ident -> expr -> expr -> expr
= fun idl x term exp ->
  let varlib = get_varlib [] term in
  substitute_inner (varlib @ idl) varlib x term exp