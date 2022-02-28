open Ast

exception TacticTypeError
exception UndefinedTactic of ident

module SMap = Map.Make(String)
module SSet = Set.Make(String)

let seq_op = "&&"
let  or_op = "||"

let pp_ident fmt id = Format.fprintf fmt "%s" id

type tactic_ident =
  | TIIntro
  | TIApply
  | TISigmaRec
  | TIExact
  | TITry
  | TIDo
  | TIDefine
  | TIUnfold
  | TIReduce

type tactic_expr =
  | TEConst of ident
  | TEVar of ident
  | TELam of (ident * tactic_expr) * tactic_expr
  | TEApp of tactic_expr * tactic_expr
  | TEPi of (ident * tactic_expr) * tactic_expr
  | TEPair of (tactic_expr * tactic_expr) * (tactic_expr option)
  | TEFst of tactic_expr
  | TESnd of tactic_expr
  | TESigma of (ident * tactic_expr) * tactic_expr
  | TETaggedExpr of tactic_expr * tactic_expr
  | TEReplace of ident

type parsed_tactic =
  | PTacReplace of ident
  | PTacVar of ident
  | PTacInt of int
  | PTacExpr of tactic_expr
  | PTacSeq of parsed_tactic * parsed_tactic
  | PTacOr of parsed_tactic * parsed_tactic
  | PTacApp of parsed_tactic * parsed_tactic
  | PTacBase of tactic_ident

type tactic_type =
  | TExpr
  | TInt
  | TIdent
  | TTac
  | TArrow of tactic_type * tactic_type
  | TUnknown

type tactic_builder =
  | Tactic of parsed_tactic
  | Arg of ident * tactic_type * tactic_builder

type raw_knel_section =
  | RawHypothesisSection of context
  | RawReasoningSection of 
      (beggining_tag * 
        ident option * 
        expr *
        expr list *
      ending_tag)
  | RawTacticDeclSection of ident * expr
  | RawDefinitionSection of ident * expr * expr

type raw_knel_file = raw_knel_section list

type tactic_env =
  | TacEnv of (tactic_type * tactic_builder * tactic_env) SMap.t

type tactic_ctxt = (tactic_type * tactic_builder * tactic_env) SMap.t

let rec texpr_of_expr env bindings = function
    | EVar id when SSet.mem id bindings -> TEVar id
    | EVar id when SMap.find_opt id env = None -> TEVar id
    | EVar id when SMap.find_opt id env = Some TExpr -> TEReplace id
    | EVar id when SMap.find_opt id env = Some TIdent -> TEReplace id
    | EVar _ -> assert false
    | EConst id -> TEConst id
    | ELam ((id, e1), e2) -> TELam ((id, texpr_of_expr env bindings e1), texpr_of_expr env (SSet.add id bindings) e2)
    | EApp (e1, e2) -> TEApp (texpr_of_expr env bindings e1, texpr_of_expr env bindings e2)
    | EPi ((id, e1), e2) -> TEPi ((id, texpr_of_expr env bindings e1), texpr_of_expr env (SSet.add id bindings) e2)
    | ESigma ((id, e1), e2) -> TESigma ((id, texpr_of_expr env bindings e1), texpr_of_expr env (SSet.add id bindings) e2)
    | EPair ((e1, e2), None) -> TEPair ((texpr_of_expr env bindings e1, texpr_of_expr env bindings e2), None)
    | EPair ((e1, e2), Some e3) -> TEPair ((texpr_of_expr env bindings e1, texpr_of_expr env bindings e2), Some (texpr_of_expr env bindings e3))
    | EFst e -> TEFst (texpr_of_expr env bindings e)
    | ESnd e -> TESnd (texpr_of_expr env bindings e)
    | ETaggedExpr (e1, e2) -> TETaggedExpr (texpr_of_expr env bindings e1, texpr_of_expr env bindings e2)

let rec compatible t1 t2 = match t1, t2 with
  | TUnknown, _ -> t2
  | _, TUnknown -> t1
  | TArrow(t3, t4), TArrow (t5, t6) -> TArrow (compatible t3 t5, compatible t4 t6)
  | _, _ when t1 = t2 -> t1
  | _, _ -> assert false

let rec checktype_of_tactic (env: tactic_type SMap.t) expected term : (tactic_type * parsed_tactic) =
  match expected with
  | TInt ->
    TInt, begin match term with
      | EVar ident when SMap.find_opt ident env = Some TInt -> PTacReplace ident
      | EConst i -> let i = try int_of_string i with Failure _ -> raise TacticTypeError in PTacInt i
      | _ -> raise TacticTypeError
    end
  | TIdent ->
    begin match term with
      | EVar ident when SMap.find_opt ident env = Some TIdent -> TIdent, PTacReplace ident
      | EVar ident when SMap.find_opt ident env = None -> TIdent, PTacVar ident
      | _ -> raise TacticTypeError
    end
  | TExpr ->
    begin match term with
      | EVar ident when SMap.find_opt ident env = Some TExpr -> TExpr, PTacReplace ident
      | EVar ident when SMap.find_opt ident env = Some TIdent -> TExpr, PTacExpr (TEReplace ident)
      | EVar ident when SMap.find_opt ident env = None -> TExpr, PTacExpr (TEVar ident)
      | EVar _ -> raise TacticTypeError
      | _ -> TExpr, PTacExpr (texpr_of_expr env SSet.empty term)
    end
  | TTac ->
    begin match term with
      | EVar ident when SMap.find_opt ident env = Some TTac -> (TTac, PTacReplace ident)
      | EApp (EApp (EConst op, pt1), pt2) when op = seq_op ->
        let t1, pt1 = checktype_of_tactic env TTac pt1 in
        let t2, pt2 = checktype_of_tactic env TTac pt2 in
        if TTac = t1 && TTac = t2
        then TTac, PTacSeq (pt1, pt2)
        else raise TacticTypeError
      | EApp (EApp (EConst op, pt1), pt2) when op = or_op ->
        let t1, pt1 = checktype_of_tactic env TTac pt1 in
        let t2, pt2 = checktype_of_tactic env TTac pt2 in
        if TTac = t1 && TTac = t2
        then TTac, PTacOr (pt1, pt2)
        else raise TacticTypeError
      | EApp (pt1, pt2) ->
        begin
          let (t1, pt1) = checktype_of_tactic env (TArrow (TUnknown, TTac)) pt1 in
          match t1 with
            | TArrow (t11, TTac) ->
              let (t2, pt2) = checktype_of_tactic env t11 pt2 in
              if t11 = t2
              then TTac, PTacApp (pt1, pt2)
              else raise TacticTypeError
            | _ -> assert false
        end
      | _ -> raise TacticTypeError
    end
  | TArrow (t1, t2) ->
    begin match term with
      | EVar ident ->
        begin match SMap.find_opt ident env with
          | Some (TArrow (t3, t4)) -> TArrow (compatible t1 t3, compatible t2 t4), PTacReplace ident
          | _ -> raise TacticTypeError
        end
      | EApp (pt1, pt2) ->
        begin match checktype_of_tactic env (TArrow (TUnknown, TArrow (t1, t2))) pt1 with
          | TArrow (t3, TArrow (t4, t5)), pt1 ->
            let (_, pt2) = checktype_of_tactic env t3 pt2 in
            TArrow (compatible t1 t4, compatible t2 t5), PTacApp (pt1, pt2)
          | _ -> raise TacticTypeError
        end
      | _ -> raise TacticTypeError
    end
  | TUnknown -> assert false

let rec tactic_type_of_expr = function
    | EVar "Tac" -> TTac
    | EVar "Int" -> TInt
    | EVar "Ident" -> TIdent
    | EVar "Expr" -> TExpr
    | EVar t -> print_endline ("\tUnknown type "^t^"\n\n\n"); raise TacticTypeError
    | EPi (("_", t1), t2) -> TArrow (tactic_type_of_expr t1, tactic_type_of_expr t2)
    | _ -> raise TacticTypeError

let rec checktype_of_tactic_builder (env: tactic_type SMap.t) = function
    | ELam ((id, tt), tb) ->
      let tt = tactic_type_of_expr tt in
      let (t, tb) = checktype_of_tactic_builder (SMap.add id tt env) tb
      in TArrow (tt, t), Arg (id, tt, tb)
    | tb ->
      let tt, tb = checktype_of_tactic env TTac tb in
      tt, Tactic tb

let defaultTacticsList = [
  "Intro", TArrow(TIdent, TTac), TIIntro;
  "Apply", TArrow(TExpr, TTac), TIApply;
  "SigmaRec",  TTac, TISigmaRec;
  "Exact", TArrow (TExpr, TTac), TIExact;
  "try", TArrow (TTac, TTac), TITry;
  "rpt", TArrow (TInt, TArrow (TTac, TTac)), TIDo;
  "Define", TArrow (TIdent, TArrow (TExpr, TArrow (TExpr, TTac))), TIDefine;
  "Unfold", TArrow (TIdent, TTac), TIUnfold;
  "Reduce", TTac, TIReduce;
]

let base_tactic_ctxt = List.fold_left (fun smap (id, tt, tname) -> SMap.add id (tt, Tactic (PTacBase tname), TacEnv SMap.empty) smap) SMap.empty defaultTacticsList

let tactic_creator env id tb =
  if SMap.mem id env
  then assert false
  else
    let (tt, tb) = checktype_of_tactic_builder (SMap.map (fun (x,_,_) -> x) env) tb in
    SMap.add id (tt, tb, TacEnv env) env

let rec get_int env: parsed_tactic -> int = function
  | PTacReplace id -> begin
    match SMap.find_opt id env with
      | Some (_, Tactic x, TacEnv env) -> get_int env x
      | _ -> assert false
    end
  | PTacInt i -> i
  | _ -> assert false

let rec get_ident env: parsed_tactic -> ident = function
    | PTacVar id -> id
    | PTacReplace id -> begin
      match SMap.find_opt id env with
        | Some (_, Tactic x, TacEnv env) -> get_ident env x
        | _ -> assert false
     end
   | _ -> assert false

let rec expr_of_tactic_expr env = function
  | TEConst id -> EConst id
  | TEVar id -> EVar id
  | TELam ((id, e1), e2) -> ELam ((id, expr_of_tactic_expr env e1), expr_of_tactic_expr env e2)
  | TEApp (e1, e2) -> EApp (expr_of_tactic_expr env e1, expr_of_tactic_expr env e2)
  | TEPi ((id, e1), e2) -> EPi ((id, expr_of_tactic_expr env e1), expr_of_tactic_expr env e2)
  | TESigma ((id, e1), e2) -> ESigma ((id, expr_of_tactic_expr env e1), expr_of_tactic_expr env e2)
  | TEFst e -> EFst (expr_of_tactic_expr env e)
  | TESnd e -> ESnd (expr_of_tactic_expr env e)
  | TEPair ((e1, e2), None) -> EPair ((expr_of_tactic_expr env e1, expr_of_tactic_expr env e2), None)
  | TEPair ((e1, e2), Some e3) -> EPair ((expr_of_tactic_expr env e1, expr_of_tactic_expr env e2), Some (expr_of_tactic_expr env e3))
  | TETaggedExpr (e1, e2) -> ETaggedExpr (expr_of_tactic_expr env e1, expr_of_tactic_expr env e2)
  | TEReplace id -> term_of_ptac env (PTacReplace id)
and term_of_ptac env = function
    | PTacExpr e -> expr_of_tactic_expr env e
    | PTacVar id -> EVar id
    | PTacReplace id ->
      begin match SMap.find_opt id env with
        | Some (_, Tactic t, TacEnv env) -> term_of_ptac env t
        | _ -> assert false
      end
    | _ -> assert false

let rec tac_of_tac_builder env args pt = match args, pt with
    | _, Tactic t -> (env, args, t)
    | (hd, envLocal)::tl, Arg (id, tt, tb) -> tac_of_tac_builder (SMap.add id (tt, Tactic hd, TacEnv envLocal) env) tl tb
    | _ -> assert false

let rec compute_tactic args (env: tactic_ctxt) parsed_tac = match args, parsed_tac with
    | _, PTacReplace id ->
      begin match SMap.find_opt id env with
        | Some (_, tb, TacEnv env) ->
          let env, args, tac = tac_of_tac_builder env args tb in
          compute_tactic args env tac
        | None -> assert false
      end
    | [], PTacSeq (pt1, pt2) ->
      SeqTac (compute_tactic [] env pt1, compute_tactic [] env pt2)
    | [], PTacOr (pt1, pt2) ->
      OrTac (compute_tactic [] env pt1, compute_tactic [] env pt2)
    | _, PTacApp (pt1, pt2) -> compute_tactic ((pt2, env)::args) env pt1
    | [x,env], PTacBase TIIntro -> BaseTac (IntroTac (get_ident env x))
    | [x,env], PTacBase TIApply -> BaseTac (ApplyTac (term_of_ptac env x))
    | [], PTacBase TISigmaRec -> BaseTac SigmaRecTac
    | [x,env], PTacBase TIExact -> BaseTac (ExactTac (term_of_ptac env x))
    | [x,env], PTacBase TITry -> TryTac (compute_tactic [] env x)
    | [x1,e1; x2,e2], PTacBase TIDo -> DoTac (get_int e1 x1, compute_tactic [] e2 x2)
    | [x1,e1; x2,e2; x3,e3], PTacBase TIDefine -> BaseTac (DefineTac (get_ident e1 x1, term_of_ptac e2 x2, term_of_ptac e3 x3))
    | [x,env], PTacBase TIUnfold -> BaseTac (UnfoldTac (get_ident env x))
    | [], PTacBase TIReduce -> BaseTac (ReduceTac)
    | _ -> assert false

let rec map_texpr (f: string -> string) : tactic_expr -> tactic_expr = function
    | TEVar id -> TEVar (f id)
    | TEApp (e1, e2) -> TEApp (map_texpr f e1, map_texpr f e2)
    | TEConst id -> TEConst id
    | TEFst e -> TEFst (map_texpr f e)
    | TESnd e -> TESnd (map_texpr f e)
    | TESigma ((id, e1), e2) -> TESigma ((id, map_texpr f e1), map_texpr f e2)
    | TEPi ((id, e1), e2) -> TEPi ((id, map_texpr f e1), map_texpr f e2)
    | TELam ((id, e1), e2) -> TELam ((id, map_texpr f e1), map_texpr f e2)
    | TEReplace id -> TEReplace (f id)
    | TEPair ((e1, e2), None) -> TEPair ((map_texpr f e1, map_texpr f e2), None)
    | TEPair ((e1, e2), Some e3) -> TEPair ((map_texpr f e1, map_texpr f e2), Some (map_texpr f e3))
    | TETaggedExpr (e1, e2) -> TETaggedExpr (map_texpr f e1, map_texpr f e2)

let rec map_ptac f = function
    | PTacApp (e1, e2) -> PTacApp (map_ptac f e1, map_ptac f e2)
    | PTacReplace id -> PTacReplace (f id)
    | PTacOr (e1, e2) -> PTacOr (map_ptac f e1, map_ptac f e2)
    | PTacSeq (e1, e2) -> PTacSeq (map_ptac f e1, map_ptac f e2)
    | PTacBase id -> PTacBase id
    | PTacExpr e -> PTacExpr (map_texpr f e)
    | PTacVar id -> PTacVar (f id)
    | PTacInt i -> PTacInt i

let rec map_ptacb f = function
    | Tactic t -> Tactic (map_ptac f t)
    | Arg (id, tt, tb) -> Arg (f id, tt, map_ptacb f tb)

let rec map_tac_ctxt f env =
    SMap.fold (fun k (tt, tb, TacEnv ctxt) -> SMap.add (f k) (tt, map_ptacb f tb, TacEnv (map_tac_ctxt f ctxt))) env SMap.empty

let tac_ctxt_merge : tactic_ctxt -> tactic_ctxt -> tactic_ctxt =
    SMap.merge (fun _ e1 e2 ->
      match e1, e2 with
        | None, None -> assert false
        | Some e1, Some e2 -> assert (e1 = e2); Some e1
        | Some e, None | None, Some e -> Some e)

let unraw_section tac_env (tl: knel_file) (rs: raw_knel_section) = match rs with
    | RawHypothesisSection ctxt ->
      HypothesisSection ctxt :: tl
    | RawDefinitionSection (i, e1, e2) ->
        DefinitionSection (i, e1, e2) :: tl
    | RawTacticDeclSection (id, tb) ->
      let () = tac_env := tactic_creator !tac_env id tb in tl
    | RawReasoningSection (bt, name_opt, stmt, proof, et) ->
      let tac_list = List.map (fun tac -> snd (checktype_of_tactic (SMap.map (fun (x, _, _) -> x) !tac_env) TTac tac)) proof in
      ReasoningSection (bt, name_opt, stmt, List.map (compute_tactic [] !tac_env) tac_list, et) :: tl

let unraw_file (tac_env: tactic_ctxt) (l: raw_knel_file) : (tactic_ctxt * Ast.knel_file) =
  let tac_env = ref tac_env in
  let l = List.fold_left (unraw_section tac_env) [] l in
  (!tac_env, List.rev l)
