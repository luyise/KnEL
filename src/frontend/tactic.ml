open Ast

exception TacticTypeError
exception UndefinedTactic of ident

module SMap = Map.Make(String)

let pp_ident fmt id = Format.fprintf fmt "%s" id

type tactic_ident =
  | TIIntro
  | TIApply
  | TISplit
  | TISigmaRec
  | TIExact
  | TITry
  | TIDo
  | TIDefine

type parsed_tactic =
  | PTacVar of ident
  | PTacInt of int
  | PTacExpr of expr
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
        parsed_tactic list *
      ending_tag)
  | RawTacticDeclSection of ident * tactic_builder

type raw_knel_file = raw_knel_section list

type tactic_env =
  | TacEnv of (tactic_type * tactic_builder * tactic_env) SMap.t

type tactic_ctxt = (tactic_type * tactic_builder * tactic_env) SMap.t


let compatible t1 t2 = match t1, t2 with
  | TUnknown, _ -> t2
  | _, TUnknown -> t1
  | _, _ when t1 = t2 -> t1
  | _, _ -> assert false 

let rec checktype_of_tactic (env: tactic_type SMap.t) expected parsed_tac : tactic_type =
  match expected with
  | TInt ->
    begin match parsed_tac with
      | PTacVar ident when SMap.find_opt ident env = Some TInt -> TInt
      | PTacInt _ -> TInt
      | PTacApp (pt1, pt2) ->
        begin
          let t1 = checktype_of_tactic env (TArrow (TUnknown, TInt)) pt1 in
          match t1 with
            | TArrow (t11, TInt) -> if t11 = checktype_of_tactic env t11 pt2 then TInt else assert false
            | _ -> assert false
        end
      | _ -> assert false
    end
  | TIdent ->
    begin match parsed_tac with
      | PTacVar ident when SMap.find_opt ident env = Some TIdent || SMap.find_opt ident env = None -> TIdent
      | PTacApp (pt1, pt2) ->
        begin
          let t1 = checktype_of_tactic env (TArrow (TUnknown, TIdent)) pt1 in
          match t1 with
            | TArrow (t11, TIdent) -> if t11 = checktype_of_tactic env t11 pt2 then TIdent else assert false
            | _ -> assert false
        end
      | _ -> assert false
    end
  | TExpr ->
    begin match parsed_tac with
      | PTacVar ident when SMap.find_opt ident env = Some TExpr -> TExpr
      | PTacExpr _ -> TExpr
      | PTacApp (pt1, pt2) ->
        begin
          let t1 = checktype_of_tactic env (TArrow (TUnknown, TExpr)) pt1 in
          match t1 with
            | TArrow (t11, TExpr) -> if t11 = checktype_of_tactic env t11 pt2 then TExpr else assert false
            | _ -> assert false
        end
      | _ -> assert false
    end
  | TTac ->
    begin match parsed_tac with
      | PTacVar ident when SMap.find_opt ident env = Some TTac -> TTac
      | PTacSeq (pt1, pt2) | PTacOr (pt1, pt2) ->
        if TTac = checktype_of_tactic env TTac pt1 && TTac = checktype_of_tactic env TTac pt2
        then TTac
        else assert false
      | PTacApp (pt1, pt2) ->
        begin
          let t1 = checktype_of_tactic env (TArrow (TUnknown, TTac)) pt1 in
          match t1 with
            | TArrow (t11, TTac) -> if t11 = checktype_of_tactic env t11 pt2 then TTac else assert false
            | _ -> assert false
        end
      | _ -> assert false
    end
  | TArrow (t1, t2) ->
    begin match parsed_tac with
      | PTacVar ident ->
        begin match SMap.find_opt ident env with
          | Some (TArrow (t3, t4)) -> TArrow (compatible t1 t3, compatible t2 t4)
          | _ -> print_endline ident; assert false
        end
      | PTacApp (pt1, pt2) ->
        begin match checktype_of_tactic env (TArrow (TUnknown, TArrow (t1, t2))) pt1 with
          | TArrow (t3, TArrow (t4, t5)) ->
            let _ = compatible t1 t4 in
            let _ = compatible t2 t5 in
            checktype_of_tactic env t3 pt2
          | _ -> assert false
        end
      | _ -> assert false
    end
  | TUnknown -> assert false

let rec checktype_of_tactic_builder (env: tactic_type SMap.t) = function
    | Tactic pt ->
      let t = checktype_of_tactic env TTac pt in
      if t <> TTac then assert false
      else t
    | Arg (id, tt, tb) ->
      TArrow (tt, checktype_of_tactic_builder (SMap.add id tt env) tb)

let defaultTacticsList = [
  "Intro", TArrow(TIdent, TTac), Arg ("v", TIdent, Tactic (PTacApp (PTacBase TIIntro, PTacVar "v")));
  "Apply", TArrow(TExpr, TTac), Arg ("t", TExpr, Tactic (PTacApp (PTacBase TIApply, PTacVar "t")));
  "Split", TArrow(TExpr, TTac), Arg ("t", TExpr, Tactic (PTacApp (PTacBase TISplit, PTacVar "t")));
  "SigmaRec",  TTac, Tactic (PTacBase TISigmaRec);
  "Exact", TArrow (TExpr, TTac), Arg ("t", TExpr, Tactic (PTacApp (PTacBase TIExact, PTacVar "t")));
  "try", TArrow (TTac, TTac), Arg ("t", TExpr, Tactic (PTacApp (PTacBase TITry, PTacVar "t")));
  "rpt", TArrow (TInt, TArrow (TTac, TTac)), Arg ("i", TInt, Arg ("t", TExpr, Tactic (PTacApp (PTacApp (PTacBase TIDo, PTacVar "i"), PTacVar "t"))));
  "Define", TArrow (TIdent, TArrow (TExpr, TArrow (TExpr, TTac))), Arg ("i", TIdent, Arg("term" , TExpr, Arg ("typ", TExpr, Tactic (PTacApp (PTacApp (PTacApp (PTacBase TIDefine, PTacVar "i"), PTacVar "term"), PTacVar "typ")))))
]

let base_tactic_ctxt = List.fold_left (fun smap (id, tt, tb) -> SMap.add id (tt, tb, TacEnv SMap.empty) smap) SMap.empty defaultTacticsList

let tactic_creator env id tb =
  if SMap.mem id env
  then assert false
  else
    let tt = checktype_of_tactic_builder (SMap.map (fun (x,_,_) -> x) env) tb in
    SMap.add id (tt, tb, TacEnv env) env

let rec get_int env: parsed_tactic -> int = function
  | PTacVar id -> begin
    match SMap.find_opt id env with
      | Some (_, Tactic x, TacEnv env) -> get_int env x
      | _ -> assert false
    end
  | PTacInt i -> i
  | _ -> assert false

let rec get_ident env: parsed_tactic -> ident = function
  | PTacVar id -> begin
    match SMap.find_opt id env with
      | Some (_, Tactic x, TacEnv env) -> get_ident env x
      | None -> id
      | _ -> assert false
    end
  | _ -> assert false

let rec term_of_ptac env = function
    | PTacExpr e -> e
    | PTacVar id ->
      begin match SMap.find_opt id env with
        | Some (_, Tactic t, TacEnv env) -> term_of_ptac env t
        | None -> EVar id
        | _ -> assert false
      end
    | PTacApp (pt1, pt2) -> EApp (term_of_ptac env pt1, term_of_ptac env pt2)
    | _ -> assert false

let rec tac_of_tac_builder env1 env2 args pt = match args, pt with
    | _, Tactic t -> (env2, args, t)
    | hd::tl, Arg (id, tt, tb) -> tac_of_tac_builder env1 (SMap.add id (tt, Tactic hd, TacEnv env1) env2) tl tb
    | _ -> assert false

let rec compute_tactic args (env: tactic_ctxt) parsed_tac = match args, parsed_tac with
    | _, PTacVar id ->
      begin match SMap.find_opt id env with
        | Some (_, tb, TacEnv env2) ->
          let env, args, tac = tac_of_tac_builder env env2 args tb in
          compute_tactic args env tac
        | None -> assert false
      end
    | [], PTacSeq (pt1, pt2) ->
      SeqTac (compute_tactic [] env pt1, compute_tactic [] env pt2)
    | [], PTacOr (pt1, pt2) ->
      OrTac (compute_tactic [] env pt1, compute_tactic [] env pt2)
    | _, PTacApp (pt1, pt2) -> compute_tactic (pt2::args) env pt1
    | [x], PTacBase TIIntro -> BaseTac (IntroTac (get_ident env x))
    | [x], PTacBase TIApply -> BaseTac (ApplyTac (term_of_ptac env x))
    | [x], PTacBase TISplit -> BaseTac (SplitTac (term_of_ptac env x))
    | [], PTacBase TISigmaRec -> BaseTac SigmaRecTac
    | [x], PTacBase TIExact -> BaseTac (ExactTac (term_of_ptac env x))
    | [x], PTacBase TITry -> TryTac (compute_tactic [] env x)
    | [x1; x2], PTacBase TIDo -> DoTac (get_int env x1, compute_tactic [] env x2)
    | [x1; x2; x3], PTacBase TIDefine -> BaseTac (DefineTac (get_ident env x1, term_of_ptac env x2, term_of_ptac env x3))
    | _ -> assert false


let unraw_section tac_env (tl: knel_file) (rs: raw_knel_section) = match rs with
    | RawHypothesisSection ctxt ->
      HypothesisSection ctxt :: tl
    | RawTacticDeclSection (id, tb) ->
      let () = tac_env := tactic_creator !tac_env id tb in tl
    | RawReasoningSection (bt, name_opt, stmt, proof, et) ->
      let _ = List.map (checktype_of_tactic (SMap.map (fun (x, _, _) -> x) !tac_env) TTac) proof in
      ReasoningSection (bt, name_opt, stmt, List.map (compute_tactic [] !tac_env) proof, et) :: tl

let unraw_file (tac_env: tactic_ctxt) (l: raw_knel_file) : (tactic_ctxt * Ast.knel_file) =
  let tac_env = ref tac_env in
  let l = List.fold_left (unraw_section tac_env) [] l in
  (!tac_env, List.rev l)
