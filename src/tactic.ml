open Ast

exception TacticTypeError
exception UndefinedTactic of ident

module SMap = Map.Make(String)

type tac_arg =
  | TATerm of term
  | TATac of parsed_tactic
  | TAIL of ident list
  | TAInt of int

and parsed_tactic =
  | BasePTac of ident * tac_arg list
  | SeqPTac of parsed_tactic * parsed_tactic
  | OrPTac of parsed_tactic * parsed_tactic


type tac_arg_inner =
  | ATerm of term
  | AInt of int
  | AIdent of ident
  | AIdentL of ident list
  | ATac of (tac_arg_inner list -> tactic)
  | AReplace of ident

type typed_tactic =
  | BaseTTac of ident * tac_arg_inner list
  | SeqTTac of typed_tactic * typed_tactic
  | OrTTac of typed_tactic * typed_tactic

type tactic_type =
  | TInt
  | TIdent
  | TIdentL
  | TTac
  | TTerm
  | TArrow of tactic_type * tactic_type

type tactic_env = (ident * tactic_type) list

let rpt_builder = function
  | [AInt i; ATac t] -> DoTac (i, t [])
  | _ -> assert false

let try_builder = function
  | [ATac t] -> TryTac (t [])
  | _ -> assert false

let intro_builder = function
  | [AIdent id] -> BaseTac (IntroTac id)
  | _ -> assert false

let apply_builder = function
  | [ATerm t] -> BaseTac (ApplyTac t)
  | _ -> assert false

let split_builder = function
  | [] -> BaseTac SplitTac
  | _ -> assert false

let prodrec_builder = function
  | [AIdentL il] -> BaseTac (ProdRecTac il)
  | _ -> assert false

let choose_builder = function
  | [AInt i] -> BaseTac (ChooseTac i)
  | _ -> assert false

let sumrec_builder = function
  | [] -> BaseTac SumRecTac
  | _ -> assert false

let exact_builder = function
  | [ATerm t] -> BaseTac (ExactTac t)
  | _ -> assert false


let base_tactic_ctxt =
  let l = [
    "rpt",      rpt_builder,      TArrow (TInt, TArrow (TTac, TTac));
    "try",      try_builder,      TArrow (TTac, TTac);
    "Intro",    intro_builder,    TArrow (TIdent, TTac);
    "Apply",    apply_builder,    TArrow (TTerm, TTac);
    "Split",    split_builder,    TTac;
    "ProdRec",  prodrec_builder,  TArrow (TIdentL, TTac);
    "Choose",   choose_builder,   TArrow (TInt, TTac);
    "SumRec",   sumrec_builder,   TTac;
    "Exact",    exact_builder,    TArrow(TTerm, TTac);
  ] in
  List.fold_left (fun map (ident, tac_builder, tac_type) -> SMap.add ident (tac_builder, tac_type) map) SMap.empty l

type tactic_ctxt = ((tac_arg_inner list -> tactic) * tactic_type) SMap.t

let parsed_tactic_of_term _ = failwith "parsed_tactic_of_term needs to be implemented"

let rec type_ctxt_builder smap = function
  | [] -> smap
  | (id, t)::tl -> type_ctxt_builder (SMap.add id t smap) tl

let rec type_arg_list arg_types ctxt given_tac arg_list = match given_tac, arg_list with
  | TArrow (TInt, t2),    TAInt i::tl -> AInt i :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TInt, t2),  TATerm (TVar ident)::tl
    when SMap.find_opt ident arg_types = Some TInt ->
    AReplace ident :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TIdent, t2),  TATerm (TVar ident)::tl
    when SMap.find_opt ident arg_types = Some TIdent ->
    AIdent ident :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TIdent, t2),  TATerm (TVar ident)::tl ->
    AIdent ident :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TIdentL, t2), TAIL l::tl -> AIdentL l :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TIdent, t2),  TATerm (TVar ident)::tl
    when SMap.find_opt ident arg_types = Some TIdentL ->
    AIdent ident :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TTac, t2),  TATerm (TVar ident)::tl
    when SMap.find_opt ident arg_types = Some TTac ->
    AIdent ident :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TTac, t2),    TATerm t::tl ->
    failwith "TODO tactic.ml line 120"
  | TArrow (TTac, t2),    TATac t::tl ->
    ATac (function | [] -> failwith "TODO tactic.ml line 122" | _ -> assert false) :: type_arg_list arg_types ctxt t2 tl
    | TArrow (TTac, t2),  TATerm (TVar ident)::tl
    when SMap.find_opt ident arg_types = Some TTerm ->
    AIdent ident :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TTerm, t2),   TATerm term::tl -> ATerm term :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TArrow _ as t1, t2),  TATerm (TVar ident)::tl
    when SMap.find_opt ident arg_types = Some t1 ->
    AIdent ident :: type_arg_list arg_types ctxt t2 tl
  | TArrow (TArrow _, _), _::_ -> failwith "TODO tactic reading tactic" 
  | TTac, [] -> []
  | _, _ -> raise TacticTypeError

let rec type_tac ctxt arg_types = function
  | OrPTac (t1, t2) -> OrTTac (type_tac ctxt arg_types t1, type_tac ctxt arg_types t2)
  | SeqPTac (t1, t2) -> SeqTTac (type_tac ctxt arg_types t1, type_tac ctxt arg_types t2)
  | BasePTac (ident, arg_list) ->
    let tactic_type =
      try SMap.find ident arg_types
      with Not_found ->
        try snd (SMap.find ident ctxt)
        with Not_found -> raise (UndefinedTactic ident) in
    let arg_list2 = type_arg_list arg_types ctxt tactic_type arg_list in
    BaseTTac (ident, arg_list2)

let tactic_creator : tactic_ctxt -> (ident * tactic_type) list -> parsed_tactic -> ((tac_arg_inner list -> tactic) * tactic_type) =
  fun ctxt argl ptac ->
    let ptac_typed = type_tac ctxt (type_ctxt_builder SMap.empty argl) ptac
    in
    let rec rewrite_tac smap = function
      | OrTTac (t1, t2) -> OrTac (rewrite_tac smap t1, rewrite_tac smap t2)
      | SeqTTac (t1, t2) -> SeqTac (rewrite_tac smap t1, rewrite_tac smap t2)
      | BaseTTac  (id, arg_list) ->
          begin 
            let tac_builder = try
              match SMap.find id smap with
                | ATac tb -> tb
                | _ -> assert false
              with Not_found ->
                try fst (SMap.find id ctxt)
                with Not_found -> assert false
            in
            let arg_list2 = List.map
              (function
                | AReplace id -> SMap.find id smap
                | arg -> arg)
              arg_list
          in tac_builder arg_list2
          end
    in 
    let rec tac_builder_builder smap type_l arg_l = match type_l, arg_l with
      | [], [] -> rewrite_tac smap ptac_typed
      | (ident, _)::type_tl, arg::arg_tl -> tac_builder_builder (SMap.add ident arg smap) type_tl arg_tl
      | _, _ -> assert false
    in
    let rec type_builder = function
      | [] -> TTac
      | (_, t)::tl -> TArrow (t, type_builder tl)
    in
    (tac_builder_builder SMap.empty argl, type_builder argl)

    

let rec compare_types : tactic_ctxt -> tactic_type -> tac_arg list -> tac_arg_inner list
  = fun ctxt tac_type tac_l -> match tac_type, tac_l with
    | TArrow (TInt, t2),    TAInt i::tl -> AInt i :: compare_types ctxt t2 tl
    | TArrow (TIdent, t2),  TATerm (TVar ident)::tl -> AIdent ident :: compare_types ctxt t2 tl
    | TArrow (TIdentL, t2), TAIL l::tl -> AIdentL l :: compare_types ctxt t2 tl
    | TArrow (TTac, t2),    TATerm t::tl ->
      ATac (function | [] -> compute_tactic ctxt (parsed_tactic_of_term t) | _ -> assert false) :: compare_types ctxt t2 tl
    | TArrow (TTac, t2),    TATac t::tl ->
      ATac (function | [] -> compute_tactic ctxt t | _ -> assert false) :: compare_types ctxt t2 tl
    | TArrow (TTerm, t2),   TATerm term::tl -> ATerm term :: compare_types ctxt t2 tl
    | TArrow (TArrow _, _), _::_ -> failwith "TODO tactic reading tactic" 
    | TTac, [] -> []
    | _, _ -> raise TacticTypeError

and compute_tactic (ctxt : tactic_ctxt) : parsed_tactic -> tactic = function
  | BasePTac (ident, ta_list) ->
    let (builder, tactic_type) = 
      try
        SMap.find ident ctxt
      with Not_found -> raise (UndefinedTactic ident) in
    let argl = compare_types ctxt tactic_type ta_list in
    builder argl
  | SeqPTac (t1, t2) ->
    SeqTac (compute_tactic ctxt t1, compute_tactic ctxt t2)
  | OrPTac (t1, t2) ->
    OrTac (compute_tactic ctxt t1, compute_tactic ctxt t2)

