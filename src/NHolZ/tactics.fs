[<AutoOpen>]
module NHolZ.tactics

open FSharp.Compatibility.OCaml
open FSharp.Compatibility.OCaml.Format

let null_inst = ([],[],[] :instantiation)

let null_meta = (([]:term list),null_inst)

(* ------------------------------------------------------------------------- *)
(* A goal has labelled assumptions, and the hyps are now thms.               *)
(* ------------------------------------------------------------------------- *)

type goal = (string * thm) list * term

let equals_goal ((a,w):goal) ((a',w'):goal) =
    forall2 (fun (s,th) (s',th') -> s = s' && thm_eq th th') a a' && w = w'

(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)

type justification = instantiation -> thm list -> thm

/// Prints a justification signature to formatter.
let pp_print_justification fmt (_ : justification) =
    pp_print_string fmt "instantiation -> thm list -> thm = <fun>" 

/// Prints a justification signature to the standard output.
let print_justification = pp_print_justification std_formatter

/// Converts a justification signature to a string representation.
let string_of_justification = print_to_string pp_print_justification

(* ------------------------------------------------------------------------- *)
(* The goalstate stores the subgoals, justification, current instantiation,  *)
(* and a list of metavariables.                                              *)
(* ------------------------------------------------------------------------- *)

type goalstate = (term list * instantiation) * goal list * justification

(* ------------------------------------------------------------------------- *)
(* A goalstack is just a list of goalstates. Could go for more...            *)
(* ------------------------------------------------------------------------- *)

type goalstack = goalstate list

(* ------------------------------------------------------------------------- *)
(* A refinement, applied to a goalstate [A1 ?- g1; ...; An ?- gn]            *)
(* yields a new goalstate with updated justification function, to            *)
(* give a possibly-more-instantiated version of the initial goal.            *)
(* ------------------------------------------------------------------------- *)

type refinement = goalstate -> goalstate

/// Prints a refinement signature to formatter.
let pp_print_refinement fmt (_ : refinement) =
    pp_print_string fmt "goalstate -> goalstate = <fun>"

/// Prints a refinement signature to the standard output.
let print_refinement = pp_print_refinement std_formatter

/// Converts a refinement signature to a string representation.
let string_of_refinement = print_to_string pp_print_refinement

(* ------------------------------------------------------------------------- *)
(* A tactic, applied to a goal A ?- g, returns:                              *)
(*                                                                           *)
(*  o A list of new metavariables introduced                                 *)
(*  o An instantiation (%)                                                   *)
(*  o A list of subgoals                                                     *)
(*  o A justification f such that for any instantiation @ we have            *)
(*    f(@) [A1@  |- g1@; ...; An@ |- gn@] = A(%;@) |- g(%;@)                 *)
(* ------------------------------------------------------------------------- *)

type tactic = goal -> goalstate

/// Prints a tactic signature to formatter.
let pp_print_tactic fmt (_ : tactic) =
    pp_print_string fmt "goal -> goalstate = <fun>"

/// Prints a tactic signature to the standard output.
let print_tactic = pp_print_tactic std_formatter

/// Converts a tactic signature to a string representation.
let string_of_tactic = print_to_string pp_print_tactic

type thm_tactic = thm -> tactic

/// Prints a thm_tactic signature to formatter.
let pp_print_thm_tactic fmt (_ : tactic) =
    pp_print_string fmt "thm -> tactic = <fun>"

/// Prints a thm_tactic signature to the standard output.
let print_thm_tactic = pp_print_thm_tactic std_formatter

/// Converts a thm_tactic signature to a string representation.
let string_of_thm_tactic = print_to_string pp_print_thm_tactic

type thm_tactical = thm_tactic -> thm_tactic

/// Prints a thm_tactical signature to formatter.
let pp_print_thm_tactical fmt (_ : thm_tactical) =
    pp_print_string fmt "thm_tactic -> thm_tactic = <fun>"

/// Prints a thm_tactical signature to the standard output.
let print_thm_tactical = pp_print_thm_tactical std_formatter

/// Converts a thm_tactical signature to a string representation.
let string_of_thm_tactical = print_to_string pp_print_thm_tactical

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

let (inst_goal:instantiation->goal->goal) =
  fun p (thms,w) ->
    map (id ||>> INSTANTIATE_ALL p) thms,instantiate p w

(* ------------------------------------------------------------------------- *)
(* Perform a sequential composition (left first) of instantiations.          *)
(* ------------------------------------------------------------------------- *)

let (compose_insts :instantiation->instantiation->instantiation) =
  fun (pats1,tmin1,tyin1) ((pats2,tmin2,tyin2) as i2) ->
    let tmin = map (instantiate i2 ||>> tyvar_inst tyin2) tmin1
    let tyin = map (type_inst tyin2 ||>> id) tyin1 in
    let tmin' = filter (fun (_,x) -> not (can (rev_assoc x) tmin)) tmin2
    let tyin' = filter (fun (_,a) -> not (can (rev_assoc a) tyin)) tyin2 in
    pats1@pats2,tmin@tmin',tyin@tyin'

(* ------------------------------------------------------------------------- *)
(* Construct A,_FALSITY_ |- p; contortion so falsity is the last element.    *)
(* ------------------------------------------------------------------------- *)

let _FALSITY_ = prim_new_const_definition ("_FALSITY_", parse_term(@"false")) //new_definition(parse_term @"_FALSITY_ = F")

let mk_fthm =
    let pth = undisch_rule(eq_imp_rule1 _FALSITY_)
    let qth = assume_rule (parse_term @"_FALSITY_") in
    fun (asl,c) -> prove_asm_rule qth (List.foldBack add_asm_rule (rev asl) (contr_rule c pth))

(* ------------------------------------------------------------------------- *)
(* Validity checking of tactics. This cannot be 100% accurate without making *)
(* arbitrary theorems, but "mk_fthm" brings us quite close.                  *)
(* ------------------------------------------------------------------------- *)

let (VALID:tactic->tactic) =
  let fake_thm (asl,w) =
    let asms = List.foldBack (union << asms << snd) asl [] in
    mk_fthm(asms,w)
  let false_tm = (parse_term @"_FALSITY_") in
  fun tac (asl,w) ->
    let ((mvs,i),gls,just as res) = tac (asl,w) in
    let ths = map fake_thm gls in
    let asl',w' = dest_thm(just null_inst ths) in
    let asl'',w'' = inst_goal i (asl,w) in
    let maxasms =
      List.foldBack (fun (_,th) -> union (insert (concl th) (asms th))) asl'' [] in
    if alpha_eq w' w'' &&
       forall (fun t -> exists (alpha_eq t) maxasms) (subtract asl' [false_tm])
    then res else failwith "VALID: Invalid tactic"

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

let (THEN),(THENL) =
    let propagate_empty i [] = []
    let propagate_thm th i [] = INSTANTIATE_ALL i th in
    let compose_justs n just1 just2 i ths =
        let ths1,ths2 = cut n ths in
        (just1 i ths1)::(just2 i ths2) in
    let rec seqapply l1 l2 = 
        match (l1,l2) with
        | ([],[]) -> null_meta,[],propagate_empty
        | ((tac:tactic)::tacs),((goal:goal)::goals) ->
                 let ((mvs1,insts1),gls1,just1) = tac goal in
                 let goals' = map (inst_goal insts1) goals in
                 let ((mvs2,insts2),gls2,just2) = seqapply tacs goals' in
                 ((union mvs1 mvs2,compose_insts insts1 insts2),
                  gls1@gls2,compose_justs (length gls1) just1 just2)
        | _,_ -> failwith "seqapply: Length mismatch" in
    let justsequence just1 just2 insts2 i ths =
        just1 (compose_insts insts2 i) (just2 i ths) in
    let tacsequence ((mvs1,insts1),gls1,just1) tacl =
        let ((mvs2,insts2),gls2,just2) = seqapply tacl gls1 in
        let jst = justsequence just1 just2 insts2 in
        let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
        ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
    let (then_: tactic -> tactic -> tactic) =
        fun tac1 tac2 g ->
            let _,gls,_ as gstate = tac1 g in
            tacsequence gstate (List.replicate (length gls) tac2)
    let (thenl_: tactic -> tactic list -> tactic) =
        fun tac1 tac2l g ->
            let _,gls,_ as gstate = tac1 g in
            if gls = [] then tacsequence gstate []
            else tacsequence gstate tac2l in
    then_,thenl_

let ((ORELSE): tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
        try tac1 g with Failure _ -> tac2 g

let (FAIL_TAC: string -> tactic) =
    fun tok g -> failwith tok

let (NO_TAC: tactic) =
    FAIL_TAC "NO_TAC"

let (ALL_TAC:tactic) =
    fun g -> null_meta,[g],fun _ [th] -> th

let TRY tac =
    tac |> ORELSE <| ALL_TAC

let rec REPEAT tac g =
    ((tac |> THEN <| REPEAT tac) |> ORELSE <| ALL_TAC) g

/// Sequentially applies all the tactics in a given list of tactics.
let EVERY tacl =
    List.foldBack THEN tacl ALL_TAC

/// Applies the first tactic in a tactic list that succeeds.
let FIRST : tactic list -> tactic =
    fun tacl g -> List.reduceBack ORELSE tacl g

/// Sequentially applies all tactics given by mapping a function over a list.
let MAP_EVERY (tacf : 'T -> tactic) (lst : 'T list) : tactic = 
    EVERY(map tacf lst)

/// Applies first tactic that succeeds in a list given by mapping a function over a list.
let MAP_FIRST tacf lst = FIRST(map tacf lst)

let (CHANGED_TAC: tactic -> tactic) =
    fun tac g ->
        let (meta,gl,_ as gstate) = tac g in
        if meta = null_meta && length gl = 1 && equals_goal (hd gl) g
        then failwith "CHANGED_TAC" else gstate

let rec REPLICATE_TAC n tac =
    if n <= 0 then ALL_TAC else tac |> THEN <| (REPLICATE_TAC (n - 1) tac)

(* ------------------------------------------------------------------------- *)
(* Combinators for theorem continuations / "theorem tacticals".              *)
(* ------------------------------------------------------------------------- *)

/// Composes two theorem-tacticals.
let (THEN_TCL : thm_tactical -> thm_tactical -> thm_tactical) = 
    fun ttcl1 ttcl2 ttac -> ttcl1(ttcl2 ttac)

let ((ORELSE_TCL): thm_tactical -> thm_tactical -> thm_tactical) =
    fun ttcl1 ttcl2 ttac th ->
        try ttcl1 ttac th with Failure _ -> ttcl2 ttac th

/// Repeatedly applies a theorem-tactical until it fails when applied to the theorem.
let rec REPEAT_TCL ttcl ttac th =
    ((ttcl |> THEN_TCL <| (REPEAT_TCL ttcl)) |> ORELSE_TCL <| id) ttac th

let (REPEAT_GTCL: thm_tactical -> thm_tactical) =
    let rec REPEAT_GTCL ttcl ttac th g =
        try ttcl (REPEAT_GTCL ttcl ttac) th g with Failure _ -> ttac th g in
    REPEAT_GTCL

/// Passes a theorem unchanged to a theorem-tactic.
let (ALL_THEN : thm_tactical) = id

let (NO_THEN: thm_tactical) =
    fun ttac th -> failwith "NO_THEN";

/// Composes a list of theorem-tacticals.
let EVERY_TCL ttcll =
    List.foldBack THEN_TCL ttcll ALL_THEN

/// Applies the first theorem-tactical in a list that succeeds.
let FIRST_TCL ttcll =
    List.reduceBack ORELSE_TCL ttcll

(* ------------------------------------------------------------------------- *)
(* Tactics to augment assumption list. Note that to allow "ASSUME p" for     *)
(* any assumption "p", these add a PROVE_HYP in the justification function,  *)
(* just in case.                                                             *)
(* ------------------------------------------------------------------------- *)

let (LABEL_TAC: string -> thm_tactic) =
    fun s thm (asl,w) ->
        null_meta,[(s,thm)::asl,w],
        fun i [th] -> prove_asm_rule (INSTANTIATE_ALL i thm) th;;

let ASSUME_TAC = LABEL_TAC ""

(* ------------------------------------------------------------------------- *)
(* Manipulation of assumption list.                                          *)
(* ------------------------------------------------------------------------- *)

let (FIND_ASSUM: thm_tactic -> term -> tactic) =
    fun ttac t ((asl,w) as g) ->
        ttac(snd(find (fun (_,th) -> concl th = t) asl)) g

let (POP_ASSUM: thm_tactic -> tactic) =
    fun ttac ->
        function gl -> match gl with
                        | (((_,th)::asl),w)  -> ttac th (asl,w)
                        | _ -> failwith "POP_ASSUM: No assumption to pop"

let (ASSUM_LIST: (thm list -> tactic) -> tactic) =
    fun aslfun (asl,w) -> aslfun (map snd asl) (asl,w)

let (POP_ASSUM_LIST: (thm list -> tactic) -> tactic) =
    fun asltac (asl,w) -> asltac (map snd asl) ([],w)

let (EVERY_ASSUM: thm_tactic -> tactic) =
    fun ttac -> ASSUM_LIST (MAP_EVERY ttac)

let (FIRST_ASSUM: thm_tactic -> tactic) =
    fun ttac (asl,w as g) -> tryfind (fun (_,th) -> ttac th g) asl

/// Maps an inference rule over the assumptions of a goal.
let (RULE_ASSUM_TAC : (thm -> thm) -> tactic) = 
    fun rule (asl,w) ->
        (POP_ASSUM_LIST(arg1_fn ALL_TAC) 
         |> THEN <| MAP_EVERY (fun (s,th) -> LABEL_TAC s (rule th)) (rev asl)) (asl, w)

(* ------------------------------------------------------------------------- *)
(* Operate on assumption identified by a label.                              *)
(* ------------------------------------------------------------------------- *)

let (USE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,w as gl) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    ttac th gl

let (REMOVE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,w) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption " + s) in
    let asl1,asl2 = cut (index s (map fst asl)) asl in
    let asl' = asl1 @ tl asl2 in
    ttac th (asl',w)

(* ------------------------------------------------------------------------- *)
(* General tool to augment a required set of theorems with assumptions.      *)
(* ------------------------------------------------------------------------- *)

let (ASM :(thm list -> tactic)->(thm list -> tactic)) =
  fun tltac ths (asl,w as g) -> tltac (map snd asl @ ths) g

  (* ------------------------------------------------------------------------- *)
(* Basic tactic to use a theorem equal to the goal. Does *no* matching.      *)
(* ------------------------------------------------------------------------- *)

let (ACCEPT_TAC: thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  fun th (asl,w) ->
    if alpha_eq (concl th) w then
      null_meta,[],propagate_thm th
    else failwith "ACCEPT_TAC"

(* ------------------------------------------------------------------------- *)
(* Create tactic from a conversion. This allows the conversion to return     *)
(* |- p rather than |- p = T on a term "p". It also eliminates any goals of  *)
(* the form "T" automatically.                                               *)
(* ------------------------------------------------------------------------- *)

let (CONV_TAC: conv -> tactic) =
  let t_tm = parse_term @"T" in
  fun conv ((asl,w) as g) ->
    let th = conv w in
    let tm = concl th in
    if alpha_eq tm w then ACCEPT_TAC th g else
    let l,r = dest_eq tm in
    if not(alpha_eq l w) then failwith "CONV_TAC: bad equation" else
    if r = t_tm then ACCEPT_TAC(eqt_elim_rule th) g else
    let th' = SYM th in
    null_meta,[asl,r],fun i [th] -> prim_eq_mp_rule (INSTANTIATE_ALL i th') th

(* ------------------------------------------------------------------------- *)
(* Tactics for equality reasoning.                                           *)
(* ------------------------------------------------------------------------- *)

let (REFL_TAC: tactic) =
  fun ((asl,w) as g) ->
    try ACCEPT_TAC(prim_refl_conv(rand w)) g
    with Failure _ -> failwith "REFL_TAC"

let (ABS_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_eq w in
        let lv,lb = dest_abs l
        let rv,rb = dest_abs r in
        let avoids = List.foldBack (union << thm_free_vars << snd) asl (free_vars w) in
        let v = mk_primed_var avoids lv in
        null_meta,[asl,mk_eq(vsubst[v,lv] lb,vsubst[v,rv] rb)],
        fun i [th] -> let ath = prim_mk_abs_rule v th in
                      prim_eq_mp_rule (ALPHA (concl ath) (instantiate i w)) ath
    with Failure _ -> failwith "ABS_TAC"

let (MK_COMB_TAC: tactic) =
  fun (asl,gl) ->
    try let l,r = dest_eq gl in
        let f,x = dest_comb l
        let g,y = dest_comb r in
        null_meta,[asl,mk_eq(f,g); asl,mk_eq(x,y)],
        fun _ [th1;th2] -> prim_mk_comb_rule th1 th2
    with Failure _ -> failwith "MK_COMB_TAC"

let (AP_TERM_TAC: tactic) =
  let tac = MK_COMB_TAC |> THENL <| [REFL_TAC; ALL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_TERM_TAC"

let (AP_THM_TAC: tactic) =
  let tac = MK_COMB_TAC |> THENL <| [ALL_TAC; REFL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_THM_TAC"

let (BINOP_TAC: tactic) =
  let tac = MK_COMB_TAC |> THENL <| [AP_TERM_TAC; ALL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_THM_TAC"

let (SUBST1_TAC: thm_tactic) =
  fun th -> CONV_TAC(SUBS_CONV [th])

let SUBST_ALL_TAC rth =
  SUBST1_TAC rth |> THEN <| RULE_ASSUM_TAC (SUBS [rth])

let BETA_TAC = CONV_TAC(REDEPTH_CONV BETA_CONV)

(* ------------------------------------------------------------------------- *)
(* Just use an equation to substitute if possible and uninstantiable.        *)
(* ------------------------------------------------------------------------- *)

let SUBST_VAR_TAC th =
  try let asm,eq = dest_thm th in
      let l,r = dest_eq eq in
      if alpha_eq l r then ALL_TAC
      else if not (subset (free_vars eq) (list_free_vars asm)) then failwith "SUBST_VAR_TAC"
      else if (is_const l || is_var l) && not(term_free_in l r)
           then SUBST_ALL_TAC th
      else if (is_const r || is_var r) && not(term_free_in r l)
           then SUBST_ALL_TAC(SYM th)
      else failwith "SUBST_VAR_TAC"
  with Failure _ -> failwith "SUBST_VAR_TAC"

(* ------------------------------------------------------------------------- *)
(* Basic logical tactics.                                                    *)
(* ------------------------------------------------------------------------- *)

let (DISCH_TAC: tactic) =
  let f_tm = false_tm in
  fun (asl,w) ->
    try let ant,c = dest_imp w in
        let th1 = assume_rule ant in
        null_meta,[("",th1)::asl,c],
        fun i [th] -> prim_disch_rule (instantiate i ant) th
    with Failure _ -> 
        try
            let ant = dest_not w in
            let th1 = assume_rule ant in
            null_meta,[("",th1)::asl,f_tm],
            fun i [th] -> not_intro_rule(prim_disch_rule (instantiate i ant) th)
        with Failure _ -> failwith "DISCH_TAC"

let (MP_TAC: thm_tactic) =
  fun thm (asl,w) ->
    null_meta,[asl,mk_imp(concl thm,w)],
    fun i [th] -> prim_mp_rule th (INSTANTIATE_ALL i thm)

let (EQ_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_eq w in
        null_meta,[asl, mk_imp(l,r); asl, mk_imp(r,l)],
        fun _ [th1; th2] -> imp_antisym_rule th1 th2
    with Failure _ -> failwith "EQ_TAC"

let (UNDISCH_TAC: term -> tactic) =
 fun tm (asl,w) ->
   try let sthm,asl' = remove1 (fun (_,asm) -> alpha_eq (concl asm) tm) asl in
       let thm = snd sthm in
       null_meta,[asl',mk_imp(tm,w)],
       fun i [th] -> prim_mp_rule th (INSTANTIATE_ALL i thm)
   with Failure _ -> failwith "UNDISCH_TAC"

let (SPEC_TAC: term * term -> tactic) =
  fun (t,x) (asl,w) ->
    try null_meta,[asl, mk_forall(x,subst[x,t] w)],
        fun i [th] -> spec_rule (instantiate i t) th
    with Failure _ -> failwith "SPEC_TAC"

let (X_GEN_TAC: term -> tactic) =
  fun x' ->
    if not(is_var x') then failwith "X_GEN_TAC" else
    fun (asl,w) ->
      try let x,bod = dest_forall w in
          let avoids = List.foldBack (union << thm_free_vars << snd) asl (free_vars w) in
          if mem x' avoids then failwith "X_GEN_TAC" else
          let afn = CONV_RULE(GEN_ALPHA_CONV x) in
          null_meta,[asl,vsubst[x',x] bod],
          fun i [th] -> afn (gen_rule x' th)
      with Failure _ -> failwith "X_GEN_TAC"

let (GEN_TAC: tactic) =
  fun (asl,w) ->
    try let x = fst(dest_forall w) in
        let avoids = List.foldBack (union << thm_free_vars << snd) asl (free_vars w) in
        let x' = mk_primed_var avoids x in
        X_GEN_TAC x' (asl,w)
    with Failure _ -> failwith "GEN_TAC"

let (EXISTS_TAC: term -> tactic) =
  fun t (asl,w) ->
    try let v,bod = dest_exists w in
        null_meta,[asl,vsubst[t,v] bod],
        fun i [th] -> exists_rule (instantiate i w,instantiate i t) th
    with Failure _ -> failwith "EXISTS_TAC"

let (X_CHOOSE_TAC: term -> thm_tactic) =
  fun x' xth ->
    try let xtm = concl xth in
        let x,bod = dest_exists xtm in
        let pat = vsubst[x',x] bod in
        let xth' = assume_rule pat in
        fun (asl,w) ->
          let avoids = List.foldBack (union << free_vars << concl << snd) asl
                              (union (free_vars w) (thm_free_vars xth)) in
          if mem x' avoids then failwith "X_CHOOSE_TAC" else
          null_meta,[("",xth')::asl,w],
          fun i [th] -> choose_rule(x',INSTANTIATE_ALL i xth) th
    with Failure _ -> failwith "X_CHOOSE_TAC"

let (CHOOSE_TAC: thm_tactic) =
  fun xth ->
    try let x = fst(dest_exists(concl xth)) in
        fun (asl,w) ->
          let avoids = List.foldBack (union << thm_free_vars << snd) asl
                              (union (free_vars w) (thm_free_vars xth)) in
          let x' = mk_primed_var avoids x in
          X_CHOOSE_TAC x' xth (asl,w)
      with Failure _ -> failwith "CHOOSE_TAC"

let (CONJ_TAC:tactic)  = 
    fun (asl,w) -> 
        let (l,r) = dest_conj w
        let just_fn:justification = fun null_inst [th1;th2] -> conj_rule th1 th2
        let g1:goal = (asl,l)
        let g2:goal = (asl,r)
        let (glist:goal list) = [g1; g2]
        (([],null_inst),[(asl,l);(asl,r)], just_fn)

let (DISJ1_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_disj w in
        null_meta,[asl,l],fun i [th] -> disj1_rule th (instantiate i r)
    with Failure _ -> failwith "DISJ1_TAC"

let (DISJ2_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_disj w in
          null_meta,[asl,r],fun i [th] -> disj2_rule (instantiate i l) th
    with Failure _ -> failwith "DISJ2_TAC"

let (DISJ_CASES_TAC: thm_tactic) =
  fun dth ->
    try let dtm = concl dth in
        let l,r = dest_disj dtm in
        let thl = assume_rule l
        let thr = assume_rule r in
        fun (asl,w) ->
          null_meta,[("",thl)::asl,w; ("",thr)::asl,w],
          fun i [th1;th2] -> disj_cases_rule (INSTANTIATE_ALL i dth) th1 th2
    with Failure _ -> failwith "DISJ_CASES_TAC"

let (CONTR_TAC: thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  fun cth (asl,w) ->
    try let th = contr_rule w cth in
        null_meta,[],propagate_thm th
    with Failure _ -> failwith "CONTR_TAC"

let (MATCH_ACCEPT_TAC:thm_tactic) =
  let propagate_thm th i [] = INSTANTIATE_ALL i th in
  let rawtac th (asl,w) =
    try let ith = PART_MATCH id th w in
        null_meta,[],propagate_thm ith
    with Failure _ -> failwith "ACCEPT_TAC" in
  fun th -> REPEAT GEN_TAC |> THEN <| rawtac th

// from bool
let GEN_ALL th =
  let asl,c = dest_thm th in
  let vars = subtract (free_vars c) (list_free_vars asl) in
  GENL vars th

let SIMPLE_CHOOSE v th =
  choose_rule(v,assume_rule (mk_exists(v,hd(asms th)))) th

let (MATCH_MP_TAC :thm_tactic) =
  fun th ->
    let sth =
      try let tm = concl th in
          let avs,bod = strip_forall tm in
          let ant,con = dest_imp bod in
          let th1 = SPECL avs (assume_rule tm) in
          let th2 = undisch_rule th1 in
          let evs = filter (fun v -> var_free_in v ant && not (var_free_in v con))
                           avs in
          let th3 = List.foldBack SIMPLE_CHOOSE evs (prim_disch_rule tm th2) in
          let tm3 = hd(asms th3) in
          prim_mp_rule (prim_disch_rule tm (GEN_ALL (prim_disch_rule tm3 (undisch_rule th3)))) th
      with Failure _ -> failwith "MATCH_MP_TAC: Bad theorem" in
    let match_fun = PART_MATCH (snd << dest_imp) sth in
    fun (asl,w) -> try let xth = match_fun w in
                       let lant = fst(dest_imp(concl xth)) in
                       null_meta,[asl,lant],
                       fun i [th] -> prim_mp_rule (INSTANTIATE_ALL i xth) th
                   with Failure _ -> failwith "MATCH_MP_TAC: No match"

(* ------------------------------------------------------------------------- *)
(* Theorem continuations.                                                    *)
(* ------------------------------------------------------------------------- *)

let CONJ_PAIR th =
  try conjunct1_rule th,conjunct2_rule th // da vedere
  with Failure _ -> failwith "CONJ_PAIR: Not a conjunction";

let (CONJUNCTS_THEN2:thm_tactic->thm_tactic->thm_tactic) =
  fun ttac1 ttac2 cth ->
      let c1,c2 = dest_conj(concl cth) in
      fun gl -> let ti,gls,jfn = (ttac1(assume_rule c1) |> THEN <| ttac2(assume_rule c2)) gl in
                let jfn' i ths =
                  let th1,th2 = CONJ_PAIR(INSTANTIATE_ALL i cth) in
                  prove_asm_rule th1 (prove_asm_rule th2 (jfn i ths)) in
                ti,gls,jfn'

let (CONJUNCTS_THEN: thm_tactical) =
  dbl_arg CONJUNCTS_THEN2

let (DISJ_CASES_THEN2:thm_tactic->thm_tactic->thm_tactic) =
  fun ttac1 ttac2 cth ->
    DISJ_CASES_TAC cth |> THENL <| [POP_ASSUM ttac1; POP_ASSUM ttac2]

let (DISJ_CASES_THEN: thm_tactical) =
  dbl_arg DISJ_CASES_THEN2

let (DISCH_THEN: thm_tactic -> tactic) =
  fun ttac -> DISCH_TAC |> THEN <| POP_ASSUM ttac

let (X_CHOOSE_THEN: term -> thm_tactical) =
  fun x ttac th -> X_CHOOSE_TAC x th |> THEN <| POP_ASSUM ttac

let (CHOOSE_THEN: thm_tactical) =
  fun ttac th -> CHOOSE_TAC th |> THEN <| POP_ASSUM ttac

(* ------------------------------------------------------------------------- *)
(* Various derived tactics and theorem continuations.                        *)
(* ------------------------------------------------------------------------- *)

let STRIP_THM_THEN =
  FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; CHOOSE_THEN]

let (ANTE_RES_THEN: thm_tactical) =                                             
  fun ttac ante ->                                                              
    ASSUM_LIST                                                                 
     (fun asl ->                                                              
        let tacs = mapfilter (fun imp -> ttac (MATCH_MP imp ante)) asl in
        match tacs with
        | [] -> failwith "IMP_RES_THEN"
        | _ -> EVERY tacs)

let (IMP_RES_THEN: thm_tactical) =                                             
  fun ttac imp ->                                                              
    ASSUM_LIST                                                                 
     (fun asl ->                                                              
        let tacs = mapfilter (fun ante -> ttac (MATCH_MP imp ante)) asl in
        match tacs with
        | [] -> failwith "IMP_RES_THEN"
        | _ -> EVERY tacs)

let STRIP_ASSUME_TAC =
  let DISCARD_TAC th =
    let tm = concl th in
    fun (asl,w as g) ->
       if exists (fun a -> alpha_eq tm (concl(snd a))) asl then ALL_TAC g
       else failwith "DISCARD_TAC: not already present" in
  (REPEAT_TCL STRIP_THM_THEN)
      (fun gth -> FIRST [CONTR_TAC gth; ACCEPT_TAC gth;
                         DISCARD_TAC gth; ASSUME_TAC gth])

let STRUCT_CASES_TAC =
    REPEAT_TCL STRIP_THM_THEN
     (fun th -> SUBST1_TAC th |> ORELSE <| ASSUME_TAC th)

let STRIP_GOAL_THEN ttac =  FIRST [GEN_TAC; CONJ_TAC; DISCH_THEN ttac]

let (STRIP_TAC: tactic) =
  fun g ->
    try STRIP_GOAL_THEN STRIP_ASSUME_TAC g
    with Failure _ -> failwith "STRIP_TAC"
        
let (UNDISCH_THEN:term->thm_tactic->tactic) =
  fun tm ttac (asl,w) ->
    let thp,asl' = remove1 (fun (_,th) -> alpha_eq (concl th) tm) asl in
    ttac (snd thp) (asl',w)

let FIRST_X_ASSUM ttac =
    FIRST_ASSUM(fun th -> UNDISCH_THEN (concl th) ttac)

(* ------------------------------------------------------------------------- *)
(* Subgoaling and freezing variables (latter is especially useful now).      *)
(* ------------------------------------------------------------------------- *)

let (SUBGOAL_THEN: term -> thm_tactic -> tactic) =
  fun wa ttac (asl,w) ->
    let meta,gl,just = ttac (assume_rule wa) (asl,w) in
    meta,(asl,wa)::gl,fun i l -> prove_asm_rule (hd l) (just i (tl l))

let SUBGOAL_TAC s tm prfs =
  match prfs with
   p::ps -> (warn (ps.Length <> 0) "SUBGOAL_TAC: additional subproofs ignored";
             SUBGOAL_THEN tm (LABEL_TAC s) |> THENL <| [p; ALL_TAC])
  | [] -> failwith "SUBGOAL_TAC: no subproof given"

let (FREEZE_THEN :thm_tactical) =
  fun ttac th (asl,w) ->
    let meta,gl,just = ttac (assume_rule(concl th)) (asl,w) in
    meta,gl,fun i l -> prove_asm_rule th (just i l)

(* ------------------------------------------------------------------------- *)
(* Metavariable tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

let (X_META_EXISTS_TAC: term -> tactic) =
  fun t (asl,w) ->
    try if not (is_var t) then failwith "X_META_EXISTS_TAC" else
        let v,bod = dest_exists w in
        ([t],null_inst),[asl,vsubst[t,v] bod],
        fun i [th] -> exists_rule (instantiate i w,instantiate i t) th
    with Failure _ -> failwith "X_META_EXISTS_TAC"

let META_EXISTS_TAC ((asl,w) as gl) =
  let v = fst(dest_exists w) in
  let avoids = List.foldBack (union << free_vars << concl << snd) asl (free_vars w) in
  let v' = mk_primed_var avoids v in
  X_META_EXISTS_TAC v' gl

let (META_SPEC_TAC: term -> thm -> tactic) =
  fun t thm (asl,w) ->
    let sth = spec_rule t thm in
    ([t],null_inst),[(("",sth)::asl),w],
    fun i [th] -> prove_asm_rule (spec_rule (instantiate i t) thm) th

(* ------------------------------------------------------------------------- *)
(* If all else fails!                                                        *)
(* ------------------------------------------------------------------------- *)

let (CHEAT_TAC:tactic) =
  fun (asl,w) -> ACCEPT_TAC(mk_thm([],w)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Intended for time-consuming rules; delays evaluation till it sees goal.   *)
(* ------------------------------------------------------------------------- *)

let RECALL_ACCEPT_TAC r a g = ACCEPT_TAC(time r a) g

(* ------------------------------------------------------------------------- *)
(* Split off antecedent of antecedent as a subgoal.                          *)
(* ------------------------------------------------------------------------- *)

let ANTS_TAC =
  let tm1 = parse_term(@"p /\ (q ==> r)")
  let tm2 = parse_term(@"p ==> q")
  let th1,th2 = CONJ_PAIR(assume_rule tm1) in
  let th = List.foldBack prim_disch_rule [tm1;tm2] (prim_mp_rule th2 (prim_mp_rule(assume_rule tm2) th1)) in
  MATCH_MP_TAC th |> THEN <| CONJ_TAC

(* ------------------------------------------------------------------------- *)
(* A printer for goals etc.                                                  *)
(* ------------------------------------------------------------------------- *)

/// Prints a term with surrounding quotes to formatter.
let pp_print_qterm fmt tm =
    pp_print_string fmt (print_qterm tm)

/// Prints a goal to formatter.
let pp_print_goal fmt (gl : goal) = 
    let string3 n = 
        if n < 10 then "  " + string n
        elif n < 100 then " " + string n
        else string n
    let pp_print_hyp fmt n (s, th : thm) =
        Format.pp_open_hbox fmt ()
        Format.pp_print_string fmt (string3 n)
        Format.pp_print_string fmt  " ["
        Format.pp_open_hbox fmt ()
        pp_print_qterm fmt (concl th)
        Format.pp_close_box fmt ()
        Format.pp_print_string fmt  "]"
        (if not(s = "") then (Format.pp_print_string fmt (" (" + s + ")"))
            else ())
        Format.pp_close_box fmt ()
        Format.pp_print_newline fmt ()
    let rec pp_print_hyps fmt n asl = 
        if asl = [] then ()
        else 
            (pp_print_hyp fmt n (hd asl)
             pp_print_hyps fmt (n + 1) (tl asl))
    let pp_print_asl_term fmt (asl, w) =
            Format.pp_print_newline fmt ()
            if asl <> [] then 
                (pp_print_hyps fmt 0 (rev asl)
                 Format.pp_print_newline fmt ())
            else ()
            pp_print_qterm fmt w
            Format.pp_print_newline fmt ()
    pp_print_asl_term fmt gl

/// Print a goal to standard output, with no following newline.
let print_goal = pp_print_goal std_formatter

/// Converts a goal to a string representation.
let string_of_goal = print_to_string pp_print_goal

/// Prints a list of goals to formatter.
let pp_print_list_goal fmt (al : goal list) =
    let rec pp_print_list_goalInner fmt al =
        match al with
        | g :: tl ->
            pp_print_goal fmt g
            pp_print_break fmt 0 0
            pp_print_list_goalInner fmt tl
        | [] -> ()
    if al.Length = 0
    then pp_print_string fmt "No goals"
    else
        pp_open_hvbox fmt 0
        pp_print_list_goalInner fmt al
        pp_close_box fmt ()

/// Print a list of goals to standard output, with no following newline.
let print_list_goal = pp_print_list_goal std_formatter

/// Converts a list of goals to a string representation.
let string_of_list_goal = print_to_string pp_print_list_goal

/// Prints a list of (term * term) to formatter.
let pp_print_list_trmtrm fmt (al : (term * term) list) =
    let rec pp_print_list_trmtrmInner fmt al =
        match al with
        | (trma,trmb) :: tl ->
            pp_print_term fmt trma
            pp_print_string fmt ", "
            pp_print_term fmt trmb
            pp_print_break fmt 0 0
            pp_print_list_trmtrmInner fmt tl
        | [] -> ()
    if al.Length = 0
    then pp_print_string fmt "No items"
    else
        pp_open_hvbox fmt 0
        pp_print_list_trmtrmInner fmt al
        pp_close_box fmt ()

let rec el0 n l = 
    if n = 0 then hd l
    else el0 (n - 1) (tl l)

/// Prints a goalstack to formatter.
let pp_print_goalstack fmt gs =
    let pp_print_goalstate fmt k (gs : goalstate) = 
        let (_, gl, _) = gs
        let n = length gl
        let s = 
            if n = 0 then "No subgoals"
            else
                (string k) + " subgoal" + (if k > 1 then "s" else "") + " (" + (string n) + " total)"
        Format.pp_print_string fmt s
        Format.pp_print_newline fmt ()
        if not <| List.isEmpty gl then
            List.iter (pp_print_goal fmt << swap_arg el0 gl) (rev([0..(k - 1)]))

    let pp_print_goalstates fmt (l : goalstack) =
        // OPTIMIZE : Use pattern-matching here -- it's faster than checking the length
        // of the list, since we don't need to traverse the entire list.
        match l with
        | [] ->
            Format.pp_print_string fmt "Empty goalstack"
        | [x] -> 
            let gs = x
            pp_print_goalstate fmt 1 gs
        | x :: y :: _ -> 
            let (_, gl, _ as gs) = x
            let (_, gl0, _) = y
            let p = length gl - length gl0
            let p' = 
                if p < 1 then 1
                else p + 1
            pp_print_goalstate fmt p' gs
    pp_print_goalstates fmt gs

/// Print a goalstack to standard output, with no following newline.
let print_goalstack = pp_print_goalstack std_formatter

/// Converts a goalstack to a string representation.
let string_of_goalstack = print_to_string pp_print_goalstack

/// Prints a goalstate to formatter.
let pp_print_goalstate fmt gs =
    let ((trml,inst),gl,j) = gs
    let rec pp_print_trml fmt trml =
        match trml with
        | trm :: tl ->
            pp_print_term fmt trm
            pp_print_break fmt 0 0
            pp_print_trml fmt tl
        | [] -> ()
    pp_print_trml fmt trml
    pp_print_instantiation fmt inst
    let rec pp_print_gl fmt gl =
        match gl with
        | g :: tl ->
            pp_print_goal fmt g
            pp_print_break fmt 0 0
            pp_print_gl fmt tl
        | [] -> ()
    pp_print_gl fmt gl
    pp_print_justification fmt j

/// Prints a goalstate (without quotes) to the standard output.
let print_goalstate = pp_print_goalstate std_formatter

/// Converts a goalstate to a string representation.
let string_of_goalstate = print_to_string pp_print_goalstate
(* ------------------------------------------------------------------------- *)
(* Convert a tactic into a refinement on head subgoal in current state.      *)
(* ------------------------------------------------------------------------- *)

let (by:tactic->refinement) =
  fun tac ((mvs,inst),gls,just) ->
    if gls = [] then failwith "No goal set" else
    let g = hd gls
    let ogls = tl gls in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let n = length subgls in
    let mvs' = union newmvs mvs
    let inst' = compose_insts inst newinst
    let gls' = subgls @ map (inst_goal newinst) ogls in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = cut n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),gls',just'

(* ------------------------------------------------------------------------- *)
(* Rotate the goalstate either way.                                          *)
(* ------------------------------------------------------------------------- *)

let (rotate:int->refinement) =
  let rotate_p (meta,sgs,just) =
    let sgs' = (tl sgs)@[hd sgs] in
    let just' i ths =
      let ths' = (last ths)::(butlast ths) in
      just i ths' in
    (meta,sgs',just')
  let rotate_n (meta,sgs,just) =
    let sgs' = (last sgs)::(butlast sgs) in
    let just' i ths =
      let ths' = (tl ths)@[hd ths] in
      just i ths' in
    (meta,sgs',just') in
  fun n -> if n > 0 then funpow n rotate_p
           else funpow (-n) rotate_n

(* ------------------------------------------------------------------------- *)
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_goalstate:goal->goalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      null_meta,[asl,w],
      (fun inst [th] -> INSTANTIATE_ALL inst th)
    else failwith "mk_goalstate: Non-boolean goal"

let (TAC_PROOF : goal * tactic -> thm) =
  fun (g,tac) ->
    let gstate = mk_goalstate g in
    let _,sgs,just = by tac gstate in
    if sgs = [] then just null_inst []
    else failwith "TAC_PROOF: Unsolved goals"

let prove(t,tac) =
  let th = TAC_PROOF(([],t),tac) in
  let t' = concl th in
  if t' = t then th else
  try prim_eq_mp_rule (ALPHA t' t) th
  with Failure _ -> failwith "prove: justification generated wrong theorem"

(* ------------------------------------------------------------------------- *)
(* Interactive "subgoal package" stuff.                                      *)
(* ------------------------------------------------------------------------- *)

let current_goalstack = ref ([] :goalstack)

let (refine:refinement->goalstack) =
  fun r ->
    let l = !current_goalstack in
    match l with
    | [] -> failwith "No current goal"
    | _ -> 
        let h = hd l in
        let res = r h :: l in
        current_goalstack := res;
        !current_goalstack

let flush_goalstack() =
  let l = !current_goalstack in
  current_goalstack := [hd l]

let e1 tac = refine(by(VALID tac))

let r n = refine(rotate n)

let set_goal(asl,w) =
  current_goalstack :=
    [mk_goalstate(map (fun t -> "",assume_rule t) asl,w)];
  !current_goalstack

let rec sort cmp lis = 
    match lis with
    | [] -> []
    | piv :: rest -> 
        let r, l = partition (cmp piv) rest
        (sort cmp l) @ (piv :: (sort cmp r))

let g t =
  let fvs = sort (<) (map (fst << dest_var) (free_vars t)) in
  (if fvs <> [] then
     let errmsg = List.reduceBack (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   set_goal([],t)

let b() =
  let l = !current_goalstack in
  if length l = 1 then failwith "Can't back up any more" else
  current_goalstack := tl l;
  !current_goalstack

let p() =
  !current_goalstack

let top_realgoal() =
  let (_,((asl,w)::_),_)::_ = !current_goalstack in
  asl,w

let top_goal() =
  let asl,w = top_realgoal() in
  map (concl << snd) asl,w

let top_thm() =
  let (_,[],f)::_ = !current_goalstack in
  f null_inst []