open HolKernel boolLib Parse bossLib;
open listTheory rich_listTheory pairTheory relationTheory miscTheory arithmeticTheory;

val _ = new_theory "execution";

(* TODO move upstream *)

Theorem steps_rel_RIGHT1:
  !R x tr j y k z.
  steps_rel R x $ tr ++ [(j,y); (k,z)]
  <=> steps_rel R x $ tr ++ [(j,y)] /\ R y k z
Proof
  ho_match_mp_tac miscTheory.steps_rel_ind
  >> rw[miscTheory.steps_rel_def,EQ_IMP_THM,FORALL_AND_THM]
  >> first_x_assum drule_all >> fs[]
QED

Theorem RC_RTC_EQ:
  !R. RC (RTC R) = RTC R
Proof
  rw[relationTheory.RC_DEF,FUN_EQ_THM,EQ_IMP_THM]
  >> fs[RTC_REFL]
QED

(* ------------------------------------------- *)
(* Execution following a labeled step relation *)
(* ------------------------------------------- *)

(* - an "execution" is a list of tuples of states and labels: ('state # 'label # 'state) list
   - a "step relation" is a relation: 'state -> 'label -> 'state -> bool
   - a "step execution" for a step relation is
     * an singleton execution which is a valid step
     * a step execution with a last element,  where the last element can be
       removed to form a step execution, and a valid step can be formed from the elements
  - drawback: duplication of states in tuples
*)

Inductive step_execution:
  (!s l s'. R s l s' ==> step_execution R [(s,l,s')])
[/\]
  (!(e:('state # 'label # 'state) list) s1 l1 s2 l2 s3.
    (step_execution R (e ++ [(s1,l1,s2)]) /\ R s2 l2 s3) ==>
    (step_execution R (e ++ [(s1,l1,s2);(s2,l2,s3)])))
End

Theorem step_execution_steps_rel:
  !R ls. step_execution R ls ==> steps_rel R (FST $ HD ls) $ MAP SND ls
Proof
  gen_tac >> ho_match_mp_tac step_execution_ind
  >> rw[miscTheory.steps_rel_def,steps_rel_RIGHT1]
  >> qhdtm_x_assum `steps_rel` mp_tac
  >> rewrite_tac[GSYM EL,EL_APPEND_EQN]
  >> fs[]
QED

Definition trace:
 trace (obs_of_label:'label -> 'obs) (exec:('state # 'label # 'state) list) =
  MAP (obs_of_label o FST o SND) exec
End

(* sanity checking *)
Theorem step_execution_singleton:
 !R s l s'. step_execution R [(s,l,s')] <=> R s l s'
Proof
  fs[Once step_execution_cases]
QED

Theorem step_execution_singleton':
  !R e. step_execution R [e] <=> R (FST e) (FST $ SND e) (SND $ SND e)
Proof
  gen_tac >> PairCases >> fs[step_execution_singleton]
QED

(* sanity checking *)
Theorem step_execution_not_empty_list:
 !R e. step_execution R e ==> e <> []
Proof
  fs[Once step_execution_cases]
QED

Theorem step_execution_EVERY:
  !R ls. step_execution R ls ==> EVERY (λ(s,tm,s'). R s tm s') ls
Proof
  gen_tac
  >> ho_match_mp_tac step_execution_ind
  >> fs[]
QED

Theorem step_execution_RIGHT1':
 !R e s l.
  ~NULL e
  ==> step_execution R (e ++ [(SND $ SND $ LAST e,l,s)])
    = (step_execution R e /\ R (SND $ SND $ LAST e) l s)
Proof
  rpt strip_tac
  >> CONV_TAC $ LAND_CONV $ ONCE_REWRITE_CONV[step_execution_cases]
  >> rename1`~NULL e`
  >> Cases_on `e` using SNOC_CASES >- fs[]
  >> rename1`SNOC x _` >> PairCases_on `x`
  >> fs[SNOC_APPEND]
QED

Theorem step_execution_LEFT1':
 !R e s l s'.
  ~NULL e
  ==> step_execution R ((s,l,FST $ HD e)::e)
    = (step_execution R e /\ R s l (FST $ HD e))
Proof
  ntac 2 gen_tac >> Induct_on `LENGTH e`
  >> fs[AND_IMP_INTRO,PULL_FORALL]
  >> rpt strip_tac
  >> rename1`SUC v = LENGTH e`
  >> Cases_on `e` using SNOC_CASES >- fs[]
  >> rename1`SNOC x _` >> PairCases_on `x` >> fs[SNOC_APPEND]
  >> Cases_on `v`
  >> once_rewrite_tac[step_execution_cases]
  >- fs[step_execution_singleton,AC CONJ_ASSOC CONJ_COMM]
  >> rename1 `SUC n = LENGTH l'`
  >> qpat_x_assum `SUC n = LENGTH l'` $ assume_tac o GSYM
  >> fs[Excl"LENGTH_NIL.1",NULL_LENGTH,GSYM NULL_EQ]
  >> Cases_on `l'` using SNOC_CASES >> fs[]
  >> PairCases_on `x` >> fs[SNOC_APPEND]
  >> once_rewrite_tac[GSYM APPEND_ASSOC]
  >> rewrite_tac[GSYM rich_listTheory.CONS_APPEND]
  >> qmatch_goalsub_abbrev_tac `step_execution R ((s,l,_)::l')`
  >> first_x_assum $ qspecl_then [`l'`,`s`,`l`] mp_tac
  >> unabbrev_all_tac
  >> rewrite_tac[GSYM EL,EL_APPEND_EQN]
  >> fs[]
  >> strip_tac >> EQ_TAC >> strip_tac
  >> gvs[AC CONJ_ASSOC CONJ_COMM]
QED

Theorem steps_rel_step_execution:
  !ls R x. steps_rel R x ls /\ ~NULL ls
  ==> step_execution R $ ZIP (x::MAP SND ls,ls)
Proof
  Induct >- fs[] >> PairCases
  >> rw[miscTheory.steps_rel_def]
  >> Cases_on `ls` >- fs[ZIP_def,Once step_execution_cases]
  >> rename1`h::t` >> PairCases_on `h` >> fs[]
  >> first_x_assum $ drule_then assume_tac
  >> drule_at Any $ iffRL step_execution_LEFT1'
  >> fs[]
QED

Theorem step_execution_append_eq_state_base:
 !R s1 l1 s2 s3 l2 s4 e.
  step_execution R (e ++ [(s1,l1,s2); (s3,l2,s4)]) ==>
  s2 = s3
Proof
  fs[Once step_execution_cases]
QED

Theorem step_execution_reduce_one:
 !R e s l s'.
  e <> [] ==>
  step_execution R (e ++ [(s,l,s')]) ==>
  step_execution R e /\ R s l s'
Proof
  ntac 6 strip_tac
  >> Cases_on `e` using SNOC_CASES >- fs[]
  >> fs[SNOC_APPEND] >> PairCases_on `x`
  >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> REWRITE_TAC[GSYM rich_listTheory.CONS_APPEND]
  >> CONV_TAC $ LAND_CONV $ ONCE_REWRITE_CONV[step_execution_cases]
  >> fs[]
QED

Theorem APPEND_mid_not_empty:
 !e1 x y e2. e1 ++ [x; y] ++ e2 <> []
Proof
 Induct >> rw []
QED

Theorem step_execution_append_eq_state:
 !R e1 e2 s1 l1 s2 s3 l2 s4.
 step_execution R (e1 ++ [(s1,l1,s2); (s3,l2,s4)] ++ e2) ==>
 s2 = s3
Proof
 STRIP_TAC >> STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >>
 rw [] >- METIS_TAC [step_execution_append_eq_state_base] >>
 fs [SNOC_APPEND] >>
 `step_execution R (e1 ++ [(s1,l1,s2); (s3,l2,s4)] ++ e2)` suffices_by METIS_TAC [] >>
 Cases_on `x` >> Cases_on `r` >>
 `e1 ++ [(s1,l1,s2); (s3,l2,s4)] ++ e2 <> []` suffices_by METIS_TAC [step_execution_reduce_one] >>
 METIS_TAC [APPEND_mid_not_empty]
QED

Theorem step_execution_append_eq_state':
  !R e1 e2 e e'.
  step_execution R (e1 ++ [e; e'] ++ e2) ==> SND $ SND e = FST e'
Proof
  ntac 3 gen_tac >> ntac 2 PairCases >> strip_tac
  >> drule step_execution_append_eq_state
  >> fs[]
QED

Theorem step_execution_conseq_eq_state:
  !R ls i. step_execution R ls
  /\ SUC i < LENGTH ls
  ==> SND $ SND $ EL i ls = FST $ EL (SUC i) ls
Proof
  rw[]
  >> qspec_then `R` irule step_execution_append_eq_state'
  >> map_every qexists_tac [`R`,`TAKE i ls`,`DROP (i + 2) ls`]
  >> qmatch_goalsub_abbrev_tac`_ ++ seg' ++ _`
  >> `seg' = SEG 2 i ls` by (
    unabbrev_all_tac
    >> rewrite_tac[arithmeticTheory.TWO]
    >> fs[rich_listTheory.SEG_SUC_EL,rich_listTheory.SEG1,arithmeticTheory.ADD1]
  )
  >> pop_assum $ simp o single
  >> fs[rich_listTheory.TAKE_SEG_DROP]
QED

Theorem step_execution_append_end_eq_state:
  !R e s1 l1 s2.
  step_execution R (e ++ [(s1,l1,s2)]) /\ ~NULL e
  ==> SND $ SND $ LAST e = s1 /\ R s1 l1 s2
Proof
  rpt gen_tac >> strip_tac
  >> drule_then assume_tac step_execution_EVERY
  >> drule_then assume_tac step_execution_conseq_eq_state
  >> fs[EL_APPEND_EQN,COND_RATOR,COND_RAND,COND_EXPAND_IMP,IMP_CONJ_THM,FORALL_AND_THM,AND_IMP_INTRO]
  >> fs[GSYM ADD1,NOT_LESS,LE,LEFT_AND_OVER_OR,LAST_EL,GSYM NULL_EQ]
  >> first_x_assum irule
  >> fs[NULL_LENGTH,NOT_ZERO_LT_ZERO,Excl"LENGTH_NIL.1"]
QED

(* custom transitive closure relation for labeled relations *)
Inductive LTC:
  (!s l s'. R s l s' ==> LTC R s s')
[/\]
  (!x y z. LTC R x y /\ LTC R y z ==> LTC R x z)
End

Theorem LTC_eq_NRC_SUC:
  !R s s'. LTC R s s' <=> ?n. NRC (λs s'. ?l. R s l s') (SUC n) s s'
Proof
  gen_tac
  >> dsimp[EQ_IMP_THM]
  >> conj_tac
  >- (
    ho_match_mp_tac LTC_ind
    >> conj_tac
    >- (
      rpt strip_tac
      >> irule_at Any $ REWRITE_RULE[arithmeticTheory.ONE] $ iffRL arithmeticTheory.NRC_1
      >> CONV_TAC $ DEPTH_CONV BETA_CONV
      >> goal_assum drule
    )
    >> fs[GSYM arithmeticTheory.TC_eq_NRC]
    >> rpt strip_tac
    >> dxrule_all_then irule $ REWRITE_RULE[transitive_def] TC_TRANSITIVE
  )
  >> Induct_on`n`
  >- fs[Once LTC_cases]
  >> rw[Once arithmeticTheory.NRC]
  >> first_x_assum $ drule_then assume_tac
  >> dxrule_then assume_tac $ cj 1 LTC_rules
  >> dxrule_all_then irule $ cj 2 LTC_rules
QED

Theorem LTC_eq_TC:
  !R s s'. LTC R = TC (λs s'. ?l. R s l s')
Proof
  fs[FUN_EQ_THM,arithmeticTheory.TC_eq_NRC,LTC_eq_NRC_SUC]
QED

Theorem singleton_neq_doubleton[local]:
 !e a b c. [a] <> e ++ [b; c]
Proof
 Induct >> rw []
QED

Theorem cons_append_eq[local]:
 !e e' a. a::(e ++ e') = a::e ++ e'
Proof
 Induct >> rw []
QED

Theorem step_execution_rest:
 !R e s1 l1 s2 s3 l2 s4.
 step_execution R (e ++ [(s1,l1,s2); (s3,l2,s4)]) ==>
 step_execution R (e ++ [(s1,l1,s2)]) /\ R s3 l2 s4
Proof
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 `e ++ [(s1,l1,s2)] <> []` by (Induct_on `e` >> rw []) >>
 `e ++ [(s1,l1,s2); (s3,l2,s4)] = (e ++ [(s1,l1,s2)]) ++ [(s3,l2,s4)]` by fs [] >>
 METIS_TAC [step_execution_reduce_one]
QED

Theorem step_execution_mid:
 !R e e' s1 l1 s2.
  step_execution R (e' ++ (s1,l1,s2)::e) ==>
  R s1 l1 s2
Proof
 STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >> rw [] >-
  (Cases_on `e'` >-
    (fs [] >>
     `(?s l s'. [(s1,l1,s2)] = [(s,l,s')] /\ R s l s') \/
        ?e s1' l1' s2' l2' s3'.
         [(s1,l1,s2)] = e ++ [(s1',l1',s2'); (s2',l2',s3')]`
     by METIS_TAC [step_execution_cases] >> fs []) >>
   `h :: t <> []` by fs [] >>
   METIS_TAC [step_execution_reduce_one]) >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >>
 `e' ++ (s1,l1,s2)::(e ++ [(q,q',r')]) = e' ++ (s1,l1,s2)::e ++ [(q,q',r')]`
  by fs [] >>
 `e' ++ (s1,l1,s2)::e <> []` by fs [] >>
 METIS_TAC [step_execution_reduce_one]
QED

Theorem step_execution_remove_head:
 !R e s1 l1 s2.
  e <> [] ==>
  step_execution R ((s1,l1,s2)::e) ==>
  step_execution R e
Proof
 STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >> rw [] >>
 Cases_on `x` >> Cases_on `r` >>
 fs [SNOC_APPEND] >>
 `(s1,l1,s2)::(e ++ [(q,q',r')]) = (s1,l1,s2)::e ++ [(q,q',r')]` by fs [] >>
 `step_execution R ((s1,l1,s2)::e ++ [(q,q',r')])` by METIS_TAC [] >>
 `(s1,l1,s2)::e <> []` by fs [] >>
 `step_execution R ((s1,l1,s2)::e) /\ R q q' r'` by METIS_TAC [step_execution_reduce_one] >>
 `e = [] \/ ?x l. e = SNOC x l` by METIS_TAC [SNOC_CASES] >-
 (fs [] >> METIS_TAC [step_execution_rules]) >>
 fs [SNOC_APPEND] >> rw [] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(l ++ [(q'',q''',r'')] ++ [(q,q',r')]) =
  (s1,l1,s2)::l ++ [(q'',q''',r'');(q,q',r')]` by fs [] >>
 `step_execution R ((s1,l1,s2)::l ++ [(q'',q''',r'');(q,q',r')])`
  by METIS_TAC [] >>
 `r'' = q` by METIS_TAC [step_execution_append_eq_state_base] >> rw [] >>
 `l ++ [(q'',q''',q)] ++ [(q,q',r')] = l ++ [(q'',q''',q);(q,q',r')]`
  by fs [] >> rw [] >>
 METIS_TAC [step_execution_rules]
QED

Theorem step_execution_DROP:
  !R n e. step_execution R e /\ n < LENGTH e ==> step_execution R $ DROP n e
Proof
  gen_tac >> Induct >> rw[]
  >> qmatch_asmsub_rename_tac `LENGTH e` >> Cases_on `e`
  >> fs[rich_listTheory.DROP] >> rename1`h::t` >> PairCases_on `h`
  >> dxrule_at_then Any assume_tac $ MP_CANON step_execution_remove_head
  >> fs[Excl"LENGTH_NIL.1",NULL_LENGTH,GSYM NULL_EQ]
QED

Theorem step_execution_TAKE:
  !R e n. step_execution R e ==> step_execution R $ TAKE (SUC n) e
Proof
  gen_tac >> fs[GSYM PULL_FORALL]
  >> ho_match_mp_tac step_execution_ind
  >> rw[step_execution_singleton']
  >> Cases_on `n <= LENGTH e`
  >- (
    fs[TAKE_APPEND,arithmeticTheory.SUB,COND_RAND,COND_RATOR,COND_EXPAND_IMP,FORALL_AND_THM,TAKE_LENGTH_TOO_LONG,NOT_LESS]
    >> rw[]
    >> dxrule_all_then assume_tac $ iffRL EQ_LESS_EQ
    >> fs[LESS_OR_EQ]
  )
  >> fs[NOT_LESS_EQUAL,TAKE_APPEND]
  >> once_rewrite_tac[CONS_APPEND]
  >> once_rewrite_tac[APPEND_ASSOC]
  >> qmatch_goalsub_abbrev_tac `e' ++ _`
  >> qspecl_then [`R`,`e'`] mp_tac step_execution_RIGHT1'
  >> unabbrev_all_tac
  >> fs[LAST_EL]
  >> disch_then kall_tac
  >> fs[TAKE_APPEND,arithmeticTheory.SUB,COND_RAND,COND_RATOR,COND_EXPAND_IMP,FORALL_AND_THM,TAKE_LENGTH_TOO_LONG,NOT_LESS,LESS_OR_EQ]
QED

Theorem step_execution_mid_execution:
 !R e' e s1 l1 s2.
  step_execution R (e' ++ (s1,l1,s2)::e) ==>
  step_execution R ((s1,l1,s2)::e)
Proof
 STRIP_TAC >>
 Induct_on `e'` >> fs [] >> rw [] >>
 `e' ++ (s1,l1,s2)::e <> []` by (Cases_on `e'` >> fs []) >>
 Cases_on `h` >> Cases_on `r` >>
 `step_execution R (e' ++ (s1,l1,s2)::e)`
  by METIS_TAC [step_execution_remove_head] >>
 METIS_TAC []
QED

Theorem step_execution_LTC:
 !R e s1 l1 s2 s3 l2 s4.
  LAST ((s1,l1,s2)::e) = (s3,l2,s4) ==>
  step_execution R ((s1,l1,s2)::e) ==>
  LTC R s1 s4
Proof
 STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >> rw [] >-
  (`?l. R s1 l s2` suffices_by METIS_TAC [LTC_rules] >>
   Q.EXISTS_TAC `l1` >>
   `(?s l s'. [(s1,l1,s2)] = [(s,l,s')] /\ R s l s') \/
    ?e s1' l1' s2' l2 s3.
     [(s1,l1,s2)] = e ++ [(s1',l1',s2'); (s2',l2,s3)] /\
      step_execution R (e ++ [(s1',l1',s2')]) /\ R s2' l2 s3`
    by METIS_TAC [step_execution_cases] >- fs [] >>
   METIS_TAC [singleton_neq_doubleton]) >>
 fs [LAST_DEF] >> fs [SNOC_APPEND] >>
 rw [] >>
 `e = [] \/ ?x e'. e = SNOC x e'` by rw [SNOC_CASES] >-
  (fs [] >>
   `[(s1,l1,s2); (s3,l2,s4)] = [] ++ [(s1,l1,s2); (s3,l2,s4)]` by fs [] >>
   `s2 = s3` by METIS_TAC [step_execution_append_eq_state_base] >>
   rw [] >>
   `step_execution R ([] ++ [(s1,l1,s2); (s2,l2,s4)])`
    by METIS_TAC [] >>
   `step_execution R ([] ++ [(s1,l1,s2)]) /\ R s2 l2 s4`
    by METIS_TAC [step_execution_rest] >>
   fs [] >>
   `LTC R s1 s2` by METIS_TAC [] >>
   `LTC R s2 s4` by METIS_TAC [LTC_rules] >>
   METIS_TAC [LTC_rules]) >>
 fs [] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(e' ++ [(q,q',r')] ++ [(s3,l2,s4)]) =
  (s1,l1,s2)::e' ++ [(q,q',r');(s3,l2,s4)]` by fs [] >>
 `step_execution R ((s1,l1,s2)::e' ++ [(q,q',r');(s3,l2,s4)])`
  by METIS_TAC [] >>
 `(s1,l1,s2)::e' <> []` by rw [] >>
 `step_execution R (((s1,l1,s2)::e') ++ [(q,q',r')]) /\ R s3 l2 s4`
  by METIS_TAC [step_execution_rest] >>
 `(s1,l1,s2)::e' ++ [(q,q',r')] = (s1,l1,s2)::(e' ++ [(q,q',r')])`
  by fs [] >>
 `LTC R s1 r'` by METIS_TAC [] >>
 `LTC R s3 s4` by METIS_TAC [LTC_rules] >>
 `r' = s3` suffices_by METIS_TAC [LTC_rules] >>
 METIS_TAC [step_execution_append_eq_state_base]
QED

Theorem step_execution_LTC':
  !R ls. step_execution R ls ==> LTC R (FST $ HD ls) (SND $ SND $ LAST ls)
Proof
  rpt strip_tac
  >> imp_res_tac step_execution_not_empty_list
  >> qmatch_asmsub_rename_tac `step_execution R ls`
  >> Cases_on `ls` >> fs[] >> rename1`h::t`
  >> PairCases_on `h` >> fs[]
  >> drule_at_then Any irule $ MP_CANON step_execution_LTC
  >> fs[pairTheory.PAIR_FST_SND_EQ]
QED

Theorem step_execution_RTC:
  !R tr. step_execution R tr
  ==> !i. i < LENGTH tr
    ==> RTC (λs s'. ?l. R s l s') (FST $ HD tr) (SND $ SND $ EL i tr)
Proof
  rpt strip_tac
  >> qmatch_goalsub_rename_tac `EL n tr`
  >> dxrule_then (qspec_then `n` assume_tac) step_execution_TAKE
  >> dxrule_then assume_tac step_execution_LTC'
  >> gs[LTC_eq_NRC_SUC,LAST_EL,Excl"LENGTH_NIL.1",NULL_LENGTH,GSYM NULL_EQ,EL_TAKE,Excl"EL_restricted.1",GSYM EL]
  >> dxrule_then irule NRC_RTC
QED

(* straightforward corollary *)
Theorem step_execution_LTC_end[local]:
 !R e s1 l1 s2 s3 l2 s4.
  step_execution R ((s1,l1,s2)::e ++ [(s3,l2,s4)]) ==>
  LTC R s1 s4
Proof
 rw [] >>
 `LAST ((s1,l1,s2)::(e ++ [(s3,l2,s4)])) = (s3,l2,s4)`
  suffices_by METIS_TAC [step_execution_LTC] >>
 fs [LAST_DEF]
QED

Theorem step_execution_mid_LTC[local]:
 !R e e' s1 l1 s2 s3 l2 s4.
  step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) ==>
  LTC R s1 s4
Proof
 STRIP_TAC >>
 HO_MATCH_MP_TAC SNOC_INDUCT >> rw [] >-
 METIS_TAC [cons_append_eq,step_execution_LTC_end] >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(e' ++ (s3,l2,s4)::(e ++ [(q,q',r')])) =
  (s1,l1,s2)::e' ++ (s3,l2,s4)::e ++ [(q,q',r')]` by fs [] >>
 `(s1,l1,s2)::e' ++ (s3,l2,s4)::e <> []` by fs [] >>
 `step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) /\ R q q' r'`
  by METIS_TAC [step_execution_reduce_one] >>
 `(s1,l1,s2)::e' ++ (s3,l2,s4)::e = (s1,l1,s2)::(e' ++ (s3,l2,s4)::e)`
  by fs [] >>
 METIS_TAC []
QED

Theorem step_execution_mid_FST_LTC[local]:
 !R e e' s1 l1 s2 s3 l2 s4.
  step_execution R ((s1,l1,s2)::e ++ (s3,l2,s4)::e') ==>
  LTC R s1 s3
Proof
 STRIP_TAC >> STRIP_TAC >>
 `e = [] \/ ?x e'. e = SNOC x e'`
  by METIS_TAC [SNOC_CASES] >> rw [] >-
  (`(s1,l1,s2)::(s3,l2,s4)::e' = [] ++ [(s1,l1,s2);(s3,l2,s4)] ++ e'`
    by fs [] >>
   `s2 = s3` by METIS_TAC [step_execution_append_eq_state] >>
   rw [] >>
   `(s1,l1,s2)::(s2,l2,s4)::e' = [] ++ (s1,l1,s2)::((s2,l2,s4)::e')` by fs [] >>
   METIS_TAC [step_execution_mid,LTC_rules]) >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(e' ++ [(q,q',r')] ++ (s3,l2,s4)::e'') =
   (s1,l1,s2)::e' ++ [(q,q',r');(s3,l2,s4)] ++ e''`
  by fs [] >>
 `r' = s3` by METIS_TAC [step_execution_append_eq_state] >>
 rw [] >>
 `(s1,l1,s2)::(e' ++ [(q,q',r')] ++ (r',l2,s4)::e'') =
   (s1,l1,s2)::e' ++ (q,q',r')::((r',l2,s4)::e'')`
  by fs [] >>
 METIS_TAC [step_execution_mid_LTC]
QED

Theorem LTC_truncate_TC[local]:
 !R x y. LTC R x y <=> TC (\a b. ?l. R a l b) x y
Proof
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> EQ_TAC >-
  (match_mp_tac LTC_ind >> rw [] >-
    (rw [TC_DEF] >> METIS_TAC []) >>
   METIS_TAC [TC_TRANSITIVE,transitive_def]) >>
 once_rewrite_tac [TC_DEF] >>
 `(!x y. (\a b. ?l. R a l b) x y ==> LTC R x y) /\
  (!x y z. LTC R x y /\ LTC R y z ==> LTC R x z)`
 suffices_by METIS_TAC [] >>
 rw [] >> METIS_TAC [LTC_rules]
QED

Theorem step_execution_RTC':
  !R ls. step_execution R ls ==> TC (λs s'. ?l. R s l s') (FST $ HD ls) (SND $ SND $ LAST ls)
Proof
  rpt strip_tac
  >> dxrule step_execution_LTC'
  >> fs[LTC_truncate_TC]
QED

Definition step_invariant:
 step_invariant
  (R: 'state -> 'label -> 'state -> bool)
  (P: 'state -> bool) =
  !s l s'. P s ==> R s l s' ==> P s'
End

Definition LTC_invariant:
  LTC_invariant
    (R: 'state -> 'label -> 'state -> bool)
    (P: 'state -> bool) =
  !s s'. P s ==> LTC R s s' ==> P s'
End

Theorem step_invariant_LTC[local]:
 !R P s s'. LTC R s s' ==> P s ==> step_invariant R P ==> P s'
Proof
 STRIP_TAC >> STRIP_TAC >> ho_match_mp_tac LTC_ind >> rw [] >>
 METIS_TAC [step_invariant]
QED

Theorem step_invariant_LTC_invariant:
 !R P. step_invariant R P ==> LTC_invariant R P
Proof
 METIS_TAC [LTC_invariant,step_invariant_LTC]
QED

Theorem step_execution_mid_LTC_invariant:
 !R P. LTC_invariant R P ==>
 !e e' s1 l1 s2 s3 l2 s4. P s1 ==>
  step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) ==>
  P s4
Proof
  ntac 13 strip_tac >>
 `LTC R s1 s4` by METIS_TAC [step_execution_mid_LTC] >>
  fs[LTC_invariant]
  >> first_x_assum $ drule_all_then irule
QED

Theorem step_execution_mid_FST_LTC_invariant:
 !R P. LTC_invariant R P ==>
 !e e' s1 l1 s2 s3 l2 s4. P s1 ==>
  step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) ==>
  P s3
Proof
 ntac 13 strip_tac >>
 `LTC R s1 s3` by METIS_TAC [step_execution_mid_FST_LTC] >>
 fs[LTC_invariant]
 >> first_x_assum $ drule_all_then irule
QED

Theorem step_execution_append_one:
 !R e s l s'.
  step_execution R e /\ SND (SND (LAST e)) = s /\ R s l s' ==>
  step_execution R (e ++ [(s,l,s')])
Proof
  STRIP_TAC >>
  ho_match_mp_tac SNOC_INDUCT >>
  rw [] >| [
    METIS_TAC [step_execution_not_empty_list],
    fs [SNOC_APPEND] >>
    Cases_on `x` >> Cases_on `r` >>
    fs[] >>
    `step_execution R (e ++ [(q,q',r'); (r',l,s')])`
      by METIS_TAC [step_execution_cases] >>
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    rewrite_tac[GSYM rich_listTheory.CONS_APPEND] >>
    asm_rewrite_tac[]
  ]
QED

Theorem step_execution_EVERY_step_invariant:
  !R ls P. step_execution R ls
  /\ step_invariant R P /\ P $ FST $ HD ls
  ==> EVERY P $ MAP FST ls /\ EVERY P $ MAP (SND o SND) ls
Proof
  fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> gen_tac
  >> ho_match_mp_tac step_execution_ind
  >> conj_tac
  >- (
    rw[step_invariant]
    >> first_x_assum $ drule_all_then irule
  )
  >> PURE_REWRITE_TAC[AND_IMP_INTRO]
  >> rpt gen_tac >> strip_tac
  >> rpt gen_tac >> strip_tac
  >> first_x_assum drule
  >> impl_tac
  >- (
    pop_assum mp_tac
    >> rewrite_tac[GSYM EL,EL_APPEND_EQN]
    >> fs[]
  )
  >> strip_tac
  >> fs[EVERY_MAP,EVERY_APPEND,step_invariant]
  >> first_x_assum $ drule_all_then irule
QED

Theorem step_execution_step_invariant:
  !R P ls.
  step_execution R ls
  /\ step_invariant R P
  /\ P $ FST $ HD ls
  ==> step_execution (λs l s'. R s l s' /\ P s /\ P s') ls
Proof
  fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ntac 2 gen_tac
  >> ho_match_mp_tac step_execution_strongind
  >> conj_tac
  >- (
    rw[step_invariant,Once step_execution_cases]
    >> first_x_assum $ drule_all_then irule
  )
  >> PURE_REWRITE_TAC[AND_IMP_INTRO]
  >> rpt gen_tac >> strip_tac
  >> first_x_assum drule
  >> impl_keep_tac
  >- (
    pop_assum mp_tac
    >> rewrite_tac[GSYM EL,EL_APPEND_EQN]
    >> fs[]
  )
  >> drule_all_then strip_assume_tac step_execution_EVERY_step_invariant
  >> strip_tac
  >> drule step_execution_append_one
  >> fs[]
  >> disch_then drule
  >> REWRITE_TAC[GSYM APPEND_ASSOC,APPEND]
  >> disch_then match_mp_tac
  >> fs[AND_IMP_INTRO,step_invariant]
  >> first_x_assum $ drule_all_then irule
QED

(* properties for proving preservation *)

Theorem step_execution_RSUBSET_EVERY:
  !R ls P. step_execution R ls
  /\ (λs s'. ?l. R s l s') RSUBSET P
  ==> EVERY (λ(s,l,s'). P s s') ls
Proof
  rpt strip_tac
  >> drule step_execution_EVERY
  >> ho_match_mp_tac $ Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC
  >> fs[relationTheory.RSUBSET,PULL_EXISTS,LAMBDA_PROD,FORALL_PROD]
  >> rpt strip_tac
  >> first_x_assum $ drule_then irule
QED

Theorem step_execution_RSUBSET:
  !R P ls.
  step_execution R ls
  /\ (λs s'. ?l. R s l s') RSUBSET P
  /\ transitive P
  ==> !i j. i < j /\ j < LENGTH ls ==> P (FST $ EL i ls) (FST $ EL j ls)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac
  >> Induct_on `j - i`
  >> fs[arithmeticTheory.SUB_RIGHT_EQ]
  >> rpt strip_tac
  >> drule_then (qspec_then `i + v` mp_tac) $ GSYM step_execution_conseq_eq_state
  >> fs[arithmeticTheory.ADD_CLAUSES]
  >> disch_then kall_tac
  >> drule step_execution_EVERY
  >> fs[EVERY_MEM,ELIM_UNCURRY]
  >> `i + v < LENGTH ls` by fs[]
  >> drule_then assume_tac rich_listTheory.EL_MEM
  >> disch_then $ drule_then assume_tac
  >> fs[RSUBSET,PULL_EXISTS]
  >> Cases_on `v = 0`
  >- (fs[] >> first_x_assum $ drule_then irule)
  >> qhdtm_x_assum `transitive` $ irule o REWRITE_RULE[transitive_def]
  >> first_x_assum $ irule_at $ Pos $ el 1
  >> first_x_assum $ drule_then $ irule_at Any
  >> fs[]
QED

(*
 * refinement theorem to show:
 * s -> s' ==> ref P R s s'
 * where P is the refinement relation and R is the abstract transition relation
 *)
Definition ref_def:
  ref P R s s' =
    !as. P s as ==> ?as'. RC R as as' /\ P s' as'
End

(* R' refines R under refinement relation P *)
Definition refinement_def:
  refinement R R' P = !s s'. R s s' ==> ref P R' s s'
End

Theorem refinement_step_execution_EVERY_ref:
  !R ls R' P. refinement (λs s'. ?l. R s l s') R' P
  /\ step_execution R ls
  ==> EVERY (λ(s,l,s'). ref P R' s s') ls
Proof
  rpt strip_tac
  >> dxrule_then ho_match_mp_tac step_execution_RSUBSET_EVERY
  >> rw[relationTheory.RSUBSET,PULL_EXISTS]
  >> fs[refinement_def,PULL_EXISTS]
  >> first_x_assum $ dxrule_then irule
QED

Theorem refinement_step_execution_EVERY_rel:
  !R ls R' P as. step_execution R ls
  /\ refinement (λs s'. ?l. R s l s') R' P
  /\ P (FST $ HD ls) as
  ==> EVERY (λ(s,l,s'). ?as. P s as) ls
Proof
  fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> gen_tac
  >> ho_match_mp_tac step_execution_strongind
  >> conj_tac
  >- (rw[] >> goal_assum drule)
  >> PURE_REWRITE_TAC[AND_IMP_INTRO]
  >> rpt gen_tac >> strip_tac
  >> fs[AND_IMP_INTRO,PULL_FORALL]
  >> rpt gen_tac >> strip_tac
  >> qmatch_asmsub_rename_tac `P _ as`
  >> first_x_assum $ drule_then $ qspec_then `as` mp_tac
  >> impl_tac
  >- (
    pop_assum mp_tac
    >> rewrite_tac[GSYM EL,EL_APPEND_EQN]
    >> fs[]
  )
  >> strip_tac
  >> Cases_on `NULL e`
  >- (
    fs[NULL_EQ,step_execution_singleton,refinement_def,PULL_EXISTS,ref_def]
    >> first_x_assum $ drule_all_then strip_assume_tac
    >> rpt $ goal_assum drule
  )
  >> drule_all_then strip_assume_tac step_execution_append_end_eq_state
  >> fs[refinement_def,EVERY_MAP,EVERY_APPEND,PULL_EXISTS,ref_def,PULL_FORALL,AND_IMP_INTRO,EL_APPEND_EQN,COND_RATOR,COND_RAND,COND_EXPAND_IMP,IMP_CONJ_THM]
  >> first_x_assum $ drule_all_then strip_assume_tac
  >> rpt $ goal_assum drule
QED

Theorem refinement_RTC:
  !R R' P. refinement R R' P ==> refinement (RTC R) (RTC R') P
Proof
  rpt strip_tac
  >> simp[refinement_def]
  >> ho_match_mp_tac RTC_INDUCT_RIGHT1
  >> conj_tac
  >- (
    rw[refinement_def,ref_def,RC_RTC_EQ]
    >> irule_at Any relationTheory.RTC_REFL
    >> asm_rewrite_tac[]
  )
  >> fs[refinement_def,ref_def,RC_RTC_EQ]
  >> rw[]
  >> rpt $ first_x_assum $ drule_then strip_assume_tac
  >> simp[Once RTC_CASES_RTC_TWICE,PULL_EXISTS,AC CONJ_ASSOC CONJ_COMM]
  >> rpt $ goal_assum drule
  >> fs[relationTheory.RC_RTC]
QED

Theorem refinement_composition:
  !R R' P' R'' P''.
    refinement R R' P' /\ refinement R' R'' P''
    ==> refinement R R'' (λs as. ?bs.  P' s bs /\ P'' bs as)
Proof
  rw[refinement_def]
  >> first_x_assum $ drule_then assume_tac
  >> fs[ref_def]
  >> rw[]
  >> first_x_assum $ drule_then strip_assume_tac
  >> dxrule_then strip_assume_tac $ iffLR RC_DEF
  >> gvs[PULL_EXISTS]
  >- (
    irule_at Any RC_REFL
    >> goal_assum drule_all
  )
  >> first_x_assum $ drule_all_then strip_assume_tac
  >> rpt $ goal_assum $ drule_at Any
QED

val _ = export_theory ();
