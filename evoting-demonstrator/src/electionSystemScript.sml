open HolKernel boolLib Parse bossLib BasicProvers
open relationTheory listTheory rich_listTheory arithmeticTheory
     formatTheory electionTheory systemTheory finite_mapTheory
     executionTheory

val _ = new_theory "electionSystem";

(* by lift_imp_disj *)
Theorem IMP_DISJ_EQ:
  (A ==> B \/ C) = ((A ==> B) \/ (A ==> C))
Proof
  fs[]
QED

Triviality PERM_APPENDs:
  (PERM A B ==> ~(PERM A (B ++ [x])))
  /\ (PERM A B ==> ~(PERM A ([x] ++ B)))
Proof
  rpt strip_tac
  >> imp_res_tac sortingTheory.PERM_LENGTH
  >> fs[]
QED

Theorem RC_RTC_EQ:
  !R. RC (RTC R) = RTC R
Proof
  rw[relationTheory.RC_DEF,FUN_EQ_THM,EQ_IMP_THM]
  >> fs[RTC_REFL]
QED

(*
 * refinement:
 * the concrete system implements an election
 *)

Definition ref_crypt_assum_def:
  ref_crypt_assum
    (vote_format :word8 list enc_data -> contestant enc_data -> voter option)
    (decrypt :contestant enc_data -> contestant)
    (participating :contestant -> bool)
  <=>
    !x enc_vote. IS_SOME (vote_format x enc_vote)
    ==> decrypt enc_vote IN participating
End

Definition sys_elect_ref1_def:
  sys_elect_ref1 decrypt
    (vote_format :word8 list enc_data -> contestant enc_data -> voter option)
    s as <=>
    s.vcs.phase <> Init
    /\ (s.vcs.phase = Voting <=> as.state.active)
    /\ (s.vcs.phase = Ended <=> ~as.state.active)
    /\ as.state.voted = s.vcs.voted
    /\ PERM as.state.votes $ MAP decrypt s.vcs.votes
    /\ as.state.eligible = s.vcs.eligible
    /\ ref_crypt_assum vote_format decrypt as.state.participating
    /\ (!request_id sign enc_vote.
      MEM (request_id,sign,enc_vote) s.vcs.in_msgs
      /\ IS_SOME (vote_format sign enc_vote)
      /\ THE $ vote_format sign enc_vote NOTIN s.vcs.voted
      ==> ?voter. MEM (<| voter := voter; contestant:= decrypt $ enc_vote |>) as.ballots
        /\ voter = THE $ vote_format sign enc_vote)
End

Theorem sys_elect_ref1_init:
  !vote_format decrypt participating eligible.
  ref_crypt_assum vote_format decrypt participating
  ==>
  sys_elect_ref1 decrypt vote_format (init with <|
      vcs updated_by (λx. x with <| phase := Voting; eligible := eligible |>)
  |>)
    $ ballot_box_init participating eligible
Proof
  fs[init_def,ballot_box_init_def,vcsStateTheory.vcsStateInit_def,sys_elect_ref1_def,system_component_equality,election_component_equality]
QED

Theorem sys_elect_ref1_upd:
     sys_elect_ref1 d v (s with mixnet := _) as     = sys_elect_ref1 d v s as
  /\ sys_elect_ref1 d v (s with sigservice := _) as = sys_elect_ref1 d v s as
  /\ sys_elect_ref1 d v (s with cdn := _) as        = sys_elect_ref1 d v s as
Proof
  fs[sys_elect_ref1_def]
QED

(*

systemTheory.system_transition_cases
|> iffRL
|> SIMP_RULE (srw_ss() ++ DNF_ss) [IMP_CONJ_THM]
|> cj 6
|> SIMP_RULE (srw_ss() ++ CONJ_ss ++DNF_ss) [clientStateTheory.set_enc_vote_def,clientStateTheory.set_vote_def,clientStateTheory.update_client_def,COND_RAND,COND_RATOR,LET_THM,optionTheory.IS_SOME_EXISTS]
|> SIMP_RULE (srw_ss() ++ CONJ_ss ++DNF_ss) [clientStateTheory.client_vote_def,clientStateTheory.client_enc_vote_def,FLOOKUP_UPDATE]

*)

Theorem active_simps:
  (process_ballot b as).active = as.active
  /\ (send_ballot v c as').state.active = as'.state.active
  /\ (receive_ballot b as').state.active = as'.state.active
Proof
  fs[process_ballot_def,COND_RATOR,COND_RAND,send_ballot_def,receive_ballot_def]
QED

Theorem election_refinement1:
  !c c' s tm s' as decrypt vote_format.
  system$system_transition c c' s tm s'
  /\ vote_format = FST $ SND $ SND c'
  /\ sys_elect_ref1 decrypt vote_format s as
  ==> ?as'.
    RC election$system_transition as as'
    /\ sys_elect_ref1 decrypt vote_format s' as'
Proof
  fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL,RC_DEF,systemTheory.system_transition_cases]
  >> rpt strip_tac
  >> dsimp[state_component_equality,sys_elect_ref1_upd]
  >> gvs[]
  >~ [`stow_vote (request_id,sign,enc_vote)`]
  >- (
    dsimp[electionTheory.system_transition_cases]
    >> disj2_tac >> disj1_tac
    >> fs[sys_elect_ref1_def,vcsStateTheory.stow_vote_def,send_ballot_def]
    >> asm_rewrite_tac[]
    >> dsimp[EXISTS_OR_THM]
    >> qmatch_goalsub_rename_tac `THE $ vote_format sign enc_vote`
    >> qexists `THE $ vote_format sign enc_vote`
    >> dsimp[DISJ_IMP_THM,LEFT_AND_OVER_OR]
    >> asm_rewrite_tac[IMP_DISJ_EQ]
    >> dsimp[EXISTS_OR_THM]
  )
  >~ [`start_voting _ _ = SOME _`]
  >- gvs[sys_elect_ref1_def,vcsStateTheory.start_voting_def]
  >~ [`update_client_result s.clients m = SOME clients'`]
  >- (
    disj1_tac
    >>
    gvs[clientStateTheory.update_client_result_def,vcsStateTheory.vcs_send_response_def,sys_elect_ref1_def]
    >> every_case_tac
    >> gvs[clientStateTheory.update_client_def,finite_mapTheory.FLOOKUP_UPDATE,COND_RAND,COND_RATOR,optionTheory.IS_SOME_EXISTS]
    >> asm_rewrite_tac[]
    >> qmatch_asmsub_rename_tac `ballot_voter m` >> Cases_on `m`
    >> fs[formatTheory.ballot_voter_def,COND_EXPAND_OR,FORALL_AND_THM,DISJ_IMP_THM,PULL_EXISTS]
  )
  >~ [`end_voting s.vcs = SOME vcs'`]
  >- (
    gvs[sys_elect_ref1_def,vcsStateTheory.end_voting_def]
    >> dsimp[electionTheory.system_transition_cases,sys_elect_ref1_def,electionTheory.end_election_def,electionTheory.deactivate_def]
    >> asm_rewrite_tac[]
  )
  >~ [`set_vote _ voter vote = SOME _`]
  >- (
    disj1_tac
    >> fs[sys_elect_ref1_def]
    >> asm_rewrite_tac[]
  )
(*
  >- (
    (* insert vote into  *)
    gvs[clientStateTheory.set_vote_def,clientStateTheory.update_client_def,optionTheory.IS_SOME_EXISTS,clientStateTheory.client_vote_def,clientStateTheory.set_enc_vote_def,FLOOKUP_UPDATE,clientStateTheory.client_enc_vote_def]
    >> disj2_tac
    >> fs[sys_elect_ref1_def]
    >> dsimp[electionTheory.system_transition_cases,send_ballot_def,AC CONJ_ASSOC CONJ_COMM]
    >> disj1_tac
    >> asm_rewrite_tac[]
    >> fs[GSYM PULL_EXISTS]
    >> disj2_tac >> disj1_tac
    >> asm_rewrite_tac[]
    >> dsimp[FLOOKUP_UPDATE,COND_RAND,COND_RATOR,COND_EXPAND_OR,PULL_EXISTS]
  )
*)
  >~ [`update_contestants _ voter contestants = SOME clients'`]
  >- (
    disj1_tac
    >>
    gvs[clientStateTheory.update_contestants_def,clientStateTheory.update_client_def,optionTheory.IS_SOME_EXISTS,clientStateTheory.client_set_contestants_def,sys_elect_ref1_def,finite_mapTheory.FLOOKUP_UPDATE,COND_RAND,COND_RATOR,COND_EXPAND_OR,PULL_EXISTS]
    >> asm_rewrite_tac[]
  )
  >~ [`process_vote auth_check vote_format serialise_abs_vote (sign,enc_vote,request_id)`]
  >- (
    fs[sys_elect_ref1_def,vcsStateTheory.process_vote_def]
    >> rpt IF_CASES_TAC
    >> dsimp[vcsStateTheory.send_msg_def]
    >> gvs[FORALL_AND_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM]
    >> asm_rewrite_tac[]
    >> disj2_tac
    >> dsimp[electionTheory.system_transition_cases,active_simps,end_election_def,deactivate_def,receive_ballot_def]
    >> rpt disj2_tac
    >> fs[process_ballot_def]
    >> rename1 `vote_format sign enc_vote` >> Cases_on `vote_format sign enc_vote`
    >> fs[optionTheory.IS_SOME_EXISTS,PULL_EXISTS,ref_crypt_assum_def]
    >> first_x_assum (fn thm =>
      drule_all_then assume_tac thm >> mp_tac thm)
    >> gs[]
    >> rpt strip_tac
    >> goal_assum drule
    >> fs[voting_ok_def]
    >> qmatch_goalsub_abbrev_tac `COND c` >> `c` by fs[IN_DEF]
    >> fs[process_ballot_def,SNOC_APPEND,sortingTheory.PERM_TO_APPEND_SIMPS,MEM_FILTER]
    >> asm_rewrite_tac[]
    >> full_simp_tac (std_ss ++ CONJ_ss) []
    >> rpt strip_tac
    >> first_x_assum $ drule_all_then irule
  )
QED

Theorem refinement_system_transitions:
  !decrypt c c'. refinement
    (λs s'. ?tm. system_transition c c' s tm s')
    election$system_transition
    (sys_elect_ref1 decrypt $ FST $ SND $ SND c')
Proof
  rw[refinement_def,ref_def]
  >> drule_at Any election_refinement1
  >> disch_then $ drule_at_then Any assume_tac
  >> CONV_TAC $ DEPTH_CONV ETA_CONV
  >> fs[SF SatisfySimps.SATISFY_ss]
QED

Theorem election_refinement1_RTC:
  !c c' s s' as decrypt vote_format.
  RTC (λs s'. ?tm. system$system_transition c c' s tm s') s s'
  /\ vote_format = FST $ SND $ SND c'
  /\ sys_elect_ref1 decrypt vote_format s as
  ==> ?as'.
    RTC election$system_transition as as'
    /\ sys_elect_ref1 decrypt vote_format s' as'
Proof
  rpt strip_tac
  >> qmatch_asmsub_rename_tac `sys_elect_ref1 decrypt vote_format s as`
  >> qmatch_asmsub_rename_tac `system_transition c c'`
  >> qspecl_then [`decrypt`,`c`,`c'`] assume_tac refinement_system_transitions
  >> dxrule_then assume_tac refinement_RTC
  >> gvs[refinement_def,ref_def]
  >> first_x_assum dxrule_all
  >> CONV_TAC $ DEPTH_CONV ETA_CONV
  >> rw[RC_RTC_EQ]
QED

Theorem system_transition_RTC_inv:
  !c c' s s' as decrypt vote_format eligible participating.
  RTC (λs s'. ?tm. system$system_transition c c' s tm s') s s'
  /\ ref_crypt_assum vote_format decrypt participating
  /\ vote_format = FST $ SND $ SND c'
  /\ s = init with <| vcs updated_by (λx. x with <| phase := Voting; eligible := eligible |>) |>
  ==>
    s.vcs.eligible = s'.vcs.eligible
    /\ s.vcs.eligible = eligible
    /\ (!v. v IN s'.vcs.voted ==> s'.vcs.eligible v)
    /\ CARD s'.vcs.voted = LENGTH s'.vcs.votes
Proof
  rpt gen_tac >> strip_tac
  >> drule_then (qspec_then `eligible` assume_tac) sys_elect_ref1_init
  >> gvs[]
  >> drule_then (drule_at_then Any assume_tac) election_refinement1_RTC
  >> fs[]
  >> drule system_transition_RTC_invariant
  >> drule system_transition_RTC_monotonic
  >> simp[invariant_init,ballot_box_init_def,election_preserving_def]
  >> ntac 2 strip_tac
  >> gs[sys_elect_ref1_def,invariant_def,valid_election_def]
  >> drule sortingTheory.PERM_LENGTH
  >> fs[]
QED

(* instance of refinement_step_execution_EVERY_ref *)
Theorem election_refinement1_step_execution:
  !ls c c' decrypt vote_format.
  step_execution (system$system_transition c c') ls
  /\ vote_format = FST $ SND $ SND c'
  ==> EVERY (λ(s,l,s'). ref (λs as. sys_elect_ref1 decrypt vote_format s as) election$system_transition s s') ls
Proof
  rpt strip_tac
  >> dxrule_at_then Any irule refinement_step_execution_EVERY_ref
  >> qmatch_goalsub_rename_tac `sys_elect_ref1 decrypt vote_format`
  >> qmatch_goalsub_rename_tac `system_transition c c'`
  >> qspecl_then [`decrypt`,`c`,`c'`] mp_tac refinement_system_transitions
  >> CONV_TAC $ DEPTH_CONV ETA_CONV
  >> fs[]
QED

(* instance of refinement_step_execution_EVERY_rel *)
Theorem election_refinement1_step_execution':
  !c c' s decrypt vote_format ls.
  step_execution (system$system_transition c c') ls
  /\ ref_crypt_assum vote_format decrypt participating
  /\ vote_format = FST $ SND $ SND c'
  /\ s = FST $ EL 0 ls
  /\ s = (init with <| vcs updated_by (λx. x with <| phase := Voting; eligible := eligible |>) |>)
  ==> EVERY (λ(s,l,s'). ?as. sys_elect_ref1 decrypt vote_format s as) ls
Proof
  rpt strip_tac
  >> dxrule_at_then Any irule refinement_step_execution_EVERY_rel
  >> gvs[]
  >> irule_at Any refinement_system_transitions
  >> qmatch_asmsub_rename_tac `_ with <| eligible := eligible |>`
  >> drule_then (qspec_then `eligible` assume_tac) sys_elect_ref1_init
  >> gs[]
  >> goal_assum drule
QED

(* election guaranties *)

Theorem step_execution_system_transition_correct:
  step_execution (system_transition c c') tr
  /\ ref_crypt_assum vote_format decrypt participating
  /\ vote_format = FST $ SND $ SND c'
  /\ s = FST $ EL 0 tr
  /\ s = (init with <| vcs updated_by (λx. x with <| phase := Voting; eligible := eligible |>) |>)
  ==> EVERY (λ(s,l,s'). s.vcs.eligible = s'.vcs.eligible
      /\ (?nv. PERM (MAP decrypt s'.vcs.votes) (nv ++ MAP decrypt s.vcs.votes))
      /\ s.vcs.voted SUBSET s'.vcs.voted
      /\ (s.vcs.phase = Ended ==> s.vcs.voted = s'.vcs.voted
        /\ s.vcs.phase = s'.vcs.phase
        /\ PERM (MAP decrypt s.vcs.votes) (MAP decrypt s'.vcs.votes))
  ) tr
Proof
  rpt strip_tac
  >> drule election_refinement1_step_execution
  >> fs[]
  >> disch_then $ qspec_then `decrypt` mp_tac
  >> ho_match_mp_tac $ Ho_Rewrite.REWRITE_RULE[GSYM AND_IMP_INTRO] EVERY_MEM_MONO
  >> rpt gen_tac >> ntac 2 strip_tac
  >> fs[pairTheory.ELIM_UNCURRY,ref_def]
  >> drule_then (drule_then $ qspec_then `eligible` assume_tac) election_refinement1_step_execution'
  >> gs[EVERY_MEM]
  >> first_x_assum $ drule_then assume_tac
  >> fs[pairTheory.ELIM_UNCURRY]
  >> first_x_assum $ drule_then strip_assume_tac
  >> drule_then assume_tac system_transition_RC_monotonic
  >> gs[election_preserving_def,sys_elect_ref1_def,election_component_equality]
  >> conj_tac
  >> ntac 2 $ dxrule_then (assume_tac o GSYM) $ iffLR sortingTheory.PERM_EQUIVALENCE_ALT_DEF
  >- (
    gvs[IS_SUFFIX_APPEND]
    >> irule_at Any sortingTheory.PERM_CONG
    >> irule_at Any sortingTheory.PERM_REFL
    >> fs[]
    >> once_rewrite_tac[sortingTheory.PERM_SYM]
    >> fs[sortingTheory.PERM_REFL]
  )
  >> gs[sortingTheory.PERM_EQUIVALENCE_ALT_DEF]
QED

Theorem step_execution_system_transition_correct2:
  !tr c c'. step_execution (system_transition c c') tr
  /\ ref_crypt_assum vote_format decrypt participating
  /\ vote_format = FST $ SND $ SND c'
  /\ s = FST $ EL 0 tr
  /\ s = (init with <| vcs updated_by (λx. x with <| phase := Voting; eligible := eligible |>) |>)
  ==> EVERY (λ(s,l,s').
    (!v. v IN s'.vcs.voted ==> s'.vcs.eligible v)
    /\ CARD s'.vcs.voted = LENGTH s'.vcs.votes
  ) tr
Proof
  rpt strip_tac
  >> fs[EVERY_MEM,MEM_EL,pairTheory.ELIM_UNCURRY] >> gen_tac >> strip_tac
  >> qmatch_asmsub_rename_tac `EL n tr`
  >> drule_all_then assume_tac step_execution_RTC
  >> drule_then (qspec_then `eligible` assume_tac) sys_elect_ref1_init
  >> gvs[]
  >> dxrule_then (drule_at_then Any assume_tac) election_refinement1_RTC
  >> fs[]
  >> drule_then assume_tac system_transition_RTC_invariant
  >> fs[invariant_init]
  >> gvs[invariant_def,sys_elect_ref1_def,voting_ok_def,valid_election_def]
  >> imp_res_tac sortingTheory.PERM_LENGTH
  >> fs[]
QED

val _ = export_theory ();
