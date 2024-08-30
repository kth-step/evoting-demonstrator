(*
  Proof connecting both abstract and concrete execution
 *)

open HolKernel boolLib Parse bossLib;
open listTheory pairTheory combinTheory relationTheory optionTheory stringTheory wordsTheory
     mllistTheory
     executionTheory networkTheory formatTheory vcsStateTheory mixnetStateTheory
     byteTreeTheory
     systemTheory TevDNetworkedSystemTheory
     electionSystemTheory

val _ = new_theory "TevDNetworkedSystemProof";

Theorem PERM_inter_singlton_eq:
  PERM (a ++ [x] ++ b) (c ++ [x] ++ d) = PERM (a ++ b) (c ++ d)
Proof
  once_rewrite_tac[GSYM APPEND_ASSOC]
  >> once_rewrite_tac[GSYM rich_listTheory.CONS_APPEND]
  >> rewrite_tac[sortingTheory.PERM_FUN_APPEND_CONS]
  >> once_rewrite_tac[sortingTheory.PERM_SYM]
  >> rewrite_tac[sortingTheory.PERM_FUN_APPEND_CONS,sortingTheory.PERM_CONS_IFF,APPEND]
QED

Theorem sign_label_ineq:
  (!v. sign_label_to_entity v <> VCS)
  /\ (!v n. sign_label_to_entity v <> Client n)
  /\ (!v. sign_label_to_entity v <> Admin)
  /\ !v. sign_label_to_entity v <> MixNet
Proof
  rpt conj_tac >> Cases >> fs[sign_label_to_entity_def]
QED

Theorem netsys_net_handler_same_src_dst:
  !src dst log fns msg state lb d msgs.
  netsys_net_handler log fns dst src msg state = (lb,d,msgs) /\ src = dst
  ==> (lb,d,msgs) = ([],state,[])
Proof
  Cases >> csimp[]
  >> dsimp[netsys_net_handler_def,AllCaseEqs()]
QED

(* relation on vcs concrete and abstract messages from vcs to client/mixnet *)
Definition match_vcs_msg_def:
  match_vcs_msg cm am serialise_enc_vote <=>
    case (cm,am) of
    | (Msg_BallotRecorded request_id voter1, BallotRecorded request voter2) =>
      voter2 = voter1 /\ request_id = request
    | (Msg_BallotError request_id, BallotError request) => request_id = request
    | (Msg_Ballots data, SendVotes enc_vote_list) =>
        prepare_submission (MAP serialise_enc_vote enc_vote_list) = SOME data
    | _ => F
End

(* cryptographic assumptions *)
Definition crypt_assum_def:
  crypt_assum fns c <=>
  !(crypt : crypt_sign)
    (crypt_sign : contestant crypt)
    auth_check vote_format serialise_enc_vote
    (deserialise_enc_vote : word8 list -> contestant enc_data)
    (deserialise_sign : word8 list -> word8 list enc_data)
    (auth_check_cake : word8 list -> bool)
    (vote_format_cake : word8 list -> word8 list -> mlstring option).
    (* crypto functions *)
    c = (crypt,(crypt_sign,auth_check,vote_format,serialise_enc_vote),deserialise_enc_vote,deserialise_sign)
    /\ fns = (auth_check_cake,vote_format_cake,I)
    ==>
    (!sign enc_vote.
      vote_format (deserialise_sign sign) (deserialise_enc_vote enc_vote)
      = OPTION_MAP Voter $ vote_format_cake sign enc_vote
    )
    /\ (!sign. auth_check $ deserialise_sign sign = auth_check_cake sign)
    /\ (serialise_enc_vote o deserialise_enc_vote = I)
    /\ (deserialise_enc_vote o serialise_enc_vote = I)
End

(* independent of the abstract state *)
Definition network_step_inv_def:
  network_step_inv (cs : netsys_name -> netsys_data)
  <=>
    EVERY is_valid_bytetree (cs Name_VCS).vcs_state.votes
  /\ (IS_SOME (cs Name_MixNet).mixnet_ballots
    ==> prepare_submission (cs Name_VCS).vcs_state.votes
        = (cs Name_MixNet).mixnet_ballots)
  /\ (IS_SOME (cs Name_MixNet).mixnet_ballots
    ==> (cs Name_VCS).vcs_state.phase = Ended)
End

Definition pkgs_map_def:
  pkgs_map deserialise_sign deserialise_enc_vote x =
    if x.src = Name_Client /\ x.dst = Name_VCS then
      (case x.body of
        Msg_Ballot sign request_id enc_vote =>
      [(request_id,deserialise_sign sign,deserialise_enc_vote enc_vote)]
      | _ => [])
    else []
End

Definition non_ballot_pkg_def:
  non_ballot_pkg x <=>
   x.src <> Name_Client \/ x.dst <> Name_VCS \/ (!a b c. x.body <> Msg_Ballot a b c)
End

Theorem pkgs_map_NIL:
  pkgs_map f g x = [] <=> non_ballot_pkg x
Proof
  rw[pkgs_map_def,non_ballot_pkg_def,AllCaseEqs(),EQ_IMP_THM] >> gs[]
  >> Cases_on `x.body` >> fs[]
QED

Theorem pkgs_map_NIL_imp =
  REWRITE_RULE[non_ballot_pkg_def] $ iffRL pkgs_map_NIL

Theorem pkgs_map_same_NIL:
  !f g x. x.src = x.dst ==> pkgs_map f g x = []
Proof
  fs[pkgs_map_NIL,non_ballot_pkg_def]
QED

Theorem non_ballot_pkg_pkgs_map_NIL:
  !xs. EVERY non_ballot_pkg xs <=>
    !deserialise_sign deserialise_enc_vote.
    FLAT $ MAP (pkgs_map
      (deserialise_sign : word8 list -> word8 list enc_data)
      (deserialise_enc_vote : word8 list -> contestant enc_data)
    ) xs = []
Proof
  rw[FLAT_EQ_NIL,EVERY_MAP,EVERY_MEM,EQ_IMP_THM]
  >> first_x_assum drule
  >> fs[pkgs_map_NIL]
QED

(* refinement *)
Definition ref_rel_def:
  (* fns concrete crypto; c abstract crypto
   * cs concrete state; as abstract state *)
  ref_rel fns pkgs cs c as <=>
  !crypt crypt_sign auth_check vote_format serialise_enc_vote
    (deserialise_enc_vote : word8 list -> contestant enc_data)
    (deserialise_sign : word8 list -> word8 list enc_data)
    (auth_check_cake : word8 list -> bool)
    (vote_format_cake : word8 list -> word8 list -> mlstring option).
    (* crypto functions *)
    c = (crypt,(crypt_sign,auth_check,vote_format,serialise_enc_vote),deserialise_enc_vote,deserialise_sign)
    /\ fns = (auth_check_cake,vote_format_cake,I)
    ==>
    (cs Name_VCS).vcs_state.phase = as.vcs.phase
    /\ EVERY (λcm. ?am. MEM am as.vcs.out_msg
          /\ match_vcs_msg cm am serialise_enc_vote)
        (cs Name_VCS).vcs_state.out_msg
    (* already voted *)
    /\ as.vcs.voted = set (cs Name_VCS).vcs_state.voted
    (* same eligibility *)
    /\ as.vcs.eligible = set (cs Name_VCS).vcs_state.eligible
    (* msg ballots are only sent after the voting has ended and have certain bytetree shape *)
    /\ EVERY (λx. !votes_data. x = create_packet Name_VCS Name_MixNet (Msg_Ballots votes_data)
      ==> (cs Name_VCS).vcs_state.phase = Ended /\ prepare_submission (cs Name_VCS).vcs_state.votes = SOME votes_data) pkgs
    /\ (IS_SOME as.mixnet.enc_votes = IS_SOME (cs Name_MixNet).mixnet_ballots)
    /\ (IS_SOME as.mixnet.enc_votes ==>
      MAP serialise_enc_vote $ THE as.mixnet.enc_votes = (cs Name_VCS).vcs_state.votes)
    /\ (cs Name_VCS).vcs_state.votes = MAP serialise_enc_vote as.vcs.votes
    (* invariants *)
    /\ network_step_inv cs
    /\ ALL_DISTINCT (cs Name_VCS).vcs_state.voted
    /\ PERM (FLAT $ MAP (pkgs_map deserialise_sign deserialise_enc_vote) pkgs) as.vcs.in_msgs
(*
    /\ EVERY (pkgs_subset_in_msgs deserialise_sign deserialise_enc_vote as.vcs.in_msgs) pkgs
    /\ EVERY (in_msgs_subset_pkgs deserialise_sign deserialise_enc_vote pkgs) as.vcs.in_msgs
    /\ ALL_DISTINCT $ MAP FST as.vcs.in_msgs
    /\ NULL (cs Name_MixNet).mixnet_ballots = NULL as.mixnet.enc_votes
    /\ (!sign enc_vote. IS_SOME $ vote_format_cake sign enc_vote ==> is_valid_bytetree enc_vote)
*)
End

Definition ref_rel_init_def:
  ref_rel_init eligible =
    network_init (λn. netsys_init n with <| vcs_state updated_by (λx.
        x with <| eligible := SET_TO_LIST eligible ; phase := Voting |>) |>)
End

Theorem ref_rel_init_thm:
  !eligible net s fns deserialise_enc_vote deserialise_sign c c'.
  FINITE eligible
  /\ net = ref_rel_init eligible
  /\ s = init with <| vcs updated_by (λx. x with <| phase := Voting; eligible := eligible |>) |>
  ==> ref_rel fns net.packets net.state (c,c',deserialise_enc_vote,deserialise_sign) s
Proof
  dsimp[network_init_def,ref_rel_def,init_def,vcsStateInit_def,netsys_init_def,vcs_state_cake_init_def,ref_rel_init_def]
  >> fs[network_step_inv_def,optionTheory.IS_SOME_EXISTS,mixnetStateInit_def,SET_TO_LIST_INV]
QED

Theorem ref_rel_append:
  !fns fns' net_st s xs zs ys.
  ref_rel fns (xs ++ zs ++ ys) net_st fns' s
  /\ EVERY non_ballot_pkg zs
  ==> ref_rel fns (xs ++ ys) net_st fns' s
Proof
  ntac 2 PairCases >> rpt strip_tac
  >> gs[ref_rel_def,create_packet_def,non_ballot_pkg_pkgs_map_NIL]
  >> rpt strip_tac
  >> gs[]
QED

Theorem network_step_system_transition_refinement:
  !net lb net' c c' s fns deserialise_enc_vote deserialise_sign.
  network_step (netsys_net_handling fns) (netsys_input_handling fns) net lb net'
  /\ ref_rel fns net.packets net.state (c,c',deserialise_enc_vote,deserialise_sign) s
  /\ fns = (_,_,I)
  /\ crypt_assum fns (c,c',deserialise_enc_vote,deserialise_sign)
  ==> ?s'.
    ref_rel fns net'.packets net'.state (c,c',deserialise_enc_vote,deserialise_sign) s'
    /\ RC (λs s'. ?lbl. system_transition c c' s lbl s') s s'
Proof
  fs[network_step_cases]
  >> csimp[netsys_net_handling_def,netsys_input_handling_def,netsys_input_handler_def,netsys_net_handler_def,RC_DEF]
  >> rpt gen_tac >> strip_tac
  >> qmatch_asmsub_abbrev_tac `ref_rel fns` >> PairCases_on `fns`
  >> unabbrev_all_tac
  >> qmatch_asmsub_rename_tac `ref_rel (auth_check_cake,vote_format_cake,I)`
  >> qmatch_goalsub_rename_tac `system_transition c c'` >> PairCases_on `c'`
  >> qmatch_goalsub_rename_tac `system_transition c (contestant_crypt,auth_format,vote_format,serialise_abs_vote)`
  >~ [`netsys_input_handler log _ h inp (net.state h) id = (lb,d,msgs)`]
  >- (
    (* input handlers are state-less *)
    Cases_on `h` >> dsimp[]
    >> gvs[NULL_EQ,netsys_input_handler_def,AllCaseEqs(),combinTheory.APPLY_UPDATE_ID,send_packets_def,serialise_netsys_output_def]
    >> fs[ref_rel_def,crypt_assum_def,network_step_inv_def]
    >> dsimp[create_packet_def,pkgs_map_same_NIL]
    >> fs[pkgs_map_NIL_imp]
    >> rpt $ strip_tac
    >> gs[]
    >> disj2_tac
    >> irule_at Any $ cj 8 system_transition_rules
    >> fs[pairTheory.ELIM_UNCURRY,stow_vote_def,pkgs_map_def]
    >> irule_at Any sortingTheory.PERM_MONO
    >> fs[]
  )
  >~ [`netsys_net_handler log _ p.dst p.src p.body (net.state p.dst) = (lb,d,msgs)`]
  >> Cases_on `p.src = p.dst`
  >- (
    drule_all_then assume_tac netsys_net_handler_same_src_dst
    >> fs[netsys_net_handler_def,send_packets_def]
    >> dsimp[]
    >> disj1_tac
    >> gs[ref_rel_def,crypt_assum_def,network_step_inv_def,combinTheory.APPLY_UPDATE_ID,create_packet_def,packet_component_equality,pkgs_map_same_NIL]
  )
  >> dsimp[]
  >> gvs[] >> drule ref_rel_append >> fs[non_ballot_pkg_def]
  >> Cases_on `p.dst` >> Cases_on `p.src`
  >> gvs[NULL_EQ,netsys_net_handler_def,AllCaseEqs(),send_packets_nil,combinTheory.APPLY_UPDATE_ID]
  (* 7 subgoals *)
  (* client node is state-less *)
  >~ [`p.dst = Name_Client`,`p.src = Name_VCS`,`Msg_BallotRecorded request_id voter`]
  >- (
    dsimp[combinTheory.APPLY_UPDATE_ID,send_packets_def,serialise_netsys_output_def]
    >> fs[ref_rel_def,crypt_assum_def,network_step_inv_def]
    >> dsimp[create_packet_def,pkgs_map_NIL_imp]
  )
  >~ [`p.dst = Name_Client`,`p.src = Name_VCS`,`Output_BallotError request_id`]
  >- (
    dsimp[combinTheory.APPLY_UPDATE_ID,send_packets_def,serialise_netsys_output_def]
    >> fs[ref_rel_def,crypt_assum_def,network_step_inv_def]
    >> dsimp[create_packet_def,pkgs_map_NIL_imp]
  )
  >~ [`p.dst = Name_VCS`,`p.src = Name_Admin`,`start_voting_cake`,`Msg_VotingStart vl`]
  >- (
    strip_tac
    >> dsimp[] >> disj2_tac
    >> fs[Once SWAP_EXISTS_THM]
    >> qexists_tac `(VCS,AdminMsg $ VotingStart vl)`
    >> dsimp[system_transition_cases,sign_label_ineq]
    >> gvs[start_voting_def,start_voting_cake_def,ref_rel_def,crypt_assum_def,network_step_inv_def,combinTheory.APPLY_UPDATE_THM,send_packets_def]
  )
  >~ [`p.dst = Name_VCS`,`p.src = Name_Admin`,`prepare_submission _ = NONE`]
  >- (
    disch_then kall_tac
    >> dxrule_then strip_assume_tac $ iffLR ref_rel_def
    >> gvs[end_voting_cake_def,crypt_assum_def,network_step_inv_def]
    >> drule prepare_submission_thm
    >> fs[]
  )
  >~ [`p.dst = Name_VCS`,`p.src = Name_Admin`,`end_voting_cake`,`prepare_submission _ = SOME _`]
  >- (
    strip_tac
    >> dsimp[] >> disj2_tac
    >> fs[Once SWAP_EXISTS_THM]
    >> qexists_tac `(VCS,AdminMsg VotingEnd)`
    >> dsimp[system_transition_cases,sign_label_ineq]
    >> gvs[end_voting_cake_def,end_voting_def,ref_rel_def,crypt_assum_def,network_step_inv_def,combinTheory.APPLY_UPDATE_THM,set_enc_votes_def,mixnetStateInit_def,send_packets_def]
    >> dsimp[create_packet_def,serialise_netsys_output_def,pkgs_map_NIL_imp]
    >> fs[create_packet_def,GSYM EXISTS_OR_THM,EVERY_MEM]
  )
  >~ [`p.dst = Name_MixNet`,`p.src = Name_VCS`,`net.state Name_MixNet`]
  >- (
    strip_tac
    >> disj2_tac
    >> ntac 2 $ dxrule_then strip_assume_tac $ iffLR ref_rel_def
    >> simp[Once SWAP_EXISTS_THM]
    >> Q.REFINE_EXISTS_TAC `(MixNet,VCSMsg $ SendVotes _)`
    >> gvs[create_packet_def,packet_component_equality,ref_rel_def,crypt_assum_def,network_step_inv_def,combinTheory.APPLY_UPDATE_THM,set_enc_votes_def,mixnetStateInit_def,pkgs_map_NIL_imp]
    >> dsimp[system_transition_cases,set_enc_votes_def,mixnetStateInit_def]
  )
  >~ [`p.dst = Name_VCS`,`p.src = Name_Client`,`process_vote_cake log _`]
  >> qmatch_asmsub_rename_tac `process_vote_cake log (auth_check_cake,vote_format_cake,I) (sign,enc_vote,request_id)`
  >> fs[RIGHT_OR_EXISTS_THM,LEFT_OR_EXISTS_THM,Once SWAP_EXISTS_THM]
  >> Q.REFINE_EXISTS_TAC `(VCS,Tau)`
  >> gvs[process_vote_cake_def,AllCaseEqs(),system_transition_cases,sign_label_ineq,PULL_EXISTS,pop_out_msgs_cake_def,combinTheory.APPLY_UPDATE_THM,send_msg_cake_def]
  >> rpt BasicProvers.TOP_CASE_TAC
  >> gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def]
  >> fs[SNOC_APPEND]
  >~ [`s.vcs.phase <> Voting`]
  >- (
    gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def,stow_vote_def,o_DEF,pkgs_map_NIL_imp]
    >> dsimp[]
    >> Cases_on `p.body` >> fs[pkgs_map_NIL_imp]
    >> qmatch_asmsub_rename_tac `Msg_Ballot sign' req_id enc_vote'`
    >> disj2_tac
    >> fs[pkgs_map_def]
    >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] sortingTheory.PERM_MEM_EQ
    >> fs[FORALL_AND_THM,DISJ_IMP_THM]
    >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
    >> pop_assum $ assume_tac o REWRITE_RULE[Once rich_listTheory.CONS_APPEND,Once APPEND_ASSOC]
    >> goal_assum $ drule_at Any
    >> qhdtm_x_assum `PERM` mp_tac
    >> fs[PERM_inter_singlton_eq]
  )
  >~ [`(net.state Name_VCS).vcs_state.phase = Voting`,`vote_format_cake sign enc_vote = NONE`]
  >- (
    gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def,pkgs_map_NIL_imp]
    >> Cases_on `p.body` >> fs[pkgs_map_NIL_imp]
    >> qmatch_asmsub_rename_tac `Msg_Ballot sign' req_id enc_vote'`
    >> dsimp[] >> disj2_tac
    >> fs[pkgs_map_def]
    >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] sortingTheory.PERM_MEM_EQ
    >> fs[FORALL_AND_THM,DISJ_IMP_THM]
    >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
    >> pop_assum $ assume_tac o REWRITE_RULE[Once rich_listTheory.CONS_APPEND,Once APPEND_ASSOC]
    >> goal_assum $ drule_at Any
    >> fs[PERM_inter_singlton_eq,process_vote_def,send_msg_def]
  )
  >~ [`(net.state Name_VCS).vcs_state.phase = Voting`,`~is_valid_bytetree enc_vote`]
  >- (
    gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def,pkgs_map_NIL_imp]
    >> Cases_on `p.body` >> fs[pkgs_map_NIL_imp]
    >> qmatch_asmsub_rename_tac `Msg_Ballot sign' req_id enc_vote'`
    >> dsimp[] >> disj2_tac
    >> fs[pkgs_map_def]
    >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] sortingTheory.PERM_MEM_EQ
    >> fs[FORALL_AND_THM,DISJ_IMP_THM]
    >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
    >> pop_assum $ assume_tac o REWRITE_RULE[Once rich_listTheory.CONS_APPEND,Once APPEND_ASSOC]
    >> goal_assum $ drule_at Any
    >> fs[PERM_inter_singlton_eq,process_vote_def,send_msg_def]
    >> fs[o_DEF,FUN_EQ_THM]
  )
  >~ [`(net.state Name_VCS).vcs_state.phase = Voting`,`~auth_check_cake sign`]
  >- (
    gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def,pkgs_map_NIL_imp]
    >> Cases_on `p.body` >> fs[pkgs_map_NIL_imp]
    >> qmatch_asmsub_rename_tac `Msg_Ballot sign' req_id enc_vote'`
    >> dsimp[] >> disj2_tac
    >> fs[pkgs_map_def]
    >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] sortingTheory.PERM_MEM_EQ
    >> fs[FORALL_AND_THM,DISJ_IMP_THM]
    >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
    >> pop_assum $ assume_tac o REWRITE_RULE[Once rich_listTheory.CONS_APPEND,Once APPEND_ASSOC]
    >> goal_assum $ drule_at Any
    >> fs[PERM_inter_singlton_eq,process_vote_def,send_msg_def]
    >> fs[o_DEF,FUN_EQ_THM]
  )
  >~ [`(net.state Name_VCS).vcs_state.phase = Voting`,`~MEM (Voter x) (net.state Name_VCS).vcs_state.eligible`]
  >- (
    gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def,pkgs_map_NIL_imp]
    >> Cases_on `p.body` >> fs[pkgs_map_NIL_imp]
    >> qmatch_asmsub_rename_tac `Msg_Ballot sign' req_id enc_vote'`
    >> dsimp[] >> disj2_tac
    >> fs[pkgs_map_def]
    >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] sortingTheory.PERM_MEM_EQ
    >> fs[FORALL_AND_THM,DISJ_IMP_THM]
    >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
    >> pop_assum $ assume_tac o REWRITE_RULE[Once rich_listTheory.CONS_APPEND,Once APPEND_ASSOC]
    >> goal_assum $ drule_at Any
    >> fs[PERM_inter_singlton_eq,process_vote_def,send_msg_def]
    >> fs[o_DEF,FUN_EQ_THM]
  )
  >~ [`(net.state Name_VCS).vcs_state.phase = Voting`,`MEM (Voter x) (net.state Name_VCS).vcs_state.voted`]
  >- (
    gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def,pkgs_map_NIL_imp]
    >> Cases_on `p.body` >> fs[pkgs_map_NIL_imp]
    >> qmatch_asmsub_rename_tac `Msg_Ballot sign' req_id enc_vote'`
    >> dsimp[] >> disj2_tac
    >> fs[pkgs_map_def]
    >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] sortingTheory.PERM_MEM_EQ
    >> fs[FORALL_AND_THM,DISJ_IMP_THM]
    >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
    >> pop_assum $ assume_tac o REWRITE_RULE[Once rich_listTheory.CONS_APPEND,Once APPEND_ASSOC]
    >> goal_assum $ drule_at Any
    >> fs[PERM_inter_singlton_eq,process_vote_def,send_msg_def]
    >> fs[o_DEF,FUN_EQ_THM]
  )
  >~ [`(net.state Name_VCS).vcs_state.phase = Voting`,`~MEM (Voter x) (net.state Name_VCS).vcs_state.voted`]
  >- (
    gvs[ref_rel_def,crypt_assum_def,network_step_inv_def,send_packets_def,vcs_msg2netsys_msg_def,combinTheory.APPLY_UPDATE_THM,process_vote_def,send_msg_def,create_packet_def,pkgs_map_NIL_imp]
    >> Cases_on `p.body` >> fs[pkgs_map_NIL_imp]
    >> qmatch_asmsub_rename_tac `Msg_Ballot sign' req_id enc_vote'`
    >> fs[pkgs_map_def]
    >> drule_then assume_tac $ cj 1 $ REWRITE_RULE[EQ_IMP_THM] sortingTheory.PERM_MEM_EQ
    >> fs[FORALL_AND_THM,DISJ_IMP_THM]
    >> dxrule_then strip_assume_tac $ iffLR MEM_SPLIT
    >> pop_assum $ assume_tac o REWRITE_RULE[Once rich_listTheory.CONS_APPEND,Once APPEND_ASSOC]
    >> goal_assum $ drule_at Any
    >> fs[PERM_inter_singlton_eq,process_vote_def,send_msg_def]
    >> fs[FUN_EQ_THM]
    >> simp[pred_setTheory.EXTENSION,AC DISJ_ASSOC DISJ_COMM,IN_DEF,ALL_DISTINCT_APPEND]
    >> fs[IN_DEF]
  )
QED

Theorem refinement_network_step_system_transition:
  !fns c c' deserialise_enc_vote deserialise_sign.
  crypt_assum fns (c,c',deserialise_enc_vote,deserialise_sign)
  /\ fns = (_,_,I)
  ==> refinement
    (λnet net'. ?lb. network_step (netsys_net_handling fns) (netsys_input_handling fns) net lb net')
    (λs s'. ?lbl. system_transition c c' s lbl s')
    (λnet s. ref_rel fns net.packets net.state (c,c',deserialise_enc_vote,deserialise_sign) s)
Proof
  rw[refinement_def,ref_def]
  >> dxrule_then (dxrule_then assume_tac) network_step_system_transition_refinement
  >> gs[SF SatisfySimps.SATISFY_ss]
QED

Theorem refinement_network_step_election_system_transition =
  MATCH_MP
    (refinement_composition
    |> ONCE_REWRITE_RULE[CONJ_COMM]
    |> REWRITE_RULE[GSYM AND_IMP_INTRO])
    $ SPEC_ALL refinement_system_transitions
  |> (fn impl => MATCH_MP impl
      $ UNDISCH_ALL $ SPEC_ALL refinement_network_step_system_transition)
  |> DISCH_ALL
  |> GEN_ALL

Theorem network_step_execution_system_transition_correct1:
  !tr fns c c' deserialise_enc_vote deserialise_sign decrypt vote_format s eligible.
  network_step_execution (netsys_net_handling fns) (netsys_input_handling fns) tr
  /\ crypt_assum fns (c,c',deserialise_enc_vote,deserialise_sign)
  /\ fns = (_,_,I)
  /\ vote_format = FST $ SND $ SND c'
  /\ ref_crypt_assum vote_format decrypt participating
  /\ FINITE eligible
  /\ s = FST $ EL 0 tr
  /\ s = ref_rel_init eligible
  ==> EVERY (λ(s,l,s').
    set (s.state Name_VCS).vcs_state.eligible = set (s'.state Name_VCS).vcs_state.eligible
    /\ set (s'.state Name_VCS).vcs_state.voted SUBSET set (s'.state Name_VCS).vcs_state.voted
    /\ ((s.state Name_VCS).vcs_state.phase = Ended ==>
      set (s'.state Name_VCS).vcs_state.voted = set (s.state Name_VCS).vcs_state.voted
      /\ (s'.state Name_VCS).vcs_state.phase = Ended
      /\ (s'.state Name_VCS).vcs_state.votes = (s'.state Name_VCS).vcs_state.votes)
    /\ ?nv. PERM
      (MAP (decrypt o deserialise_enc_vote) (s'.state Name_VCS).vcs_state.votes)
      (nv ++ (MAP (decrypt o deserialise_enc_vote) (s.state Name_VCS).vcs_state.votes))
  ) tr
Proof
  rpt strip_tac
  >> fs[network_step_execution_def]
  >> rename1 `ref_crypt_assum vote_format decrypt participating`
  >> rename1 `FINITE eligible`
  >> drule_then (qspec_then `decrypt` assume_tac) refinement_network_step_election_system_transition
  >> fs[]
  >> drule_all refinement_step_execution_EVERY_ref
  >> ho_match_mp_tac $ Ho_Rewrite.REWRITE_RULE[GSYM AND_IMP_INTRO] EVERY_MEM_MONO
  >> rpt gen_tac >> ntac 2 strip_tac
  >> fs[pairTheory.ELIM_UNCURRY,ref_def,PULL_EXISTS]
  >> drule_then dxrule refinement_step_execution_EVERY_rel
  >> fs[EVERY_MEM,PULL_EXISTS]
  >> drule_then (qspec_then `eligible` assume_tac) sys_elect_ref1_init
  >> gs[]
  >> disch_then dxrule
  >> fs[GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
  >> impl_tac
  >- (
    irule ref_rel_init_thm
    >> simp[systemTheory.state_component_equality]
    >> irule_at Any EQ_REFL
    >> fs[]
  )
  >> disch_then $ drule_then assume_tac
  >> gs[ELIM_UNCURRY]
  >> first_x_assum $ drule_all_then strip_assume_tac
  >> drule_then assume_tac electionTheory.system_transition_RC_monotonic
  >> qmatch_asmsub_rename_tac `crypt_assum (a,b,I) (c,c',deserialise_enc_vote,deserialise_sign)`
  >> PairCases_on `c'`
  >> qmatch_asmsub_rename_tac `crypt_assum (auth_check_cake,vote_format_cake,I) (_,(contestant_crypt,auth_format,vote_format',serialise_abs_vote),_,_)`
  >> gvs[crypt_assum_def]
  >> gs[electionTheory.election_preserving_def,sys_elect_ref1_def,ref_rel_def,electionTheory.election_component_equality,rich_listTheory.IS_SUFFIX_APPEND]
  >> fs[MAP_MAP_o,o_DEF,crypt_assum_def,FUN_EQ_THM]
  >> CONV_TAC $ DEPTH_CONV ETA_CONV
  >> ONCE_REWRITE_TAC[sortingTheory.PERM_SYM]
  >> irule_at Any sortingTheory.PERM_TRANS
  >> irule_at Any $ iffRL $ cj 1 sortingTheory.PERM_APPEND_IFF
  >> goal_assum $ dxrule_at Any
  >> ONCE_REWRITE_TAC[sortingTheory.PERM_SYM]
  >> fs[]
QED

Theorem network_step_execution_system_transition_correct2:
  !tr fns c c' deserialise_enc_vote deserialise_sign decrypt vote_format s eligible participating.
  network_step_execution (netsys_net_handling fns) (netsys_input_handling fns) tr
  /\ crypt_assum fns (c,c',deserialise_enc_vote,deserialise_sign)
  /\ fns = (_,_,I)
  /\ vote_format = FST $ SND $ SND c'
  /\ ref_crypt_assum vote_format decrypt participating
  /\ FINITE eligible
  /\ s = FST $ EL 0 tr
  /\ s = ref_rel_init eligible
  ==> EVERY (λ(s,l,s').
    (!x. MEM x (s'.state Name_VCS).vcs_state.voted ==>
      MEM x (s'.state Name_VCS).vcs_state.eligible)
    /\ LENGTH (s'.state Name_VCS).vcs_state.voted
      = LENGTH (s'.state Name_VCS).vcs_state.votes
  ) tr
Proof
  rpt strip_tac
  >> fs[network_step_execution_def,EVERY_MEM,Once MEM_EL,pairTheory.ELIM_UNCURRY,PULL_EXISTS]
  >> gen_tac >> strip_tac
  >> qmatch_goalsub_rename_tac `EL n tr`
  >> dxrule_all_then assume_tac step_execution_RTC
  >> drule_then (qspec_then `eligible` assume_tac) sys_elect_ref1_init
  >> drule_then (qspec_then `decrypt` assume_tac) refinement_network_step_election_system_transition
  >> gs[]
  >> dxrule_then mp_tac refinement_RTC
  >> simp[refinement_def,ref_def,PULL_EXISTS]
  >> disch_then dxrule
  >> gs[]
  >> disch_then dxrule
  >> impl_tac
  >- (
    irule ref_rel_init_thm
    >> simp[systemTheory.state_component_equality]
    >> irule_at Any EQ_REFL
    >> fs[]
  )
  >> strip_tac
  >> fs[RC_RTC_EQ]
  >> dxrule_then assume_tac electionTheory.system_transition_RTC_invariant
  >> fs[electionTheory.invariant_init]
  >> qmatch_asmsub_rename_tac `crypt_assum (a,b,I) (c,c',deserialise_enc_vote,deserialise_sign)`
  >> PairCases_on `c'`
  >> qmatch_asmsub_rename_tac `crypt_assum (auth_check_cake,vote_format_cake,I) (_,(contestant_crypt,auth_format,vote_format',serialise_abs_vote),_,_)`
  >> fs[electionTheory.invariant_def,sys_elect_ref1_def,ref_rel_def,electionTheory.voting_ok_def,electionTheory.valid_election_def]
  >> imp_res_tac sortingTheory.PERM_LENGTH
  >> gs[IN_DEF,ALL_DISTINCT_CARD_LIST_TO_SET]
QED

val _ = export_theory ();
