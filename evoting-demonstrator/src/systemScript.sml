(*
   The voting system implementation
 *)

open HolKernel boolLib Parse bossLib BasicProvers
open relationTheory listTheory rich_listTheory arithmeticTheory
     formatCryptoTheory formatTheory executionTheory finite_mapTheory
     vcsStateTheory clientStateTheory signatureTheory cdnStateTheory mixnetStateTheory
     byteTreeTheory;

val _ = new_theory "system";

(* TODO move general thms *)

Theorem SPLITP_single =
  EVAL o Term $ `SPLITP P [x]` |> GEN_ALL;

Theorem SPLITP_eq:
  !ls P. FST (SPLITP P ls) ++ SND (SPLITP P ls) = ls
Proof
  rpt gen_tac
  >> ONCE_REWRITE_TAC[EQ_SYM_EQ]
  >> irule rich_listTheory.SPLITP_JOIN
  >> fs[pairTheory.PAIR]
  >> irule_at Any EQ_REFL
QED

Theorem SPLITP_NULL:
  !ls P. NULL $ SND $ SPLITP P ls <=> EVERY ($~ o P) ls
Proof
  reverse $ rw[EQ_IMP_THM]
  >> fs[combinTheory.o_DEF]
  >- (drule rich_listTheory.SPLITP_EVERY >> fs[])
  >> qmatch_asmsub_rename_tac `SPLITP P ls`
  >> Cases_on `SPLITP P ls`
  >> gs[NULL_EQ,rich_listTheory.SPLITP_NIL_SND_EVERY,combinTheory.o_DEF]
QED

(* Entities *)
Datatype:
  entity = VCS | Client request_id | SigService | MixNet | Admin | CDN
End

(* Messages *)
Datatype:
  message =
    ClientMsg request_id cl_msg
  | SigMsg sig_msg
  | VCSMsg vcs_msg
  | AdminMsg admin_msg
  | CDNMsg (contestant list)
  | ElectionResult ((contestant # num) list)
  | Tau
End

(* state of the system *)
Datatype:
  state = <|
      vcs          : vcsState
    ; clients      : voter |-> clientState
    ; sigservice   : tp
    ; cdn          : cdnState
    ; mixnet       : mixnetState
  |>
End

val state_component_equality = fetch"-" "state_component_equality";

(* initial state *)
Definition init_def:
  init = <|
      vcs          := vcsStateInit
    ; clients      := FEMPTY
    ; sigservice   := tpInit
    ; cdn          := cdnInit
    ; mixnet       := mixnetStateInit
  |>
End

Definition sign_label_to_entity_def:
  sign_label_to_entity (SignRequestRP _ _) = CDN
  /\ sign_label_to_entity (SignRequestTP _ _) = SigService
  /\ sign_label_to_entity (SignToken _) = CDN
  /\ sign_label_to_entity SignUserSigning = SigService
  /\ sign_label_to_entity SignSignature = CDN
End

Theorem sign_label_to_entity_ineq:
  !b. sign_label_to_entity b = VCS <=> F
Proof
  Cases >> fs[sign_label_to_entity_def]
QED

(*
  transitions
  c is the crypto for signatures
  c' is the crypto for votes
  lbl = (target, msg)
*)

Inductive system_transition:
  (* generate public key *)
  (!(s :state) s' (c: crypt_sign) a v (c': crypt_vote) pubkey privatekey mixnet' mixnet''.
    set_publickey pubkey s.mixnet = SOME mixnet'
    /\ set_privatekey privatekey mixnet' = SOME mixnet''
    /\ s' = s with <| mixnet := mixnet'' |>
    ==> system_transition c (c',a,v) s (MixNet, Tau) s')
  (* send list of contestants and public key *)
[/\] (!(s :state) s' c c' cls pubkey cdn' cdn''.
    cdn_set_contestants cls s.cdn = SOME cdn'
    /\ cdn_set_pubkey pubkey cdn' = SOME cdn''
    /\ s' = s with <| cdn := cdn'' |>
    ==> system_transition c c' s (CDN, AdminMsg $ Contestants cls) s')
  (* start the voting phase *)
[/\] (!s s' c c' vl vcs'.
    start_voting s.vcs (set vl) = SOME vcs'
    /\ s' = s with <| vcs := vcs' |>
    ==> system_transition c c' s (VCS, AdminMsg $ VotingStart vl) s')
  (* client hello to CDN *)
[/\] (!s s' c c' voter clientid cdn' voterid.
    cdn_client_hello voter s.cdn = cdn'
    /\ s' = s with <| cdn := cdn' |>
    ==> system_transition c c' s (CDN, ClientMsg clientid $ Hello voterid) s')
  (* receive list of contestants from CDN *)
[/\] (!s s' c c' contestants clients' voter clientid.
    contestants = s.cdn.contestants
    /\ update_contestants s.clients voter contestants = SOME clients'
    /\ s' = s with <| clients := clients' |>
    ==> system_transition c c' s (Client clientid, CDNMsg contestants) s')
  (* cast vote and hash *)
[/\] (!s s' c c' clients' clients'' voter vote clientid.
    set_vote s.clients voter vote = SOME clients'
    /\ set_enc_vote clients' voter (FST c').enc = SOME clients''
    /\ s' = s with <| clients := clients'' |>
    ==> system_transition c c' s (Client clientid, Tau) s')
  (* signing protocol *)
[/\] (!s label (target:entity) (mes:message) s' c c' rp tp rp' tp' serialise.
    sign_tr c serialise label rp tp rp' tp'
    /\ rp = s.cdn.signatures
    /\ tp = s.sigservice
    /\ s' = s with <|
        sigservice := tp'
      ; cdn := s.cdn with <| signatures := rp' |>
    |>
    /\ target = sign_label_to_entity label
    (* can only sign if client has said hello *)
    /\ (IS_SOME $ get_signid label ==>
      MEM (Voter $ THE $ get_signid label) s.cdn.client_hello)
    ==> system_transition c c' s (target,mes) s')
  (* send vote from client to VCS *)
[/\] (!s c c' s' request_id sign enc_vote.
    (* TODO add signing *)
    (* ALL_DISTINCT (request_id::MAP FST s.vcs.in_msgs) *)
    s' = s with <| vcs updated_by stow_vote (request_id,sign,enc_vote)|>
    ==> system_transition c (c',auth_check,vote_format,serialise_abs_vote) s (VCS,ClientMsg request_id $ PreVote sign request_id enc_vote) s')
  (* process a received vote *)
[/\] (!s c c' s' auth_check vote_format request_id serialise_abs_vote enc_vote sign xs ys.
    s.vcs.in_msgs = xs ++ (request_id,sign,enc_vote)::ys
    /\ s' = (s with <| vcs updated_by process_vote auth_check vote_format serialise_abs_vote (sign,enc_vote,request_id) |>)
      with <| vcs updated_by (λx.
      x with in_msgs := xs ++ ys
    ) |>
    ==> system_transition c (c',auth_check,vote_format,serialise_abs_vote) s (VCS,Tau) s')
  (* send voting response to client *)
[/\] (!s s' clients' vcs' c c' voter clientid m.
    vcs_send_response m voter s.vcs = SOME vcs'
    /\ update_client_result s.clients m = SOME clients'
    /\ s' = s with <|
        vcs := vcs'
      ; clients := clients'
    |>
    ==> system_transition c c' s (Client clientid,VCSMsg m) s')
  (* end the voting *)
[/\] (!s s' c c' vcs'.
    end_voting s.vcs = SOME vcs'
    /\ s' = s with <| vcs := vcs' |>
    ==> system_transition c c' s (VCS,AdminMsg VotingEnd) s')
  (* send votes to mixnet *)
[/\] (!s s' c c' enc_votes auth_check vote_format serialise_abs_vote mixnet'.
    set_enc_votes enc_votes s.mixnet = SOME mixnet'
    /\ enc_votes = s.vcs.votes
    /\ s' = s with <| mixnet := mixnet' |>
    ==> system_transition c (c',auth_check,vote_format,serialise_abs_vote) s (MixNet,VCSMsg $ SendVotes enc_votes) s')
  (* mix votes *)
[/\] (!s s' c c' mixnet' votes.
    s.vcs.phase = Ended
    /\ mix votes s.mixnet = SOME mixnet'
    /\ s' = s with <| mixnet := mixnet' |>
    ==> system_transition c c' s (MixNet,Tau) s')
  (* decrypt votes *)
[/\] (!s s' c c' mixnet' votes.
    IS_SOME s.mixnet.privatekey
    /\ IS_SOME s.mixnet.enc_votes
    /\ votes = MAP ((FST c').dec $ THE s.mixnet.privatekey) $ THE s.mixnet.enc_votes
    /\ s.mixnet.mixed
    /\ set_votes votes s.mixnet = SOME mixnet'
    /\ s' = s with <| mixnet := mixnet' |>
    ==> system_transition c c' s (MixNet,Tau) s')
End

(* the transition target label (nearly) encodes the changed state component *)

Theorem system_transition_unchanged:
  system_transition c c' s (CDN,mes) s'
  ==> s.vcs = s'.vcs
  /\ s.clients = s'.clients
  /\ s.sigservice = s'.sigservice
Proof
  dsimp[system_transition_cases,sign_label_to_entity_def,sign_tr_cases]
QED

Theorem system_transition_unchanged1:
  system_transition c c' s (Client id,mes) s'
  ==> s.cdn = s'.cdn /\ s.sigservice = s'.sigservice
Proof
  dsimp[system_transition_cases,sign_label_to_entity_def,sign_tr_cases,state_component_equality]
QED

Theorem system_transition_unchanged2:
  system_transition c c' s (SigService,mes) s'
  ==> s.vcs = s'.vcs
  /\ s.cdn = s'.cdn
  /\ s.clients = s'.clients
Proof
  dsimp[system_transition_cases,sign_label_to_entity_def,sign_tr_cases,get_signid_def,state_component_equality,cdnState_component_equality]
QED

Theorem system_transition_unchanged3:
  system_transition c c' s (VCS,mes) s'
  ==> s.cdn = s'.cdn
  /\ s.clients = s'.clients
  /\ s.sigservice = s'.sigservice
Proof
  dsimp[system_transition_cases,sign_label_to_entity_def,sign_tr_cases]
QED

(* system_transition invariants *)

Theorem system_transition_phase_inv:
  !c c'' s lbl s'.
    system_transition c c'' s lbl s'
    /\ s.vcs.phase <> Init ==> s'.vcs.phase <> Init
Proof
  rpt gen_tac >> strip_tac
  >> fs[GSYM AND_IMP_INTRO,GSYM PULL_FORALL,RC_DEF,system_transition_cases]
  >> gvs[start_voting_def,stow_vote_def,end_voting_def,vcs_send_response_def,clientStateTheory.update_client_result_def,send_msg_def,process_vote_def]
  >> fs[COND_RAND,COND_RATOR]
QED

Definition log_msg_ended_def:
  log_msg_ended x = ?m. x = Voteerror (Inactive Ended) m
End

Definition system_transition_inv_def:
  system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s <=>
    (s.vcs.phase <> Init ==> s.vcs.voted SUBSET s.vcs.eligible)
    /\ (s.vcs.phase = Init ==> s.vcs.voted = {})
    /\ LENGTH s.vcs.votes = CARD s.vcs.voted
    /\ FINITE s.vcs.eligible
    /\ FINITE s.vcs.voted
    /\ LENGTH s.vcs.votes <= LENGTH s.vcs.log
    /\ EVERY (is_valid_bytetree o serialise_abs_vote) s.vcs.votes
(*
desired but not checked
    /\ ALL_DISTINCT s.vcs.votes
*)
    /\ (!enc_vote. MEM enc_vote s.vcs.votes
      ==>
(* cannot reason about earlier votes: voter NOTIN s.vcs.voted *)
      ?voter sign.
        voter IN s.vcs.eligible
        /\ auth_check sign
        /\ vote_format sign enc_vote = SOME voter
        /\ is_valid_bytetree $ serialise_abs_vote enc_vote
        /\ MEM (Votesuccess sign enc_vote) s.vcs.log)
    /\ EVERY (λx. !sign enc_vote. x = Votesuccess sign enc_vote
      ==> MEM enc_vote s.vcs.votes) s.vcs.log
    /\ (!lr.
      lr = SPLITP log_msg_ended s.vcs.log
      ==> EVERY log_msg_ended $ SND lr
      /\ (s.vcs.phase <> Ended ==> NULL $ SND lr)
    )
    /\ (!id x.
      FLOOKUP s.clients id = SOME x
      ==> IS_SOME x.vote = IS_SOME x.enc_vote
        /\ (IS_SOME x.vote ==>
          ?y. x.enc_vote = SOME $ c'.enc y $ THE x.vote
        ))
End

Theorem system_transition_inv_init:
  !crypto. system_transition_inv crypto init
Proof
  dsimp[system_transition_inv_def,init_def,vcsStateInit_def,pairTheory.FORALL_PROD,rich_listTheory.SPLITP]
QED

Theorem system_transition_preserve_inv:
  !c c' s lbl s' auth_check vote_format serialise_abs_vote.
    system_transition c (c',auth_check,vote_format,serialise_abs_vote) s lbl s'
    /\ system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s
    ==> system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s'
Proof
  simp[system_transition_inv_def,system_transition_cases]
  >> rpt gen_tac >> strip_tac
  >~ [`set_privatekey _ _ = SOME _`,`set_publickey _ _ = _`]
  >- (
    gvs[]
    >> asm_rewrite_tac[]
  )
  >~ [`cdn_set_contestants _ _ = SOME _`]
  >- (
    gvs[] >> asm_rewrite_tac[]
  )
  >~ [`start_voting _ _ = SOME _`]
  >- (
    gvs[start_voting_def]
    >> asm_rewrite_tac[]
  )
  >~ [`cdn_client_hello _`,`ClientMsg _ _`]
  >- (
    gvs[] >> asm_rewrite_tac[]
  )
  >~ [`update_contestants _ _ _ = SOME _`,`CDNMsg _`]
  >- (
    gvs[update_contestants_def,update_client_def,client_set_contestants_def,COND_RAND,COND_RATOR,FLOOKUP_UPDATE]
    >> dxrule_then strip_assume_tac $ iffLR optionTheory.IS_SOME_EXISTS
    >> dsimp[COND_EXPAND_OR]
    >> first_assum $ dxrule_then $ fs o single
    >> rw[]
    >> first_x_assum drule
    >> fs[]
  )
  >~ [`set_enc_vote _ _ _ = SOME _`]
  >- (
    gvs[set_vote_def,set_enc_vote_def,client_enc_vote_def,update_client_def,COND_RAND,COND_RATOR,FLOOKUP_UPDATE,COND_EXPAND_OR,client_vote_def]
    >> rpt $ dxrule_then strip_assume_tac $ iffLR optionTheory.IS_SOME_EXISTS
    >> dsimp[]
    >> irule_at (Pos $ el 1) EQ_REFL
    >> rw[]
    >> first_assum $ dxrule_then $ fs o single
    >> fs[]
  )
  >~ [`sign_tr`,`get_signid label'`]
  >- (
    gvs[] >> asm_rewrite_tac[]
  )
  >~ [`vcs_send_response _ _ _ = SOME _`]
  >- (
    fs[COND_RATOR,COND_RAND,update_client_result_def]
    >> gvs[update_client_def,vcs_send_response_def,client_set_contestants_def,COND_EXPAND_OR,FLOOKUP_UPDATE]
    >> asm_rewrite_tac[]
    >> dxrule_then strip_assume_tac $ iffLR optionTheory.IS_SOME_EXISTS
    >> dsimp[COND_EXPAND_OR,FLOOKUP_UPDATE,COND_RATOR,COND_RAND]
    >> rw[]
    >> first_x_assum $ drule_then strip_assume_tac
    >> fs[]
  )
  >~ [`end_voting s.vcs = SOME _`]
  >- (
    gvs[end_voting_def]
    >> asm_rewrite_tac[]
  )
  >~ [`set_enc_votes _ _ = SOME _`,`VCSMsg $ SendVotes _`]
  >- (
    fs[] >> asm_rewrite_tac[]
  )
  >~ [`mix _ _ = SOME _`,`(MixNet,Tau)`]
  >- (
    fs[] >> asm_rewrite_tac[]
  )
  >~ [`set_votes _ _ = SOME _`,`(MixNet,Tau)`]
  >- (
    fs[] >> asm_rewrite_tac[]
  )
  >~ [`stow_vote (request_id,sign,enc_vote)`]
  >- (
    gvs[stow_vote_def] >> asm_rewrite_tac[]
  )
  >~ [`process_vote auth_check vote_format ser_abs_vote`]
  >- (
    (* very slow*)
    fs[start_voting_def,end_voting_def,update_client_result_def,vcs_send_response_def,process_vote_def]
    >> BasicProvers.every_case_tac
    >> fs[send_msg_def,PULL_FORALL,SNOC_APPEND]
    >> gs[Once $ GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,optionTheory.IS_SOME_EXISTS]
    >> dsimp[rich_listTheory.SPLITP_APPEND,SPLITP_single]
    >> qmatch_asmsub_abbrev_tac `NULL $ SND $ SPLITP P _`
    >> CONV_TAC $ ONCE_DEPTH_CONV $ ONCE_REWRITE_CONV[COND_RAND]
    >> fs[]
    >> `s.vcs.phase <> Ended ==> ~EXISTS P s.vcs.log` by (
      rw[] >> gs[SPLITP_NULL]
    )
    >> Cases_on `s.vcs.phase`
    >> gs[log_msg_ended_def,SPLITP_NULL,combinTheory.o_DEF]
    >> ONCE_REWRITE_TAC[EXISTS_NOT_EVERY]
    >> SIMP_TAC std_ss [combinTheory.o_DEF]
    >> CONV_TAC $ DEPTH_CONV $ ETA_CONV
    >> asm_rewrite_tac[]
    >> rw[Abbr`P`,log_msg_ended_def]
    >> rev_drule_at_then Any (irule_at Any) $ MP_CANON EVERY_MONOTONIC
    >> fs[]
  )
QED

Theorem system_transition_preserve_inv_RTC:
  !c c' auth_check vote_format serialise_abs_vote s s'.
    RTC (λa b. ?lbl. system_transition c (c',auth_check,vote_format,serialise_abs_vote) a lbl b) s s'
    /\ system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s
    ==> system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s'
Proof
  ntac 5 gen_tac
  >> fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac RTC_INDUCT
  >> rw[]
  >> first_x_assum irule
  >> drule_all_then irule system_transition_preserve_inv
QED

Theorem system_transition_preserve_inv_init_RTC:
  !c c' auth_check vote_format serialise_abs_vote s s'.
    RTC (λa b. ?lbl. system_transition c (c',auth_check,vote_format,serialise_abs_vote) a lbl b) init s
    ==> system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s
Proof
  rpt strip_tac
  >> qmatch_abbrev_tac `system_transition_inv crypto _`
  >> qspec_then `crypto` assume_tac system_transition_inv_init
  >> unabbrev_all_tac
  >> drule_all_then irule system_transition_preserve_inv_RTC
QED

Theorem system_transition_preserve_ended:
  !c c' s lbl s' auth_check vote_format serialise_abs_vote.
    system_transition c (c',auth_check,vote_format,serialise_abs_vote) s lbl s'
    /\ system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s
    /\ s.vcs.phase = Ended
    ==> s.vcs.phase = s'.vcs.phase
    /\ s.vcs.votes = s'.vcs.votes
    /\ s.vcs.voted = s'.vcs.voted
    /\ (s'.vcs.log = s.vcs.log \/ ?m. s'.vcs.log = s.vcs.log ++ [Voteerror (Inactive Ended) m])
Proof
  rw[system_transition_cases]
  >> gvs[start_voting_def,end_voting_def,clientStateTheory.update_client_result_def,vcs_send_response_def,process_vote_def,send_msg_def,stow_vote_def]
QED

Theorem system_transition_preserve_ended_RTC:
  !c c' auth_check vote_format serialise_abs_vote s s'.
    RTC (λa b. ?lbl. system_transition c (c',auth_check,vote_format,serialise_abs_vote) a lbl b) s s'
    /\ system_transition_inv (c',auth_check,vote_format,serialise_abs_vote) s
    /\ s.vcs.phase = Ended
    ==> s.vcs.phase = s'.vcs.phase
    /\ s.vcs.votes = s'.vcs.votes
    /\ s.vcs.voted = s'.vcs.voted
    /\ s.vcs.log = TAKE (LENGTH s.vcs.log) s'.vcs.log
    /\ EVERY (λx. ?m. x = Voteerror (Inactive Ended) m)
      $ DROP (LENGTH s.vcs.log) s'.vcs.log
Proof
  ntac 5 gen_tac
  >> fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac RTC_INDUCT
  >> fs[rich_listTheory.DROP_LENGTH_NIL,AND_IMP_INTRO]
  >> rpt gen_tac >> strip_tac
  >> drule_all_then assume_tac system_transition_preserve_inv
  >> drule_all_then assume_tac system_transition_preserve_ended
  >> gs[]
  >> qmatch_goalsub_rename_tac `TAKE (LENGTH s.vcs.log) s''.vcs.log`
  >> qpat_x_assum `s'.vcs.log = TAKE (LENGTH s.vcs.log + 1) s''.vcs.log` kall_tac
  >> qspecl_then [`LENGTH s.vcs.log + 1`,`s''.vcs.log`] mp_tac TAKE_DROP
  >> disch_then $ ONCE_REWRITE_TAC o single o GSYM
  >> qpat_x_assum `_ = TAKE (LENGTH s.vcs.log + 1) s''.vcs.log` $ ONCE_REWRITE_TAC o single o GSYM
  >> fs[rich_listTheory.TAKE_APPEND,rich_listTheory.DROP_APPEND,rich_listTheory.DROP_LENGTH_NIL]
  >> irule rich_listTheory.EVERY_DROP
  >> fs[]
QED

val _ = export_theory ();

