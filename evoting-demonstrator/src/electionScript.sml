open HolKernel boolLib Parse bossLib BasicProvers
open formatTheory executionTheory;

val _ = new_theory "election";

(* TODO move upstream*)

Theorem RSUBSET_RC:
  !P R. reflexive P /\ R RSUBSET P ==> (RC R) RSUBSET P
Proof
  rw[relationTheory.RSUBSET,relationTheory.reflexive_def,relationTheory.RC_DEF]
  >> fs[]
QED

Theorem RSUBSET_TC:
  !R R'. transitive R' /\ R RSUBSET R' ==> TC R RSUBSET R'
Proof
  qsuff_tac `!R R' a b. TC R a b /\ transitive R' /\ R RSUBSET R' ==> R' a b`
  >- (
    fs[relationTheory.RSUBSET]
    >> rpt strip_tac
    >> first_x_assum $ drule_all_then irule
  )
  >> ntac 2 gen_tac
  >> fs[GSYM AND_IMP_INTRO,PULL_FORALL]
  >> ho_match_mp_tac relationTheory.TC_INDUCT
  >> conj_tac >- fs[relationTheory.RSUBSET]
  >> rpt strip_tac >> fs[]
  >> fs[relationTheory.transitive_def]
  >> first_x_assum $ drule_at_then Any irule
  >> fs[relationTheory.RSUBSET]
QED

Theorem RSUBSET_RTC:
  !R R'. transitive R' /\ reflexive R' /\ R RSUBSET R' ==> RTC R RSUBSET R'
Proof
  qsuff_tac `
    !R R' a b. RTC R a b /\ transitive R' /\ reflexive R' /\ R RSUBSET R' ==> R' a b
  `
  >- (
    fs[relationTheory.RSUBSET]
    >> rpt strip_tac
    >> first_x_assum $ drule_all_then irule
  )
  >> ntac 2 gen_tac
  >> fs[GSYM AND_IMP_INTRO,relationTheory.RSUBSET,PULL_FORALL]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> conj_tac
  >- fs[relationTheory.reflexive_def]
  >> rpt strip_tac >> fs[]
  >> fs[relationTheory.transitive_def]
  >> first_x_assum $ drule_at_then Any irule
  >> fs[relationTheory.RSUBSET]
QED

(* an election holds the ballot box (votes), the electoral register (voted),
 * and predicates to check for eligible voter and participating contestant *)

Datatype:
  election = <|
      votes : contestant list
    ; voted : voter set
    ; active : bool
    ; participating : contestant -> bool
    ; eligible : voter -> bool
  |>
End

(* valid elections contain votes for participating contestants
 * and eligible voters *)

Definition valid_election_def:
  valid_election (e : election) <=>
    EVERY e.participating e.votes
    /\ !v. v IN e.voted ==> e.eligible v
End

Definition voting_ok_def:
  voting_ok (v : voter) (e : election) <=>
    e.active /\ e.eligible v /\ ~(v IN e.voted)
End

Datatype:
  ballot = <|
      voter : voter
    ; contestant : contestant
  |>
End

Definition process_ballot_def:
  process_ballot (b : ballot) (e : election) : election <=>
    if voting_ok b.voter e
    /\ b.contestant IN e.participating
    then
      e with <|
          votes updated_by (λvotes. b.contestant :: votes)
        ; voted updated_by (λvoted. b.voter INSERT voted)
        |>
    else e
End

(* invariants under processing of ballots *)

Theorem process_ballot_eqs[simp]:
  !b e.
    (process_ballot b e).eligible = e.eligible
    /\ (process_ballot b e).participating = e.participating
Proof
  rw[process_ballot_def]
QED

Definition deactivate_def:
  deactivate (e : election) : election =
    e with active := F
End

Datatype:
  system = <|
      ballots : ballot list
    ; state : election
  |>
End

Definition send_ballot_def:
  send_ballot (v : voter) (c : contestant) (s : system) : system =
    s with ballots updated_by (λx. <| voter := v; contestant := c |> :: x)
End

Definition receive_ballot_def:
  receive_ballot (b : ballot) (s : system) : system =
  s with <|
        ballots updated_by FILTER (λx. x.voter <> b.voter)
      ; state := process_ballot b s.state
    |>
End

Definition end_election_def:
  end_election (s : system) : system =
    s with state updated_by deactivate
End

(*
Properties of elections:

- only ballots from eligible voters are included
- eligible voters can vote at most once
*)

Inductive system_transition:
[~system_send_ballot:]
  (!s s' v c.
    send_ballot v c s = s'
    ==> system_transition s s')
[~system_process_ballot:] (!s s' b.
    MEM b s.ballots
    /\ receive_ballot b s = s'
    ==> system_transition s s')
[~system_end_election:] (!s s'.
    s.state.active
    /\ end_election s = s'
    ==> system_transition s s')
End

Definition ballot_box_init_def:
  ballot_box_init participating eligible = <|
    ballots := []:ballot list
    ; state := <|
        votes := [] : contestant list
      ; voted := {} : voter set
      ; active := T
      ; participating := participating
      ; eligible := eligible
      |>
    |>
End

(*
Invariants:
- #set of voters = LENGTH of list of votes
- set of voters ⊂ set of eligible voters
- Only eligible voter's identity is stored (to check "already voted")
  (by design)
*)

Definition invariant_def:
  invariant sys <=>
    CARD sys.state.voted = LENGTH sys.state.votes
    /\ sys.state.voted SUBSET sys.state.eligible
    /\ FINITE sys.state.voted
    /\ valid_election sys.state
End

Theorem invariant_init:
  !participating eligible.
    invariant $ ballot_box_init participating eligible
Proof
  fs[invariant_def,ballot_box_init_def,valid_election_def]
QED

Theorem system_transition_invariant:
  !s s'.
    system_transition s s'
    /\ invariant s
    ==> invariant s'
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac system_transition_ind
  >> rw[invariant_def,send_ballot_def,receive_ballot_def,process_ballot_def,end_election_def,deactivate_def,valid_election_def]
  >> fs[fetch "-" "system_accfupds",voting_ok_def,pred_setTheory.CARD_INSERT,IN_DEF,deactivate_def,valid_election_def]
QED

Theorem system_transition_RC_invariant:
  !s s'.
    RC system_transition s s'
    /\ invariant s
    ==> invariant s'
Proof
  dsimp[relationTheory.RC_DEF]
  >> ACCEPT_TAC system_transition_invariant
QED

Theorem step_invariant_system_transition_invariant:
  step_invariant (λs l s'. system_transition s s') invariant
Proof
  rw[step_invariant]
  >> drule_all_then irule system_transition_invariant
QED

Theorem system_transition_RTC_invariant:
  !s s'.
    RTC system_transition s s'
    /\ invariant s
    ==> invariant s'
Proof
  fs[GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac relationTheory.RTC_INDUCT
  >> rpt strip_tac
  >> dxrule_then strip_assume_tac system_transition_invariant
  >> fs[]
QED

Definition election_preserving_def:
  election_preserving s s' <=>
      IS_SUFFIX s'.state.votes s.state.votes
    /\ s.state.voted SUBSET s'.state.voted
    /\ s.state.participating = s'.state.participating
    /\ s.state.eligible = s'.state.eligible
    /\ (~s.state.active ==> s'.state = s.state )
End

Theorem transitive_election_preserving:
  transitive election_preserving
Proof
  rw[relationTheory.transitive_def,election_preserving_def]
  >- (drule_then irule rich_listTheory.IS_SUFFIX_TRANS >> fs[])
  >- (drule_then irule pred_setTheory.SUBSET_TRANS >> fs[])
QED

Theorem reflexive_election_preserving:
  reflexive election_preserving
Proof
  rw[relationTheory.reflexive_def,election_preserving_def]
QED

Theorem system_transition_monotonic':
  system_transition RSUBSET election_preserving
Proof
  fs[relationTheory.RSUBSET,GSYM AND_IMP_INTRO,election_preserving_def]
  >> ho_match_mp_tac system_transition_ind
  >> rw[invariant_def,send_ballot_def,receive_ballot_def,process_ballot_def,end_election_def,deactivate_def,valid_election_def,rich_listTheory.IS_SUFFIX_APPEND]
  >> fs[fetch "-" "system_accfupds",voting_ok_def,pred_setTheory.CARD_INSERT,IN_DEF,deactivate_def,valid_election_def]
QED

Theorem system_transition_monotonic =
  REWRITE_RULE[relationTheory.RSUBSET] system_transition_monotonic'

Theorem system_transition_RC_monotonic':
    RC system_transition RSUBSET election_preserving
Proof
  irule RSUBSET_RC
  >> fs[reflexive_election_preserving,system_transition_monotonic']
QED

Theorem system_transition_RC_monotonic =
  REWRITE_RULE[relationTheory.RSUBSET] system_transition_RC_monotonic'

Theorem step_execution_system_transition_election_preserving:
  !ls. step_execution (λs l s'. system_transition s s') ls
  ==> EVERY (λ(s,l,s'). election_preserving s s') ls
Proof
  rpt strip_tac
  >> drule_then irule step_execution_RSUBSET_EVERY
  >> fs[pairTheory.ELIM_UNCURRY,relationTheory.RSUBSET,system_transition_monotonic]
QED

Theorem step_execution_system_transition_election_preserving2:
  !ls.
  step_execution (λs l s'. system_transition s s') ls
  ==> !i j. i < j /\ j < LENGTH ls ==> election_preserving (FST $ EL i ls) (FST $ EL j ls)
Proof
  rpt strip_tac
  >> assume_tac transitive_election_preserving
  >> drule_then (drule_at Any) step_execution_RSUBSET
  >> fs[pairTheory.ELIM_UNCURRY,relationTheory.RSUBSET,system_transition_monotonic]
QED

Theorem system_transition_RTC_monotonic':
  RTC system_transition RSUBSET election_preserving
Proof
  irule RSUBSET_RTC
  >> fs[reflexive_election_preserving,transitive_election_preserving,system_transition_monotonic']
QED

Theorem system_transition_RTC_monotonic =
  REWRITE_RULE[relationTheory.RSUBSET] system_transition_RTC_monotonic'

Theorem system_transition_RTC_init:
  !s s' s'' participating eligible.
  RTC system_transition (ballot_box_init participating eligible) s
  ==>
    invariant s /\ s.state.participating = participating /\ s.state.eligible = eligible
Proof
  rpt gen_tac >> strip_tac
  >> drule system_transition_RTC_invariant
  >> fs[invariant_init]
  >> drule system_transition_RTC_monotonic
  >> fs[ballot_box_init_def,election_preserving_def]
QED

(* when election ends only active state changes *)

Theorem system_transition_ending:
  !s s'.
    system_transition s s'
    /\ s.state.active
    /\ ~s'.state.active
    ==>
    s'.state = s.state with active updated_by $~
Proof
  fs[fetch"-""election_component_equality",fetch"-""system_component_equality"]
  >> dsimp[rich_listTheory.IS_SUFFIX_APPEND,system_transition_cases,PULL_EXISTS,send_ballot_def,receive_ballot_def,process_ballot_def,end_election_def,deactivate_def,voting_ok_def]
  >> dsimp[COND_RAND,COND_RATOR]
QED

(* recorded-as-cast : the ballot is recorded unaltered *)
(* for a single transition *)

Theorem recorded_as_cast:
  !v c s s' s''.
  s.state.active
  /\ s' = send_ballot v c s
  /\ v IN s.state.eligible
  /\ ~(v IN s.state.voted)
  /\ c IN s.state.participating
  /\ s'' = receive_ballot <| voter := v; contestant := c |> s'
  ==> SUC $ LENGTH $ FILTER ($= c) s'.state.votes
    = LENGTH $ FILTER ($= c) s''.state.votes
Proof
  fs[send_ballot_def,receive_ballot_def,fetch "-" "system_accfupds",IN_DEF,process_ballot_def,voting_ok_def]
QED

val _ = export_theory ();

