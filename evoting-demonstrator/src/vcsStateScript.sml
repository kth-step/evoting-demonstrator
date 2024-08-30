open HolKernel boolLib Parse bossLib BasicProvers
open formatCryptoTheory formatTheory byteTreeTheory

(*
 * The state of the vote collection server
 *)

val _ = new_theory "vcsState";

(*
The mutable state of the VCS contains:
- an append-only list of invalid received votes with error reason
(derived from electionTheory:)
- list of valid votes (will be in order of receival)
- set of voters (for the valid votes)
- voting phases

The immutable state of the VCS contains:
(derived from electionTheory:)
- set of eligible voters
- set of participating contestants
- public key for signature verification
*)

(* an election holds the ballot box (votes), the electoral register (voted),
 * and predicates to check for eligible voter and participating contestant *)

(* different phases of the VCS *)
Datatype:
  vcsPhase = Init | Voting | Ended
End

Datatype:
  vote_error =
          (* ordered by first checked *)
             Inactive vcsPhase (* cannot vote in this phase of the election *)
           | Format            (* unrecognised format *)
           | ByteFormat        (* unrecognised bytetree *)
           | Unauth            (* invalid authentication *)
           | Ineligible        (* voter not part of elegible voters *)
           | Voted             (* voter has already voted *)
End

Datatype:
  log = Voteerror vote_error cl_msg | Votesuccess sign enc_vote
End

Datatype:
  vcsState = <|
      voted : voter set
    ; eligible : voter set
    ; votes : enc_vote list
    ; in_msgs : (request_id # sign # enc_vote) list (* queue of incoming votes *)
    ; out_msg : vcs_msg list        (* outstanding messages to voters *)
    ; log : log list
    ; phase : vcsPhase
  |>
End

val vcsState_accfupds = fetch "-" "vcsState_accfupds";

Definition vcsStateInit_def:
  vcsStateInit = <|
      voted := {}
    ; eligible := {}
    ; votes := []
    ; in_msgs := []
    ; out_msg := []
    ; log := []
    ; phase := Init
  |>
End

Definition send_msg_def:
  send_msg s req_id client (Voteerror vote_error cl_msg) =
    s with <|
        log updated_by (SNOC $ Voteerror vote_error cl_msg)
      ; out_msg := [BallotError req_id]
    |>
  /\ send_msg s req_id client (Votesuccess sign enc_vote) =
    s with <|
        log updated_by (SNOC $ Votesuccess sign enc_vote)
      ; out_msg := [BallotRecorded req_id client]
    |>
End

Definition pop_out_msgs_def:
  pop_out_msgs s =
    (s with out_msg := [], s.out_msg)
End

(* assumes a unique request_id *)
Definition stow_vote_def:
  stow_vote v s = s with in_msgs updated_by (λls. v::ls)
End

(* processing a message of a client *)
(* auth_check is checking signing with a fixed public key *)
Definition process_vote_def:
  process_vote auth_check vote_format serialise_abs_vote (sign,enc_vote,req_id) (s : vcsState) =
    let vote = PreVote sign req_id enc_vote in
    if s.phase <> Voting then
      send_msg s req_id (Voter «unknown») $ Voteerror (Inactive s.phase) vote
    else if IS_NONE $ vote_format sign enc_vote then
      send_msg s req_id (Voter «unknown») $ Voteerror Format vote
    else
    let voter = THE $ vote_format sign enc_vote in
    if ~(is_valid_bytetree $ serialise_abs_vote enc_vote) then
      send_msg s req_id voter $ Voteerror ByteFormat vote
    else if ~auth_check sign then
      send_msg s req_id voter $ Voteerror Unauth vote
    else if voter NOTIN s.eligible then
      send_msg s req_id voter $ Voteerror Ineligible vote
    else if voter IN s.voted then
      send_msg s req_id voter $ Voteerror Voted vote
    else s with <|
        voted updated_by (λx. voter INSERT x)
      ; votes updated_by (SNOC enc_vote)
      ; out_msg := [BallotRecorded req_id voter]
      ; log updated_by (SNOC $ Votesuccess sign enc_vote)
    |>
End

(*
Invariants:
- #set of voters = LENGTH of list of votes
- set of voters ⊂ set of eligible voters
- Only eligible voter's identity is stored (to check "already voted")
  (by design)
- eligible voters can vote at most once
*)

Definition vcs_state_inv_def:
  vcs_state_inv s <=>
    FINITE s.voted
    /\ FINITE s.eligible
    /\ CARD s.voted = LENGTH s.votes
    /\ s.voted SUBSET s.eligible
    /\ CARD s.voted <= CARD s.eligible
End

Theorem vcs_state_inv_thm1:
  !v' s a v sav. vcs_state_inv s ==> vcs_state_inv (process_vote a v sav v' s)
Proof
  PairCases
  >> rw[vcs_state_inv_def,process_vote_def,send_msg_def,listTheory.SNOC_APPEND]
  >~ [`SUC _ <= CARD _`]
  >- (
    drule_all_then assume_tac
      $ Ho_Rewrite.REWRITE_RULE [PULL_EXISTS]
        $ iffRL pred_setTheory.PSUBSET_MEMBER
    >> qpat_x_assum `CARD _ = _` $ fs o single o GSYM
    >> drule_all pred_setTheory.CARD_PSUBSET
    >> fs[]
  )
  >> metis_tac[pred_setTheory.SUBSET_UNION,REWRITE_RULE[relationTheory.transitive_def] pred_setTheory.SUBSET_transitive]
QED

Definition end_voting_def:
  end_voting (s : vcsState) =
    if s.phase = Init \/ s.phase = Ended
    then NONE
    else SOME $ s with <| phase := Ended |>
End

Theorem vcs_state_inv_thm2:
  !v' s s'. vcs_state_inv s
    /\ end_voting s = SOME s'
    ==> vcs_state_inv s'
Proof
  rw[vcs_state_inv_def,end_voting_def]
  >> fs[vcsState_accfupds]
QED

Definition start_voting_def:
  start_voting (s : vcsState) vl =
    if s.phase = Init
    then SOME $ s with <| phase := Voting ; eligible := vl |>
    else NONE
End

Definition vcs_send_response_def:
  vcs_send_response m voter (s : vcsState) =
    if MEM m s.out_msg /\ voter = ballot_voter m
    then SOME $ s with out_msg updated_by (FILTER $ ($<> m))
    else NONE
End

Theorem vcs_state_inv_thm4:
  !m client s s'. vcs_state_inv s
    /\ vcs_send_response m client s = SOME s'
    ==> vcs_state_inv s'
Proof
  rw[vcs_state_inv_def,vcs_send_response_def]
  >> fs[vcsState_accfupds]
  >> fs[pred_setTheory.SUBSET_DEF,listTheory.MEM_FILTER]
QED

(*
Non-expressible invariants (in this model):
- Each voter's sign is never stored
- invalid votes ∩ valid votes = ∅
- invalid votes with Ineligible vote_error
  not in eligible voters
*)

val _ = export_theory ();
