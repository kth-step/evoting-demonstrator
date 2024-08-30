From mathcomp Require Import all_ssreflect.
From RecordUpdate Require Import RecordSet.

Section Election.

Import RecordSetNotations.

Variable voter : finType.

Variable eligible : pred voter.

Variable contestant : finType.

Variable participating : pred contestant.

Variable tabulate : seq contestant -> seq (nat * contestant).

(*
Spec for tabulate function:
 
- every participating contestant has exactly one entry in tabulation results
- tabulation results are sorted in descending order according to most voted for
- the number for each contestant corresponds to number of occurrences in input list
*)

Record election := mkElection
 { votes : seq contestant; voted : {set voter}; active : bool}.

Instance election_settable : Settable _ :=
 settable! mkElection <votes;voted;active>.

Record ballot := mkBallot
 { ballot_voter : voter ; ballot_contestant : contestant }.

Definition code_ballot b := (ballot_voter b, ballot_contestant b).
Definition decode_ballot b := let: (v, c) := b in mkBallot v c.
Lemma cancel_ballot : pcancel code_ballot (fun x => Some (decode_ballot x)).
Proof. by case. Qed.
Canonical ballot_eqType := EqType ballot (PcanEqMixin cancel_ballot).

Definition voting_ok (v : voter) (e : election) :=
 e.(active) && eligible v && (v \notin e.(voted)).

Definition process_ballot (b : ballot) (e : election) : election :=
 if voting_ok b.(ballot_voter) e then
   e <| votes := rcons e.(votes) b.(ballot_contestant) |>
     <| voted := b.(ballot_voter) |: e.(voted) |>
 else e.

Definition deactivate (e : election) : election :=
 e <| active := false |>.

Record system := mkSys { ballots : seq ballot ; state : election }.

Instance system_settable : Settable _ := settable! mkSys <ballots; state>.

Definition send_ballot (v : voter) (c : contestant) (s : system) : system :=
 s <| ballots := mkBallot v c :: s.(ballots) |>.

Definition receive_ballot (b : ballot) (s : system) : system :=
  s <| ballots := rem b s.(ballots) |>
    <| state := process_ballot b s.(state) |>.

Definition end_election (s : system) : system :=
 s <| state := deactivate s.(state) |>.

(* 
Properties of elections:

- only ballots from eligible voters are included
- eligible voters can vote at most once
*)

Inductive system_transition : system -> system -> Prop :=
| system_send_ballot : forall s s' v c,
    send_ballot v c s = s' ->
    system_transition s s'
| system_process_ballot : forall s s' b,
    b \in s.(ballots) ->
    receive_ballot b s = s' ->
    system_transition s s'
| system_end_election : forall s s',
    s.(state).(active) ->
    end_election s = s' ->
    system_transition s s'.

End Election.
