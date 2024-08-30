(*
  Defines the system's types
 *)

open HolKernel boolLib Parse bossLib BasicProvers
open relationTheory listTheory rich_listTheory arithmeticTheory;
open formatCryptoTheory mlstringTheory;

val _ = new_theory "format";

(* basically all data *)
Type data = ``:word8 list``

Datatype:
  request_id = Request word64
End

(* voter id *)
Datatype:
  voter = Voter mlstring
End

Definition get_voterid_def:
  get_voterid $ Voter id = id
End

(* contestants *)
Datatype:
  contestant = Contestant word64
End

Definition contestant_to_word64_def:
  contestant_to_word64 $ Contestant n = n
End

Definition word64_to_contestant_def:
  word64_to_contestant n = Contestant n
End

(* encrypted vote *)
Type enc_vote = ``:contestant enc_data``
Type crypt_vote = ``:contestant crypt``

(* messages that the client emits *)
Datatype:
  cl_msg =
      Vote sign voter enc_vote
    | PreVote sign request_id enc_vote
    | SigningRequest hash voter
    | Hello voter
End

(* admin messages *)
Datatype:
  admin_msg = VotingStart (voter list) | VotingEnd | Contestants (contestant list)
End

Datatype:
  vcs_msg =
      BallotRecorded request_id voter
    | BallotError request_id
    | SendVotes (enc_vote list) (* send votes to mixnet *)
End

Definition ballot_voter_def:
  ballot_voter $ BallotRecorded request voter = SOME voter
  /\ ballot_voter _ = NONE
End

Datatype:
  sig_msg = Signature sign voter
End

val _ = export_theory ();
