(*
   The state of the client
 *)

open HolKernel boolLib Parse bossLib BasicProvers;
open formatTheory finite_mapTheory

val _ = new_theory "clientState";

(*
The mutable state of the client contains:
- a contestant
- potentially a vote ballot
- potentially a signature of the above
- an identifier (?)
*)

Datatype:
  clientState = <|
      vote : contestant option
    ; enc_vote : enc_vote option
    ; pubkey : pubkey option
    ; contestants : contestant list
    ; result : vcs_msg option
    ; vote_queue : sign option           (* waiting for submitting a signature *)
  |>
End

Definition clientInit_def:
  clientInit = <|
      vote := NONE
    ; enc_vote := NONE
    ; pubkey := NONE
    ; contestants := []
    ; result := NONE
    ; vote_queue := NONE
  |>
End

(* update client state by function *)
Definition update_client_def:
  update_client (clients : voter |-> clientState) voter f =
    let
      v = FLOOKUP clients voter;
    in
      if IS_SOME v /\ IS_SOME $ f (THE v)
      then SOME $ clients |+ (voter, THE $ f (THE v))
      else NONE
End

(* update a client with a result message *)
Definition update_client_result_def:
  update_client_result clients msg =
    if IS_NONE $ ballot_voter msg
    then SOME clients
    else
      update_client clients (THE $ ballot_voter msg)
        (λs:clientState. SOME $ s with <| result := SOME msg |>)
End

(* extract result and remove it *)
Definition extract_result_def:
  extract_result s =
    if s.result <> clientInit.result
      /\ IS_SOME s.result
    then SOME (THE s.result, s with <| result := clientInit.result |>)
    else NONE
End

(* get vote *)
Definition get_vote_def:
  get_vote s =
    if s.vote_queue <> clientInit.vote_queue
      /\ IS_SOME s.vote_queue
    then SOME $ THE s.vote_queue
    else NONE
End

(* try to set contestants *)
Definition client_set_contestants_def:
  client_set_contestants contestants s =
    if s.contestants <> clientInit.contestants
    then SOME $ s with <| contestants := contestants |>
    else NONE
End

Definition update_contestants_def:
  update_contestants clients voter contestants
  = update_client clients voter $ client_set_contestants contestants
End

(* vote locally, allows re-voting *)
Definition client_vote_def:
  client_vote vote s = SOME $ s with <| vote := SOME vote |>
End

Definition set_vote_def:
  set_vote clients voter vote
  = update_client clients voter $ client_vote vote
End

Definition client_enc_vote_def:
  client_enc_vote enc s =
    if IS_SOME s.vote /\ IS_SOME s.pubkey
    then SOME $ s with <| enc_vote := SOME $ enc (THE s.pubkey) $ THE s.vote |>
    else NONE
End

Definition set_enc_vote_def:
  set_enc_vote clients voter enc
  = update_client clients voter $ client_enc_vote enc
End

val _ = export_theory ();
