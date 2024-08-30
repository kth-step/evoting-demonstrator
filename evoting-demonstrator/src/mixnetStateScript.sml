open HolKernel boolLib Parse bossLib BasicProvers;
open relationTheory listTheory rich_listTheory arithmeticTheory sortingTheory;
open formatCryptoTheory formatTheory;

val _ = new_theory "mixnetState";

Datatype:
  mixnetState = <|
      privatekey : privkey option
    ; publickey : pubkey option
    ; mixed : bool
    ; enc_votes : enc_vote list option
    ; votes : contestant list
  |>
End

Definition mixnetStateInit_def:
  mixnetStateInit = <|
      privatekey := NONE
    ; publickey  := NONE
    ; mixed      := F
    ; enc_votes  := NONE
    ; votes      := []
  |>
End

Definition set_privatekey_def:
  set_privatekey key (s: mixnetState) =
    if s.privatekey = mixnetStateInit.privatekey
    then SOME $ s with <| privatekey := key |>
    else NONE
End

Definition set_publickey_def:
  set_publickey key (s: mixnetState) =
    if s.publickey = mixnetStateInit.publickey
    then SOME $ s with <| publickey := SOME key |>
    else NONE
End

Definition set_enc_votes_def:
  set_enc_votes enc_votes (s: mixnetState) =
    if s.enc_votes = mixnetStateInit.enc_votes
    then SOME $ s with <| enc_votes := SOME enc_votes |>
    else NONE
End

Definition set_votes_def:
  set_votes votes (s: mixnetState) =
    if s.votes = mixnetStateInit.votes
    then SOME $ s with <| votes := votes |>
    else NONE
End

Definition mix_def:
  mix votes s =
    if PERM s.votes votes
    then SOME $ s with <| votes := votes ; mixed := T |>
    else NONE
End

val _ = export_theory ();

