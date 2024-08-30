(*
  The state of the CDN and its handlers
 *)

open HolKernel boolLib Parse bossLib BasicProvers
open relationTheory listTheory rich_listTheory arithmeticTheory;
open formatCryptoTheory formatTheory finite_mapTheory signatureTheory

val _ = new_theory "cdnState";

Datatype:
  cdnState = <|
      contestants : contestant list
    ; client_hello : voter list
    ; signatures : rp
    ; electionpubkey : pubkey
  |>
End

Definition cdnInit_def:
  cdnInit = <|
      contestants := []
    ; client_hello := []
    ; signatures := rpInit : rp
    ; electionpubkey := [n2w 0]
  |>
End

Definition cdn_set_contestants_def:
  cdn_set_contestants cls s =
    if s.contestants = cdnInit.contestants
    then SOME $ s with <| contestants := cls |>
    else NONE
End

Definition cdn_set_pubkey_def:
  cdn_set_pubkey key s =
    if s.electionpubkey = cdnInit.electionpubkey
    then SOME $ s with <| electionpubkey := key |>
    else NONE
End

Definition cdn_client_hello_def:
  cdn_client_hello voter s =
    s with client_hello updated_by (SNOC voter)
End

val _ = export_theory ();
