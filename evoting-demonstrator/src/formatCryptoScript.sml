(*
  Defines types relevant for the crypto
 *)

open HolKernel boolLib Parse bossLib BasicProvers
open wordsTheory;

val _ = new_theory "formatCrypto";

(* basically all data *)
Type data = ``:word8 list``

(* public key *)
Type pubkey = ``:data``

(* private key *)
Type privkey = ``:data``

(* a hash *)
Type hash = ``:data``

(* hash function *)
Type hashfn = ``:'data -> hash``

(* encrypted data: 'data x random *)
Datatype:
  enc_data = Enc 'data num
End

(* decryption function *)
Type decfn = ``:privkey -> 'data enc_data -> 'data``

(* encryption function *)
Type encfn = ``:pubkey -> 'data -> 'data enc_data``

(* signature *)
Type sign = ``:hash enc_data``

(* cryptographic operations on the data *)
Datatype:
  crypt = <|
      dec  : 'data decfn
    ; enc  : 'data encfn
    ; hash : 'data -> num
  |>
End

val _ = export_theory ();
