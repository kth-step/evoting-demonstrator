(*
  This defines the signing protocol with data
 *)

open HolKernel boolLib Parse bossLib BasicProvers
open listTheory finite_mapTheory;
open formatCryptoTheory mlstringTheory;

val _ = new_theory "signature";

(* unique token assigned to a signature request *)
Type signtoken = ``:num``

(* signer id *)
Type signerid = ``:mlstring``

(* collect crypto functions *)
Datatype:
  crypt_sign = <|
      dec  : data decfn
    ; enc  : data encfn
    ; hash : data hashfn
    ; serialise_sig : sign -> data
  |>
End

(* Trusted Party *)
Datatype:
  tp = <|
    (* active identifiers for signature signing transactions *)
      active_tokens : signtoken set
    ; pubkey : pubkey
    (* per token the user signer id, the signed data and the user signature *)
    ; signed : signtoken |-> (signerid # data # (sign option))
  |>
End

Definition tpInit_def:
  tpInit = <|
      active_tokens := {}
    ; pubkey := [n2w 42]
    ; signed := FEMPTY : signtoken |-> (signerid # word8 list # (sign option))
  |>
End

(* relaying party *)
Datatype:
  rp = <|
      (* pairs of active signing requests user id and token *)
      sign_requests : (signerid # signtoken) list
      (* for each signer contains the signed data and both user and tp signature  *)
    ; signatures : signerid |-> (data # ((sign # sign) option))
  |>
End

Definition rpInit_def:
  rpInit = <|
      sign_requests := []
    ; signatures := FEMPTY : signerid |-> (word8 list # (sign # sign) option)
  |>
End

(* transition label *)
Datatype:
  siglabel =
    SignRequestRP signerid data
  | SignRequestTP signerid data
  | SignToken signtoken
  | SignUserSigning
  | SignSignature
End

Definition get_signid_def:
  get_signid (SignRequestRP signerid data) = SOME signerid
  /\ get_signid (SignRequestTP signerid data) = SOME signerid
  /\ get_signid _ = NONE
End

(* signing transition relation *)
(* sign_tr c rp tp rp' tp' *)
Inductive sign_tr:
  (* request signing at RP (may be an unobserved transition) *)
  (!tp rp signerid data c serialise_data.
   sign_tr c serialise_data (SignRequestRP signerid data) rp tp
     (rp with signatures updated_by (λx. x |+ (signerid,(data,NONE)))) tp)
  (* request signing of data from tp *)
[/\] (!tp rp tok signerid data c serialise_data.
    FLOOKUP rp.signatures signerid = SOME (data,NONE)
    ==> sign_tr c serialise_data (SignRequestTP signerid data) rp tp rp
      (tp with <|
          active_tokens updated_by (λx. tok INSERT x)
        ; signed updated_by (λx. x |+ (tok,(signerid,data,NONE))) |>))
  (* respond with token *)
[/\] (!tp rp tok signerid data c serialise_data.
    FLOOKUP rp.signatures signerid = SOME (data,NONE)
    /\ FLOOKUP tp.signed tok = SOME (signerid, data, NONE)
    ==> sign_tr c serialise_data (SignToken tok) rp tp
      (rp with sign_requests updated_by (λx. SNOC (signerid,tok) x))
      tp)
  (* user signs *)
[/\] (!tp rp tok data signerid (userprivkey : privkey) c serialise_data.
    tok IN tp.active_tokens
    ==> sign_tr c serialise_data SignUserSigning rp tp rp
      (tp with signed updated_by
        (λx. x |+ (tok,(signerid,data,SOME $ c.enc userprivkey $ c.hash $ serialise_data data)))))
  (* rp gets signature *)
[/\] (!tp rp tok data signerid (userprivkey : privkey) c serialise_data.
    tok IN tp.active_tokens
    /\ FLOOKUP tp.signed tok = SOME (signerid,(data,SOME sigservice_sig))
    /\ c.dec userprivkey user_sign = c.hash $ serialise_data data
    /\ c.dec tp.pubkey sigservice_sig = c.hash $ c.serialise_sig user_sign
    ==> sign_tr c serialise_data SignSignature rp tp (rp with signatures updated_by
      (λx. x |+ (signerid,(data,SOME (user_sign,sigservice_sig))))) tp)
End

val _ = export_theory ();

