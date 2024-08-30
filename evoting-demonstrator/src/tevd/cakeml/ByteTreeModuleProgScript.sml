(*
   Translation of the ByteTree theory
*)

open preamble basis ml_progTheory astPP fromSexpTheory astToSexprLib
     mlmapTheory comparisonTheory totoTheory bytesTheory
     byteTreeTheory Base64ModuleProgTheory;

val _ = new_theory "ByteTreeModuleProg";

val _ = translation_extends "Base64ModuleProg"

val _ = ml_prog_update (open_module "ByteTree");

val r = translate numposrepTheory.n2l_def

Theorem n2l_side_thm:
  !n b. b <> 0 ==> n2l_side b n
Proof
  completeInduct_on `n`
  >> rw[Once $ fetch "-" "n2l_side_def"]
QED
val n2l_side = update_precondition n2l_side_thm;

val r = translate numposrepTheory.l2n_def
Theorem l2n_side_thm:
  !v4 v3. NULL v4 \/ v3 <> 0 ==> l2n_side v3 v4
Proof
  Induct >> rw[Once $ fetch "-" "l2n_side_def"]
QED
val l2n_side = update_precondition l2n_side_thm;

val r = translate $ REWRITE_RULE[GSYM Word8ProgTheory.Word8_fromInt_def] bytes_thm;
Theorem bytes_side_thm:
  !x. bytes_side x
Proof
  fs[fetch "-" "bytes_side_def"]
  >> simp[n2l_side_thm]
QED
val bytes_side = update_precondition bytes_side_thm;

val r = translate $
  REWRITE_RULE[GSYM mllistTheory.take_def,combinTheory.o_DEF] bytes4_def;

val r = translate $
  REWRITE_RULE[GSYM Word8ProgTheory.Word8_toInt_def] unbytes_def;

Theorem unbytes_side_thm:
  !v. unbytes_side v
Proof
  fs[fetch "-" "unbytes_side_def",l2n_side_thm]
QED
val unbytes_side = update_precondition unbytes_side_thm;

val r = translate_no_ind $
  REWRITE_RULE[GSYM mllistTheory.take_def,GSYM mllistTheory.drop_def,bytetree_max_def]
  deserialise_byteTree_acc_def;

Triviality deserialise_bytetree_acc_ind:
  deserialise_bytetree_acc_ind
Proof
  once_rewrite_tac [fetch "-" "deserialise_bytetree_acc_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,mllistTheory.take_def,mllistTheory.drop_def,ADD1,bytetree_max_def]
QED

val _ = deserialise_bytetree_acc_ind |> update_precondition;

val r = translate deserialise_byteTree_def;
val r = translate   serialise_byteTree_def;

(* ⊢ (LIST_TYPE WORD8 --> BOOL) is_valid_bytetree is_valid_bytetree_v *)
val r = translate is_valid_bytetree_def;

(* ⊢ (LIST_TYPE (LIST_TYPE WORD8) --> OPTION_TYPE (LIST_TYPE WORD8)) prepare_submission prepare_submission_v *)
val r = translate $
  REWRITE_RULE[mllistTheory.foldl_intro] prepare_submission_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
