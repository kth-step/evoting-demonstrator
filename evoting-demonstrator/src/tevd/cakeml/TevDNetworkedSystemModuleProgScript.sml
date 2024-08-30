
open preamble basis ml_progTheory astPP fromSexpTheory astToSexprLib
     mlmapTheory comparisonTheory totoTheory bytesTheory
     executionTheory networkTheory formatTheory vcsStateTheory mixnetStateTheory
     serialiseTheory TevDNetworkedSystemTheory TevDLibsProgTheory
     hexbyteTheory;

val _ = new_theory "TevDNetworkedSystemModuleProg";

Theorem serialise_num_translate_thm =
  REWRITE_RULE[GSYM Word8ProgTheory.Word8_fromInt_def] serialise_num_def;

Theorem serialise_word64_translate_thm =
  REWRITE_RULE[GSYM Word64ProgTheory.Word64_toInt_def,GSYM mllistTheory.take_def] serialise_word64_def

Theorem deserialise_word64_translate_thm =
  REWRITE_RULE[GSYM Word64ProgTheory.Word64_fromInt_def,GSYM mllistTheory.take_def,GSYM mllistTheory.drop_def] deserialise_word64_def

Theorem ws2n_word8_eq =
  INST_TYPE [alpha |-> ``:8``] ws2n_def
  |> REWRITE_RULE[ws2n_acc_eq,GSYM Word8ProgTheory.Word8_toInt_def,wordsTheory.dimword_8]

Theorem serialise_long_list_thm =
  REWRITE_RULE[GSYM mllistTheory.drop_def,GSYM mllistTheory.take_def,mllistTheory.foldl_intro] serialise_long_list_def

Theorem EXPLODE_explode_eq:
  !str. EXPLODE $ explode str = explode str
Proof
  Induct >> Induct >> fs[EXPLODE_def]
QED

Theorem serialise_string_translate_thm =
  REWRITE_RULE[GSYM Word8ProgTheory.Word8_fromInt_def] serialise_string_def;

Theorem deserialise_string_translate_thm =
  deserialise_string_def
  |> REWRITE_RULE [GSYM CharProgTheory.fromByte_def,combinTheory.o_DEF]
  |> REWRITE_RULE[GSYM Word8ProgTheory.Word8_toInt_def,
      GSYM StringProgTheory.String_implode_def,GSYM mlstringTheory.implode_def,
      GSYM mllistTheory.drop_def,GSYM mllistTheory.take_def];

Theorem word8_tostring_thm =
  REWRITE_RULE[GSYM Word8ProgTheory.Word8_toInt_def] word8_tostring_def;

Theorem process_vote_cake_thm =
  REWRITE_RULE[ml_translatorTheory.MEMBER_INTRO] process_vote_cake_def;

Theorem serialise_mlstring_thm =
  SIMP_RULE (srw_ss()) [serialise_string_translate_thm,combinTheory.o_DEF,optionTheory.OPTION_MAP_CASE,pairTheory.ELIM_UNCURRY,EXPLODE_explode_eq,GSYM Word8ProgTheory.Word8_toInt_def,GSYM mllistTheory.drop_def] serialise_mlstring_def

Theorem deserialise_mlstring_thm:
  deserialise_mlstring ts =
  if NULL ts
  then NONE
  else if 0 < Word8_toInt (HD ts) /\ Word8_toInt (HD ts) <= LENGTH (TL ts)
  then
    SOME
      (implode
          (MAP (\x. CHR (Word8_toInt x))
            (take (TL ts) (Word8_toInt (HD ts)))),
        drop (TL ts) (Word8_toInt (HD ts)))
  else NONE
Proof
  fs[deserialise_mlstring_def,combinTheory.o_DEF,optionTheory.OPTION_MAP_CASE,pairTheory.LAMBDA_PROD,list_case_compute,option_case_compute,LET_THM,COND_RATOR,COND_RAND,Word8ProgTheory.Word8_toInt_def,GSYM mllistTheory.drop_def,deserialise_string_translate_thm,GSYM CharProgTheory.fromByte_def]
QED

val _ = translation_extends "TevDLibsProg"

val _ = ml_prog_update (open_module "TevDNetworkedSystem");

val _ = register_type ``:vcs_state_cake``;
val _ = register_type ``:netsys_data``;

val r = translate vcs_state_cake_init_def;
val _ = next_ml_names := ["init"];
val _ = translate netsys_init_def;

val r = translate word8_tostring_thm
val r = translate $ REWRITE_RULE[GSYM mllistTheory.take_def] list_tostring_def;
val r = translate option_tostring_def;
val r = translate contestant_tostring_def;
val r = translate voter_tostring_def;
val r = translate request_id_tostring_def;

val r = translate send_msg_cake_def;
val r = translate start_voting_cake_def;
val r = translate end_voting_cake_def;
val r = translate pop_out_msgs_cake_def;
val r = translate formatTheory.get_voterid_def;
val r = translate process_vote_cake_thm;

val r = translate   serialise_mlstring_thm;

val r = translate_no_ind deserialise_mlstring_thm;

Theorem deserialise_mlstring_side_thm:
  deserialise_mlstring_side v
Proof
  once_rewrite_tac [fetch "-" "deserialise_mlstring_side_def"]
  >> rw[NULL_EQ,Word8ProgTheory.Word8_toInt_def]
  >> once_rewrite_tac[GSYM wordsTheory.dimword_8]
  >> irule wordsTheory.w2n_lt
QED

val _ = update_precondition deserialise_mlstring_side_thm;

val _ = translate   serialise_opt_def;
val _ = translate deserialise_opt_def;

Theorem n2ws_word8_ind =
  INST_TYPE [alpha |-> ``:8``] n2ws_ind
  |> REWRITE_RULE[GSYM Word8ProgTheory.Word8_fromInt_def,wordsTheory.dimword_8]

Theorem n2ws_word8_eq =
  INST_TYPE [alpha |-> ``:8``] n2ws_def
  |> REWRITE_RULE[GSYM Word8ProgTheory.Word8_fromInt_def,wordsTheory.dimword_8]

val r = translate_no_ind n2ws_word8_eq;
Triviality n2ws_ind':
  n2ws_ind
Proof
  once_rewrite_tac [fetch "-" "n2ws_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac n2ws_word8_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,mllistTheory.drop_def,mllistTheory.take_def,FORALL_PROD]
QED
val _ = n2ws_ind' |> update_precondition;

val r = translate serialise_word64_translate_thm;
val r = translate ws2n_word8_eq;
val r = translate deserialise_word64_translate_thm;

val r = translate   serialise_num_def;
val r = translate deserialise_num_def;
val r = translate   serialise_format_contestant_def;
val r = translate deserialise_format_contestant_def;
val r = translate   serialise_format_voter_def;
val r = translate deserialise_format_voter_def;

val r = translate   serialise_format_request_id_def;
val r = translate deserialise_format_request_id_def;

val r = translate   serialise_word8_def;
val r = translate deserialise_word8_def;

val res = translate_no_ind serialise_long_list_thm;

Triviality serialise_long_list_ind:
  serialise_long_list_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "serialise_long_list_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,mllistTheory.drop_def,mllistTheory.take_def,FORALL_PROD]
QED

val _ = serialise_long_list_ind |> update_precondition;

val r = translate deserialise_long_list_ff_def;
val res = translate_no_ind deserialise_long_list_def;

Triviality deserialise_long_list_ind:
  deserialise_long_list_ind (:α)
Proof
  once_rewrite_tac [fetch "-" "deserialise_long_list_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = deserialise_long_list_ind |> update_precondition;

val r = translate   serialise_list_def;
val r = translate deserialise_list_def;

val r = translate   serialise_pair_def;
val r = translate deserialise_pair_def;

val _ = next_ml_names := ["serialise_msg"];
val r = translate   serialise_netsys_msg_def;

val _ = next_ml_names := ["deserialise_msg"];
val r = translate deserialise_netsys_msg_def;

val _ = translate   serialise_netsys_name_def;
val _ = translate deserialise_netsys_name_def;

val _ = next_ml_names := ["serialise_output"];
val _ = translate   serialise_netsys_output_def
val r = translate deserialise_netsys_output_def;

val _ = next_ml_names := ["deserialise_input"];
val r = translate deserialise_netsys_input_def;
val r = translate   serialise_netsys_input_def;


val _ = next_ml_names := ["msg_tostring"];
val r = translate netsys_msg_tostring_def;

val r = translate netsys_input_tostring_def;

val r = translate log_tostring_def;
val r = translate phase_tostring_def;
val r = translate vcs_state_tostring_def;
val r = translate netsys_data_tostring_def;
val r = translate netsys_out_tostring_def;
val r = translate pair_tostring_def;
val r = translate sum_tostring_def;

val _ = next_ml_names := ["name_tostring"];
val r = translate netsys_name_tostring_def;

val _ = next_ml_names := ["string_to_name"];
val r = translate string_to_netsys_name_def;

val r = translate trace_tostring_def;

val _ = next_ml_names := ["handler_out_tostring"];
val r = translate netsys_handler_out_tostring_def;

val _ = next_ml_names := ["input_handler"];
val _ = translate netsys_input_handler_def;

val r = translate vcs_msg2netsys_msg_def;
val _ = next_ml_names := ["net_handler"];
val _ = translate netsys_net_handler_def;

val r = translate netsys_msg_is_inputanswer_def;
val _ = next_ml_names := ["msg_partition"];
val r = translate netsys_msg_partition_def;

val r = translate   serialise_requests_def;
val r = translate deserialise_requests_def;

val r = translate   serialise_response_def;
val r = translate deserialise_response_def;

val r = translate main_def;
val r = translate put_get_def;
val r = translate tevd_main_def;

(* translation of hexbyteTheory *)

val res = translate $
  Ho_Rewrite.REWRITE_RULE[mllistTheory.foldl_intro,FUN_EQ_THM] until_none_def

val res = translate $ REWRITE_RULE[LLOOKUP_THM,GSYM mllistTheory.nth_def] hexint_to_string_def
val res = translate hexintlist_to_stringlist_def
val res = translate hexbyteBE_def
val res = translate byteArrayToHexBE_def

Definition hex_bl2hsBE_def:
  hex_bl2hsBE = bytelist_to_hexstrBE hexbyte$hex_alphabet
End

val res = translate $
  REWRITE_RULE[hexbyteTheory.hex_alphabet_def,bytelist_to_hexstrBE_def,FUN_EQ_THM,hex_alphabet_props] hex_bl2hsBE_def

Theorem hex_bl2hsbe_side:
  hex_bl2hsbe_side v1
Proof
  fs[fetch "-" "hex_bl2hsbe_side_def",hexintlist_to_stringlist_some]
  >> irule EVERY_MONOTONIC
  >> irule_at Any byteArrayToHexBE_EVERY
  >> fs[GREATER_DEF]
QED

val _ = hex_bl2hsbe_side |> update_precondition;

(* val _ = show_assums := true; *)

val res = translate_no_ind $
  REWRITE_RULE[GSYM mllistTheory.take_def,GSYM mllistTheory.drop_def] take_map_def;

Triviality take_map_ind:
  take_map_ind (:'a) (:'b)
Proof
  once_rewrite_tac [fetch "-" "take_map_ind_def"]
  \\ fs[mllistTheory.take_def,mllistTheory.drop_def]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,ADD1]
QED

val _ = take_map_ind |> update_precondition;

val res = translate bytehexBE_def
val res = translate hexToByteArrayBE_def


Definition hex_hs2blBE_def:
  hex_hs2blBE = hexstr_to_bytelistBE hexbyte$hex_alphabet
End

val _ = translate OPTION_CHOICE_def

val res = translate INDEX_FIND_def
val res = translate INDEX_OF_def
val res = translate string_to_hexint_def
val res = translate stringlist_to_hexintlist_def

val res = translate $
  REWRITE_RULE[hexbyteTheory.hex_alphabet_def,hexstr_to_bytelistBE_def,FUN_EQ_THM,hex_alphabet_props] hex_hs2blBE_def

Theorem hex_hs2blbe_side:
  hex_hs2blbe_side v1
Proof
  fs[fetch "-" "hex_hs2blbe_side_def"]
  >> qmatch_goalsub_abbrev_tac `OPTION_CHOICE a`
  >> Cases_on `a` >> fs[]
QED

val _ = hex_hs2blbe_side |> update_precondition;

(* transformation on word8 *)
Definition transform_def:
  transform =
    hex_hs2blBE o MAP (toUpper o fromByte) : word8 list -> char list
End

(*

Definition abc_def:
abc = "0000000002000000000201000000210002663959889691193e9317aa66f1ffb1e89c9786919fb45c5aa066f9a21630560100000021009ee9775091c4f805f2b8214b0a29e6dc5657aaacb795ba60dc6a2f783d88d74d00000000020100000021009e70b42e03b118692a9207abac2303d81b6d6c5d1be9f232632b6beba8016cfc01000000210000a3b02bdf64b874322f23a675f73eb23766e4f3b2263e943ce356d5c68ddc4b"
End

EVAL ``
DROP (0 * 13) $ MAP w2n $ transform $ MAP (n2w o ORD) abc
``

[0; 0; 0; 0; 2; 0; 0; 0; 0; 2; 1; 0; 0;
0; 33; 0; 2; 102; 57; 89; 136; 150; 145; 25;
62; 147; 23; 170; 102; 241; 255; 177; 232; 156; 151; 134;
145; 159; 180; 92; 90; 160; 102; 249; 162; 22; 48; 86; 1;
... ]

*)


val _ = translate isLower_def
val res = translate toUpper_def

Theorem toupper_side:
  toupper_side v1
Proof
  fs[fetch "-""toupper_side_def",isLower_def]
QED

val _ = toupper_side |> update_precondition;

(*
type_of $ Term `transform`
:word8 list -> word8 list
*)

val _ = translate transform_def

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
