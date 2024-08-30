(*
 Defines verificatum byte trees and from_byte_array and to_byte_array
*)

open HolKernel boolLib Parse bossLib;
open combinTheory numposrepTheory rich_listTheory listTheory ASCIInumbersTheory
     wordsTheory numposrepLib wordsLib arithmeticTheory
     bytesTheory

val _ = new_theory "byteTree";

Datatype:
  bytetree = BTNode (bytetree list) | BTLeaf (word8 list)
End

(* length of encoding byte tree nodes *)
Definition bt_cost_def:
  bt_cost $ BTNode btl = 1 + 4 + SUM (MAP bt_cost btl)
  /\ bt_cost $ BTLeaf btl = 1 + 4 + LENGTH btl
Termination
  WF_REL_TAC `measure bytetree_size`
End

Definition bytetree_size2_def:
  bytetree_size2 (BTNode a) = 1n + bytetree1_size2 a /\
  bytetree_size2 (BTLeaf a) = 1 /\
  bytetree1_size2 [] = 0 /\
  bytetree1_size2 (a0::a1) = 1 + bytetree_size2 a0 + bytetree1_size2 a1
End

Theorem bytetree_size2_SUM:
  !ls. bytetree1_size2 ls = LENGTH ls + (SUM $ MAP bytetree_size2 ls)
Proof
  Induct >> simp[Once bytetree_size2_def]
QED

Theorem bytetree_size2_APPEND:
  !l1 l2. bytetree1_size2 (l1 ++ l2) = bytetree1_size2 l1 + bytetree1_size2 l2
Proof
  fs[bytetree_size2_SUM,SUM_APPEND]
QED

Definition bytetree_max_def:
  bytetree_max = 256 ** 4
End

Definition wf_bytetree_def:
  wf_bytetree (BTLeaf ls) = (LENGTH ls < bytetree_max) /\
  wf_bytetree (BTNode ls) =
    (LENGTH ls < bytetree_max /\ EVERY wf_bytetree ls)
Termination
  WF_REL_TAC `measure $ bytetree_size`
End

Theorem SUC_256_4_EXP_LOG = Q.SPEC `4n` SUC_256_EXP_LOG

Theorem bytetree_max_LOG_LE =
  REWRITE_RULE[GSYM bytetree_max_def] SUC_256_4_EXP_LOG

Triviality bytetree_max4_LOG:
  LOG 256 $ bytetree_max = 4
Proof
  EVAL_TAC
QED

Definition bytes4_def:
  bytes4 = TAKE 4 o PAD_LEFT 0w 4 o bytes
End

Theorem bytes4_thm =
  REWRITE_RULE[FUN_EQ_THM,o_DEF] bytes4_def
  |> CONV_RULE $ DEPTH_CONV BETA_CONV

Theorem bytes4_LENGTH:
  !n. LENGTH $ bytes4 n = 4
Proof
  fs[bytes4_def,LENGTH_GENLIST,LENGTH_TAKE,PAD_LEFT]
QED

Theorem bytes4_zero = EVAL ``bytes4 0``


Theorem bytetree_max_bytes_LENGTH =
  Q.SPEC `4` bytes_LENGTH
  |> REWRITE_RULE[GSYM bytetree_max_def]
  |> SIMP_RULE (std_ss) []

Theorem bytetree_max_unbytes_bytes4 =
  Q.SPEC `4n` unbytes_TAKE_PAD_LEFT_bytes
  |> REWRITE_RULE[GSYM bytetree_max_def,GSYM bytes4_thm]
  |> SIMP_RULE (std_ss) []

Theorem bytetree_max_bytes4_unbytes =
  Q.SPEC `4n` bytes_unbytes
  |> REWRITE_RULE[GSYM bytetree_max_def,GSYM bytes4_thm]
  |> SIMP_RULE (std_ss) []

Definition window_aux_def:
  window_aux n [] = [] /\
  window_aux 0 _ = [] /\
  window_aux n ls = (TAKE n ls) :: (window_aux n $ DROP n ls)
Termination
  WF_REL_TAC `measure $ LENGTH o SND`
  >> fs[]
End

Definition window_def:
  window n ls =
  let
    len = LENGTH ls ;
    diff = len MOD n
  in
    (if diff = 0 then [] else [TAKE diff ls])
    ++ (window_aux n $ DROP diff ls)
End

Definition word8l_from_hex_def:
  word8l_from_hex x = MAP word_from_hex_string $ window 2 x
End

(*
⊢ word8l_from_hex "abcde" = [10w; 188w; 222w]:

EVAL o Term $ ` word8l_from_hex "abcde"`

⊢ word_from_hex_string "0A" = 10w

EVAL o Term $ ` word_from_hex_string "0A"`

*)

Theorem word8_to_hex_example:
  let x = bytes 10 in
    LENGTH x = 1 /\ word_to_hex_string (HD x) = "A"
Proof
  EVAL_TAC
QED

Definition serialise_byteTree_def:
  serialise_byteTree bt : word8 list =
    case bt of
    | BTNode bl =>
        [0w] ++ (bytes4 (LENGTH bl)) ++ (FLAT $ MAP serialise_byteTree bl)
    | BTLeaf wl =>
        [1w] ++ (bytes4 (LENGTH wl)) ++ wl
Termination
  WF_REL_TAC `measure $ bytetree_size`
End

Theorem bt_cost_LENGTH_serialise_byteTree:
  !btl. bt_cost btl = LENGTH $ serialise_byteTree btl
Proof
  gen_tac >> completeInduct_on `bytetree_size2 btl`
  >> reverse Cases
  >- (
    PRED_ASSUM is_forall kall_tac
    >> fs[bytetree_size2_def,serialise_byteTree_def,bytes4_LENGTH,bt_cost_def]
  )
  >> simp[Once serialise_byteTree_def,bt_cost_def,bytetree_size2_def,bytes4_LENGTH]
  >> strip_tac
  >> fs[LENGTH_FLAT,MAP_MAP_o,o_DEF,ADD1,PULL_FORALL,AND_IMP_INTRO]
  >> MK_COMB_TAC >> fs[]
  >> irule MAP_CONG
  >> rw[MEM_SPLIT]
  >> fs[bytetree_size2_SUM,SUM_APPEND]
QED

Definition byte_tree_example_def:
  byte_tree_example = BTNode [
    BTNode [
      BTLeaf $ word8l_from_hex "AF";
      BTLeaf $ word8l_from_hex "03E1" ];
    BTLeaf $ word8l_from_hex "2D52" ]
End

Theorem byte_tree_ex_eq =
  EVAL o Term $ `serialise_byteTree byte_tree_example`

(*

byte_tree_ex_eq
⊢ serialise_byteTree byte_tree_example = [
  0w; 0w; 0w; 0w; 2w;
    0w; 0w; 0w; 0w; 2w;
      1w; 0w; 0w; 0w; 1w; 175w;
      1w; 0w; 0w; 0w; 2w; 3w; 225w;
    1w; 0w; 0w; 0w; 2w; 45w; 82w]

"00 00 00 00 02
  00 00 00 00 02
    01 00 00 00 01 AF
    01 00 00 00 02 03 E1
  01 00 00 00 02 2D 52"

AF = 175w
E1 = 225w
2D = 45w

*)

Definition deserialise_byteTree_acc_def:
  deserialise_byteTree_acc 0 acc (ts : word8 list) = SOME (acc, ts) /\
  deserialise_byteTree_acc (SUC n) acc ts =
    case ts of
    | 1w :: ts =>
      let len = LENGTH ts in
      if len < 4 then NONE else
      let len_data = unbytes (TAKE 4 ts) in
      if len < 4 + len_data \/ bytetree_max <= len_data then NONE else
        deserialise_byteTree_acc n (acc ++ [BTLeaf $ TAKE len_data $ DROP 4 ts]) $ DROP len_data $ DROP 4 ts
    | 0w :: ts =>
      (let len = LENGTH ts in
      if len < 4 then NONE else
      let num = unbytes (TAKE 4 ts) in
      if bytetree_max <= num then NONE else
        case deserialise_byteTree_acc num [] (DROP 4 ts) of
        | NONE => NONE
        | SOME (btl, ts') =>
          if LENGTH btl <> num \/ LENGTH ts <= LENGTH ts' then NONE else
            deserialise_byteTree_acc n (acc ++ [BTNode btl]) ts')
    | _ => NONE
Termination
  WF_REL_TAC `measure $ LENGTH o SND o SND`
  >> fs[]
End

Definition deserialise_byteTree_def:
  deserialise_byteTree x =
  case deserialise_byteTree_acc (SUC 0) [] x of
  | SOME ([x],[]) => SOME x
  | _ => NONE
End

(*
⊢ deserialise_byteTree [1w; 0w; 0w; 0w; 1w; 175w] = SOME (BTLeaf [175w])

EVAL o Term $ `deserialise_byteTree [1w; 0w; 0w; 0w; 1w; 175w]`

⊢ deserialise_byteTree [1w; 0w; 0w; 0w; 2w; 3w; 225w] =
    SOME (BTLeaf [3w; 225w])

EVAL o Term $ `deserialise_byteTree [1w; 0w; 0w; 0w; 2w; 3w; 225w]`

⊢ deserialise_byteTree
    [0w; 0w; 0w; 0w; 2w; 1w; 0w; 0w; 0w; 1w; 175w; 1w; 0w; 0w; 0w; 2w; 3w; 225w] =
     SOME (BTNode [BTLeaf [175w]; BTLeaf [3w; 225w]])

EVAL o Term $ `deserialise_byteTree
  [0w; 0w; 0w; 0w; 2w;
      1w; 0w; 0w; 0w; 1w; 175w;
      1w; 0w; 0w; 0w; 2w; 3w; 225w]
`

EVAL o Term $ `deserialise_byteTree ^( rand $ concl byte_tree_ex_eq)`

   (BTNode [BTNode [BTLeaf [175w]; BTLeaf [3w; 225w]]; BTLeaf [45w; 82w]])

*)

Theorem deserialise_byteTree_acc_APPEND:
  !btl acc rest. EVERY wf_bytetree btl
    ==> deserialise_byteTree_acc (LENGTH btl) acc
        ((FLAT $ MAP serialise_byteTree btl) ++ rest)
      = SOME (acc ++ btl,rest)
Proof
  completeInduct_on `bytetree1_size2 btl`
  >> Cases >- fs[bytetree_size2_def,deserialise_byteTree_acc_def]
  >> rw[bytetree_size2_def,Once deserialise_byteTree_acc_def]
  >> rw[Once serialise_byteTree_def,bytetree_size2_def,wf_bytetree_def,bytes4_LENGTH,TAKE_LENGTH_ID_rwt,TAKE_APPEND1,DROP_APPEND1]
  >> CASE_TAC
  >> fs[bytetree_size2_def,wf_bytetree_def,bytetree_max_unbytes_bytes4,bytes4_LENGTH,TAKE_LENGTH_ID_rwt,TAKE_APPEND1,DROP_APPEND1,DROP_LENGTH_NIL_rwt]
  >> fs[AND_IMP_INTRO,PULL_FORALL,ETA_THM,NOT_LESS_EQUAL]
  >> qmatch_goalsub_abbrev_tac `deserialise_byteTree_acc (LENGTH l) [] (mapl ++ mapt ++ rest)`
  >> first_assum $ qspecl_then [`l`,`[]`,`mapt ++ rest`] mp_tac
  >> impl_tac >- fs[]
  >> unabbrev_all_tac
  >> REWRITE_TAC[APPEND_ASSOC]
  >> disch_then $ fs o single
QED

(* invariant for successful recursion call *)
Definition deserialise_byteTree_acc_inv_def:
  deserialise_byteTree_acc_inv (len,acc,ts) (len',acc',ts') =
  ?btl ts_red. acc' = acc ++ btl /\ ts = ts_red ++ ts'
    /\ LENGTH ts_red = SUM $ MAP bt_cost btl
    /\ ts_red = FLAT $ MAP serialise_byteTree btl
    /\ EVERY wf_bytetree btl
End

Theorem deserialise_byteTree_acc_inv_init:
  !a. deserialise_byteTree_acc_inv a a
Proof
  PairCases >> fs[deserialise_byteTree_acc_inv_def]
QED

Theorem deserialise_byteTree_acc_preserves_invariant:
  !len' acc' ts' len acc ts btl rest.
  deserialise_byteTree_acc_inv (len,acc,ts) (len',acc',ts')
  /\ deserialise_byteTree_acc len' acc' ts' = SOME (btl,rest)
  ==> deserialise_byteTree_acc_inv (len,acc,ts) (0,btl,rest)
Proof
  ho_match_mp_tac deserialise_byteTree_acc_ind
  >> fs[cj 1 deserialise_byteTree_acc_def,NOT_LESS]
  >> rpt strip_tac
  >> qpat_x_assum `deserialise_byteTree_acc (SUC _) _ _ = SOME _` $
    assume_tac o ONCE_REWRITE_RULE[deserialise_byteTree_acc_def]
  >> gvs[AllCaseEqs(),NOT_LESS,NOT_LESS_EQUAL]
  >> first_x_assum irule
  >~ [`BTLeaf`]
  >- (
    fs[deserialise_byteTree_acc_inv_def,SUM_APPEND,serialise_byteTree_def,bytetree_max_bytes4_unbytes]
    >> fs[wf_bytetree_def,bt_cost_def,bytes4_LENGTH]
    >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
    >> rewrite_tac[TAKE_DROP]
  )
  >~ [`BTNode`]
  >> fs[deserialise_byteTree_acc_inv_def]
  >> ONCE_REWRITE_TAC[serialise_byteTree_def]
  >> fs[o_DEF,SUM_APPEND,bytetree_max_bytes4_unbytes,bytes4_LENGTH,LENGTH_FLAT,MAP_MAP_o,ETA_THM,GSYM bt_cost_LENGTH_serialise_byteTree,ADD1]
  >> simp[bt_cost_def,ETA_THM,wf_bytetree_def]
  >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> qpat_x_assum `DROP 4 _ = _` $ rewrite_tac o single o GSYM
  >> fs[]
QED

Theorem deserialise_byteTree_imp_inv':
  !ts btl.
  deserialise_byteTree ts = SOME btl
  ==> deserialise_byteTree_acc_inv (1,[],ts) (0,[btl],[])
Proof
  rw[deserialise_byteTree_def,AllCaseEqs()]
  >> drule_at_then Any irule deserialise_byteTree_acc_preserves_invariant
  >> fs[deserialise_byteTree_acc_inv_init]
QED

Theorem deserialise_byteTree_imp_inv =
  deserialise_byteTree_imp_inv'
  |> SIMP_RULE (srw_ss()) [deserialise_byteTree_acc_inv_def]

Theorem ser_deser:
  !ts bt.
  deserialise_byteTree ts = SOME bt
  ==> serialise_byteTree bt = ts /\ wf_bytetree bt
Proof
  rpt gen_tac >> strip_tac
  >> drule deserialise_byteTree_imp_inv
  >> fs[]
QED

Theorem deser_ser:
  !bt. wf_bytetree bt
  ==> deserialise_byteTree $ serialise_byteTree bt = SOME bt
Proof
  Cases >> fs[]
  >~ [`BTLeaf`]
  >- (
    fs[wf_bytetree_def,serialise_byteTree_def,deserialise_byteTree_def,AllCaseEqs()]
    >> strip_tac
    >> REWRITE_TAC[ONE,Once deserialise_byteTree_acc_def]
    >> fs[AllCaseEqs(),NOT_LESS_EQUAL,NOT_LESS,bytes4_LENGTH,TAKE_LENGTH_ID_rwt,TAKE_APPEND,bytetree_max_unbytes_bytes4,DROP_LENGTH_NIL_rwt,DROP_APPEND]
    >> fs[deserialise_byteTree_acc_def]
  )
  >~ [`BTNode l`]
  >> rw[wf_bytetree_def,Once serialise_byteTree_def,deserialise_byteTree_def]
  >> REWRITE_TAC[Once deserialise_byteTree_acc_def,ONE]
  >> fs[bytes4_LENGTH,TAKE_LENGTH_ID_rwt,TAKE_APPEND,DROP_LENGTH_NIL_rwt,DROP_APPEND,bytetree_max_unbytes_bytes4,bytetree_size2_def,ETA_THM,AllCaseEqs(),NOT_LESS,NOT_LESS_EQUAL]
  >> qmatch_goalsub_abbrev_tac `deserialise_byteTree_acc (LENGTH l) [] mapl`
  >> drule_then (qspecl_then [`[]`,`[]`] mp_tac) deserialise_byteTree_acc_APPEND
  >> fs[]
  >> disch_then kall_tac
  >> fs[deserialise_byteTree_acc_def]
QED

(* is_valid_bytetree : word8 list -> bool *)
Definition is_valid_bytetree_def:
  is_valid_bytetree x =
  case deserialise_byteTree x of
  | SOME $ BTNode [l; r] => T
  | _ => F
End

(* expect each vote as  BTNode [one; two] *)
(* transforms enc_vote_list : N x 2 matrix into 2 x N matrix *)
Definition prepare_submission_def:
  prepare_submission enc_vote_list =
  let enc_vote_pairs = FOLDL (λe x.
    case e of
    | NONE => NONE
    | SOME (el, er) =>
      (case deserialise_byteTree x of
      | SOME $ BTNode [l; r] =>
          SOME (SNOC l el, SNOC r er)
      | _ => NONE)
  ) (SOME ([],[])) enc_vote_list
  in case enc_vote_pairs of
  | SOME (l,r) => SOME $ serialise_byteTree $ BTNode [BTNode l; BTNode r]
  | NONE => NONE
End

Theorem prepare_submission_thm:
  !enc_vote_list.
    EVERY is_valid_bytetree enc_vote_list
    ==> IS_SOME $ prepare_submission enc_vote_list
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> rw[FOLDL_FOLDR_REVERSE,prepare_submission_def,REVERSE_SNOC]
  >> fs[FOLDR_FOLDL_REVERSE,AllCaseEqs(),SNOC_APPEND,EVERY_APPEND,optionTheory.IS_SOME_EXISTS,is_valid_bytetree_def]
  >> dsimp[]
  >> BasicProvers.every_case_tac
QED

val _ = export_theory ();

