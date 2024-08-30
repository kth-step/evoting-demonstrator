(*
   (De)serialisation of basic datatypes (like strings and option) to word8 list and string
*)

open HolKernel boolLib bossLib Parse;
open BasicProvers arithmeticTheory bitstringTheory combinTheory listTheory
     pairTheory rich_listTheory stringTheory wordsTheory wordsLib optionTheory
     bytesTheory

val _ = new_theory "serialise";

Theorem SUM_MAP_MULT:
  !ls a. a:num * SUM ls = SUM $ MAP (λx. a * x) ls
Proof
  Induct >> rw[arithmeticTheory.LEFT_ADD_DISTRIB]
QED

(* Definitions for reversible (de)serialisation  *)

(* Anything serialised can be deserialised, mostly  P = (λx. T)  *)
Definition ser_imp_deser_def:
  ser_imp_deser ser deser P <=>
    !ser_obj ts ts'.
      ser ser_obj = SOME ts /\ P ser_obj
      ==> deser (ts ++ ts') = SOME (ser_obj,ts')
End

(* Anything deserialised can be serialised *)
Definition deser_imp_ser_def:
  deser_imp_ser ser deser <=>
    !ts ser_obj ts'.
      deser ts = SOME (ser_obj, ts')
      ==> ?ts''. ser ser_obj = SOME ts'' /\ ts = ts'' ++ ts'
End

(* successful serialisation adds to the token stream *)
Definition ser_ok_def:
  ser_ok ser <=>
    !ser_obj ts. ser ser_obj = SOME ts ==> ~NULL ts
End

(* successful deserialisation takes from the token stream *)
Definition deser_ok_def:
  deser_ok deser <=>
    !ts ser_obj ts'.
      deser ts = SOME (ser_obj, ts')
      ==> IS_SUFFIX ts ts' /\ LENGTH ts' < LENGTH ts
End


(* serialise one word8 (identic) *)

Definition serialise_word8_def:
  serialise_word8 x :word8 list option = SOME [x]
End

Definition deserialise_word8_def:
  deserialise_word8 (ts : word8 list) =
    case ts of
    | [] => NONE
    | t::ts => SOME (t, ts)
End

Theorem ser_imp_deser_word8:
  ser_imp_deser serialise_word8 deserialise_word8 (λx. T)
Proof
  fs[ser_imp_deser_def,serialise_word8_def,deserialise_word8_def]
QED

Theorem deser_imp_ser_word8:
  deser_imp_ser serialise_word8 deserialise_word8
Proof
  fs[deser_imp_ser_def,serialise_word8_def,deserialise_word8_def,AllCaseEqs()]
QED

Theorem ser_ok_word8:
  ser_ok serialise_word8
Proof
  fs[ser_ok_def,serialise_word8_def,AllCaseEqs()]
QED

Theorem deser_ok_word8:
  deser_ok deserialise_word8
Proof
  fs[deser_ok_def,deserialise_word8_def,AllCaseEqs(),rich_listTheory.IS_SUFFIX_CONS,rich_listTheory.IS_SUFFIX_CONS2_E,rich_listTheory.IS_SUFFIX_APPEND1]
QED

(* serialise single digit number, smaller than 256 *)

Definition serialise_num_def:
  serialise_num x :word8 list option = SOME $ [n2w x]
End

Definition deserialise_num_def:
  deserialise_num (ts : word8 list) =
    case ts of
    | [] => NONE
    | t::ts => SOME (w2n t, ts)
End

Theorem serialise_num_thm:
  !x ts ts'.
  x < 256 /\ serialise_num x = SOME ts
  ==> deserialise_num (ts++ts') = SOME (x, ts')
Proof
  rw[deserialise_num_def,serialise_num_def] >> fs[dimword_8]
QED

Theorem ser_ok_num:
  ser_ok serialise_num
Proof
  fs[serialise_num_def,ser_ok_def]
QED

Theorem ser_imp_deser_num:
  ser_imp_deser serialise_num deserialise_num (λx. x < 256)
Proof
  fs[ser_imp_deser_def,serialise_num_thm]
QED

Theorem deserialise_num_thm:
  !ts ts' x.
    deserialise_num ts = SOME (x, ts')
    ==> ?ts''. serialise_num x = SOME ts'' /\ ts = ts'' ++ ts'
Proof
  fs[deserialise_num_def,serialise_num_def]
  >> Cases >> fs[]
QED

Theorem deser_imp_ser_num:
  deser_imp_ser serialise_num deserialise_num
Proof
  fs[deser_imp_ser_def,deserialise_num_thm]
QED

Theorem deser_ok_num:
  deser_ok deserialise_num
Proof
  fs[deser_ok_def,deserialise_num_def,AllCaseEqs(),PULL_EXISTS,rich_listTheory.IS_SUFFIX_CONS]
QED

(* serialise word16 *)

Definition serialise_word16_def:
  serialise_word16 (x : word16) :word8 list option =
    SOME $ TAKE 2 $ PAD_LEFT 0w 2 $ bytes $ w2n x
End

Definition deserialise_word16_def:
  deserialise_word16 (ts : word8 list) : (word16 # word8 list) option =
    if LENGTH ts < 2 then NONE else
      SOME (n2w $ unbytes $ TAKE 2 ts, DROP 2 ts)
End

(*
val vv = ``636w:word16``
val v = EVAL ``serialise_word16 (^vv)`` |> concl |> rand
EVAL ``deserialise_word16 $ THE (^v)``
EVAL ``deserialise_word16 $ [0w;0w]``
EVAL ``deserialise_word16 $ [0w;1w]``
EVAL ``deserialise_word16 $ [1w;0w]``
EVAL ``deserialise_word16 $ [1w;1w]``
EVAL ``deserialise_word16 $ [255w;255w]``
*)

Theorem ser_imp_deser_word16:
  ser_imp_deser serialise_word16 deserialise_word16 (λx. T)
Proof
  rw[ser_imp_deser_def,serialise_word16_def,deserialise_word16_def,NOT_LESS,DROP_APPEND,length_pad_left]
  >> qmatch_goalsub_rename_tac `w2n x`
  >> qmatch_goalsub_abbrev_tac `TAKE 2 (TAKE 2 ls ++ ts')`
  >> qspec_then `x` assume_tac $ INST_TYPE [alpha |-> ``:16``] w2n_lt
  >> qspec_then `2` assume_tac unbytes_TAKE_PAD_LEFT_bytes
  >> fs[]
  >> first_x_assum $ drule_then assume_tac
  >> `LENGTH $ TAKE 2 ls = 2` by (
    qunabbrev_tac `ls`
    >> fs[TAKE_LENGTH_ID_rwt,length_pad_left]
  )
  >> gs[TAKE_APPEND1,TAKE_LENGTH_ID_rwt]
QED

Theorem deser_imp_ser_word16:
  deser_imp_ser serialise_word16 deserialise_word16
Proof
  rw[deser_imp_ser_def,serialise_word16_def,deserialise_word16_def,NOT_LESS,unbytes_bytes]
  >> rename1`TAKE 2 ts`
  >> `unbytes $ TAKE 2 ts < 256 ** 2` by (
    irule unbytes_POW_LENGTH
    >> fs[LENGTH_TAKE]
  )
  >> fs[bytes_unbytes,LESS_MOD]
QED

Theorem ser_ok_word16:
  ser_ok serialise_word16
Proof
  fs[GSYM rich_listTheory.LENGTH_NOT_NULL,ser_ok_def,serialise_word16_def,AllCaseEqs(),LENGTH_TAKE_EQ,length_pad_left]
QED

Theorem deser_ok_word16:
  deser_ok deserialise_word16
Proof
  fs[deser_ok_def,deserialise_word16_def,AllCaseEqs(),rich_listTheory.IS_SUFFIX_CONS,rich_listTheory.IS_SUFFIX_CONS2_E,rich_listTheory.IS_SUFFIX_APPEND1,arithmeticTheory.NOT_LESS]
  >> rw[rich_listTheory.IS_SUFFIX_APPEND]
  >> irule_at Any $ GSYM TAKE_DROP
QED

(* serialise word32 *)

Definition serialise_word32_def:
  serialise_word32 (x : word32) :word8 list option =
    SOME $ TAKE 4 $ PAD_LEFT 0w 4 $ bytes $ w2n x
End

Definition deserialise_word32_def:
  deserialise_word32 (ts : word8 list) : (word32 # word8 list) option =
    if LENGTH ts < 4 then NONE else
      SOME (n2w $ unbytes $ TAKE 4 ts, DROP 4 ts)
End

(*
EVAL ``deserialise_word32 [0w:word8;0w;0w;1w]``
EVAL ``serialise_word32 (1w:word32)``

val v = EVAL ``serialise_word32 (65536w:word32)`` |> concl |> rand
EVAL ``deserialise_word32 $ THE (^v)``
*)

Theorem ser_imp_deser_word32:
  ser_imp_deser serialise_word32 deserialise_word32 (λx. T)
Proof
  rw[ser_imp_deser_def,serialise_word32_def,deserialise_word32_def,NOT_LESS,DROP_APPEND,length_pad_left]
  >> qmatch_goalsub_rename_tac `w2n x`
  >> qmatch_goalsub_abbrev_tac `TAKE 4 (TAKE 4 ls ++ ts')`
  >> qspec_then `x` assume_tac $ INST_TYPE [alpha |-> ``:32``] w2n_lt
  >> qspec_then `4` assume_tac unbytes_TAKE_PAD_LEFT_bytes
  >> fs[]
  >> first_x_assum $ drule_then assume_tac
  >> `LENGTH $ TAKE 4 ls = 4` by (
    qunabbrev_tac `ls`
    >> fs[TAKE_LENGTH_ID_rwt,length_pad_left]
  )
  >> gs[TAKE_APPEND1,TAKE_LENGTH_ID_rwt]
QED

Theorem deser_imp_ser_word32:
  deser_imp_ser serialise_word32 deserialise_word32
Proof
  rw[deser_imp_ser_def,serialise_word32_def,deserialise_word32_def,NOT_LESS,unbytes_bytes]
  >> rename1`TAKE 4 ts`
  >> `unbytes $ TAKE 4 ts < 256 ** 4` by (
    irule unbytes_POW_LENGTH
    >> fs[LENGTH_TAKE]
  )
  >> fs[bytes_unbytes,LESS_MOD]
QED

Theorem ser_ok_word32:
  ser_ok serialise_word32
Proof
  fs[GSYM rich_listTheory.LENGTH_NOT_NULL,ser_ok_def,serialise_word32_def,AllCaseEqs(),LENGTH_TAKE_EQ,length_pad_left]
QED

Theorem deser_ok_word32:
  deser_ok deserialise_word32
Proof
  fs[deser_ok_def,deserialise_word32_def,AllCaseEqs(),rich_listTheory.IS_SUFFIX_CONS,rich_listTheory.IS_SUFFIX_CONS2_E,rich_listTheory.IS_SUFFIX_APPEND1,arithmeticTheory.NOT_LESS]
  >> rw[rich_listTheory.IS_SUFFIX_APPEND]
  >> irule_at Any $ GSYM TAKE_DROP
QED

Definition serialise_word64_def:
  serialise_word64 (x : word64) :word8 list option =
    SOME $ TAKE 8 $ PAD_LEFT 0w 8 $ bytes $ w2n x
End

Definition deserialise_word64_def:
  deserialise_word64 (ts : word8 list) : (word64 # word8 list) option =
    if LENGTH ts < 8 then NONE else
      SOME (n2w $ unbytes $ TAKE 8 ts, DROP 8 ts)
End

Theorem ser_imp_deser_word64:
  ser_imp_deser serialise_word64 deserialise_word64 (λx. T)
Proof
  rw[ser_imp_deser_def,serialise_word64_def,deserialise_word64_def,NOT_LESS,DROP_APPEND,length_pad_left]
  >> qmatch_goalsub_rename_tac `w2n x`
  >> qmatch_goalsub_abbrev_tac `TAKE 8 (TAKE 8 ls ++ ts')`
  >> qspec_then `x` assume_tac $ INST_TYPE [alpha |-> ``:64``] w2n_lt
  >> qspec_then `8` assume_tac unbytes_TAKE_PAD_LEFT_bytes
  >> fs[]
  >> first_x_assum $ drule_then assume_tac
  >> `LENGTH $ TAKE 8 ls = 8` by (
    qunabbrev_tac `ls`
    >> fs[TAKE_LENGTH_ID_rwt,length_pad_left]
  )
  >> gs[TAKE_APPEND1,TAKE_LENGTH_ID_rwt]
QED

Theorem deser_imp_ser_word64:
  deser_imp_ser serialise_word64 deserialise_word64
Proof
  rw[deser_imp_ser_def,serialise_word64_def,deserialise_word64_def,NOT_LESS,unbytes_bytes]
  >> rename1`TAKE 8 ts`
  >> `unbytes $ TAKE 8 ts < 256 ** 8` by (
    irule unbytes_POW_LENGTH
    >> fs[LENGTH_TAKE]
  )
  >> fs[bytes_unbytes,LESS_MOD]
QED

Theorem ser_ok_word64:
  ser_ok serialise_word64
Proof
  fs[GSYM rich_listTheory.LENGTH_NOT_NULL,ser_ok_def,serialise_word64_def,AllCaseEqs(),LENGTH_TAKE_EQ,length_pad_left]
QED

Theorem deser_ok_word64:
  deser_ok deserialise_word64
Proof
  fs[deser_ok_def,deserialise_word64_def,AllCaseEqs(),rich_listTheory.IS_SUFFIX_CONS,rich_listTheory.IS_SUFFIX_CONS2_E,rich_listTheory.IS_SUFFIX_APPEND1,arithmeticTheory.NOT_LESS]
  >> rw[rich_listTheory.IS_SUFFIX_APPEND]
  >> irule_at Any $ GSYM TAKE_DROP
QED

Definition serialise_list_def:
  serialise_list (f :'a -> word8 list option) x : word8 list option =
    case x of
    | [] => SOME [0w]
    | t::ts =>
      (case f t of
      | NONE => NONE
      | SOME w =>
        (case serialise_list f ts of
        | NONE => NONE
        | SOME ls => SOME $ [1w : word8] ++ w ++ ls))
End

Theorem ser_ok_list:
  !f. ser_ok f ==> ser_ok $ serialise_list f
Proof
  rpt strip_tac
  >> fs[ser_ok_def]
  >> qx_gen_tac `ls`
  >> measureInduct_on `LENGTH ls`
  >> rw[Once serialise_list_def,AllCaseEqs()]
  >> fs[]
QED

Definition deserialise_list_def:
  deserialise_list (f : word8 list -> ('a # word8 list) option) x =
    case x of
    | [] => NONE
    | (0w:word8)::ts => SOME ([], ts)
    | 1w::ts =>
        (case f ts of
        | NONE => NONE
        | SOME (elem, ts') =>
          if LENGTH ts <= LENGTH ts' then NONE else
          (case deserialise_list f ts' of
          | NONE => NONE
          | SOME (ls', ts') => SOME (elem :: ls', ts')))
    | _ => NONE
Termination
  WF_REL_TAC `measure $ LENGTH o SND` >> fs[]
End

Theorem ser_imp_deser_list:
  !ser deser. ser_imp_deser ser deser (λx. T) /\ ser_ok ser
  ==> ser_imp_deser (serialise_list ser) (deserialise_list deser) (λx. T)
Proof
  rpt strip_tac
  >> simp[ser_imp_deser_def]
  >> Induct
  >> dsimp[Once serialise_list_def,Once deserialise_list_def,AllCaseEqs()]
  >> rpt strip_tac
  >> fs[ser_imp_deser_def,ser_ok_def,arithmeticTheory.NOT_LESS_EQUAL]
  >> ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC]
  >> first_x_assum $ drule_then $ irule_at Any
  >> first_x_assum drule
  >> fs[rich_listTheory.LENGTH_NOT_NULL]
QED

Theorem deser_imp_ser_list:
  !ser deser. deser_imp_ser ser deser /\ deser_ok deser
  ==> deser_imp_ser (serialise_list ser) (deserialise_list deser)
Proof
  rpt strip_tac
  >> simp[deser_imp_ser_def]
  >> qx_gen_tac `ts`
  >> measureInduct_on `LENGTH ts`
  >> dsimp[Once serialise_list_def,Once deserialise_list_def,AllCaseEqs()]
  >> rpt strip_tac
  >> fs[deser_imp_ser_def,deser_ok_def,arithmeticTheory.NOT_LESS_EQUAL]
  >> ntac 2 $ first_x_assum $ drule_then strip_assume_tac
  >> gvs[]
QED

Definition serialise_long_list_def:
  serialise_long_list (f :'a -> word8 list option) ls : word8 list option =
    let len = LENGTH ls in
    let res =
      FOLDL (λe x. OPTION_MAP2 (λx y. x ++ y) e $ f x) (SOME []) $ TAKE (MIN 254 len) ls
    in if 254 < len
    then OPTION_MAP2
          (λx y. x ++ y)
            (OPTION_MAP (λx. 255w::x) res)
              (serialise_long_list f $ DROP 254 ls)
    else OPTION_MAP (λx. (n2w len) :: x) res
Termination
  WF_REL_TAC `measure $ LENGTH o SND` >> fs[]
End

(*
0..<300
EVAL ``GENLIST I 300``
val bla = EVAL ``serialise_long_list serialise_num $ GENLIST I 300``
val rhs_tm = concl bla |> rand
EVAL ``MAP ((n2w : num -> word8) o w2n) $ THE ^rhs_tm``
255; 0..=253;   46; 254; 255; 0w..=43
*)

Theorem ser_ok_long_list:
  !f. ser_ok f ==> ser_ok $ serialise_long_list f
Proof
  rpt strip_tac
  >> fs[ser_ok_def]
  >> qx_gen_tac `ls`
  >> measureInduct_on `LENGTH ls`
  >> rw[Once serialise_long_list_def,AllCaseEqs()]
  >> fs[]
QED

Definition deserialise_long_list_ff_def:
  deserialise_long_list_ff f = (λe_opt.
        case e_opt of
        | NONE => NONE
        | SOME (e,ts) =>
          (case f ts of
          | NONE => NONE
          | SOME (value, ts) => SOME (e ++ [value], ts))
      )
End

Theorem deserialise_long_list_ff_thm:
  !f n ts ts' ser_obj ls. deser_ok f
  /\ FUNPOW (deserialise_long_list_ff f) n (SOME (ls,ts)) = SOME (ser_obj,ts')
  ==> IS_SUFFIX ts ts' /\ LENGTH ts' < SUC $ LENGTH ts
Proof
  gen_tac >> Induct
  >> gs[deser_ok_def,deserialise_long_list_ff_def,FUNPOW_SUC]
  >> rw[AllCaseEqs()]
  >> res_tac
  >- (irule IS_SUFFIX_TRANS >> rpt $ goal_assum $ drule_at Any)
  >> irule LESS_TRANS >> rpt $ goal_assum $ drule_at Any
QED

Definition deserialise_long_list_def:
  deserialise_long_list (f : word8 list -> ('a # word8 list) option) x =
    case x of
    | t::ts =>
      if w2n t < 255
      then FUNPOW (deserialise_long_list_ff f) (w2n t) (SOME ([],ts))
      else
(* only due to non-injectivity of w2n, e.g. case that t = -1w
    EVAL ``w2n (-1w:word8) = w2n (255w:word8)``
*)
        if t <> 255w then NONE
        else
        (case FUNPOW (deserialise_long_list_ff f) 254 (SOME ([],ts)) of
        | NONE => NONE
        | SOME (ls,ts') =>
          if LENGTH ts < LENGTH ts' then NONE else
            (case deserialise_long_list f ts' of
            | SOME ([],_) => NONE
            | SOME (ls', ts) => SOME (ls ++ ls', ts)
            | NONE => NONE))
    | _ => NONE
Termination
  WF_REL_TAC `measure $ LENGTH o SND` >> fs[]
End

Theorem deser_ok_long_list:
  !f. deser_ok f ==> deser_ok $ deserialise_long_list f
Proof
  rpt strip_tac
  >> simp[deser_ok_def]
  >> qx_gen_tac `ts`
  >> measureInduct_on `LENGTH ts`
  >> simp[Once deserialise_long_list_def]
  >> fs[AllCaseEqs()]
  >> rpt gen_tac >> strip_tac
  >- (
    fs[]
    >> irule_at Any IS_SUFFIX_CONS
    >> drule_at Any deserialise_long_list_ff_thm
    >> fs[]
  )
  >> gvs[NOT_LESS]
  >> drule_all_then strip_assume_tac deserialise_long_list_ff_thm
  >> first_x_assum drule
  >> disch_then $ drule_then strip_assume_tac
  >> irule_at Any IS_SUFFIX_CONS
  >> fs[]
  >> irule IS_SUFFIX_TRANS >> rpt $ goal_assum $ drule_at Any
QED

Theorem FOLDL_OPTION_MAP2:
  !x x' f f'. FOLDL (λe x. OPTION_MAP2 f e (f' x)) NONE x = SOME x' ==> F
Proof
  Induct >> fs[OPTION_MAP2_DEF]
QED

Theorem FOLDL_OPTION_MAP2_IS_PREFIX:
  !x s f x'.
  FOLDL (λe x. OPTION_MAP2 (λx y. x ++ y) e (f x)) (SOME s) x = SOME x'
  ==> IS_PREFIX x' s
Proof
  Induct >> rw[]
  >> Cases_on `f h` >> fs[] >- imp_res_tac FOLDL_OPTION_MAP2
  >> first_x_assum $ drule_then assume_tac
  >> drule_then irule IS_PREFIX_APPEND1
QED

Theorem ser_deser_long_list_FOLDL_FUNPOW:
  !f f' x ts' x'.
  ser_imp_deser f f' (λx. T)
  /\ FOLDL (λe x. OPTION_MAP2 (λx y. x ++ y) e (f x)) (SOME []) x = SOME x'
  ==> FUNPOW (deserialise_long_list_ff f') (LENGTH x) (SOME ([],x' ++ ts')) = SOME (x,ts')
Proof
  ntac 2 gen_tac
  >> fs[FOLDL_FOLDR_REVERSE]
  >> Induct using SNOC_INDUCT >- fs[NULL_EQ]
  >> rw[] >> gvs[FUNPOW_SUC,REVERSE_SNOC]
  >> gvs[ser_imp_deser_def,ser_ok_def]
  >> fs[FOLDR_FOLDL_REVERSE]
  >> qmatch_goalsub_rename_tac `_ ++ y ++ ts'`
  >> last_x_assum $ qspec_then `y ++ ts'` assume_tac
  >> fs[deserialise_long_list_ff_def,AllCaseEqs()]
QED

Theorem ser_imp_deser_long_list:
  !f f'. ser_imp_deser f f' (λx. T)
  ==> ser_imp_deser (serialise_long_list f) (deserialise_long_list f') (λx. T)
Proof
  rpt strip_tac
  >> simp[ser_imp_deser_def]
  >> qx_gen_tac `x`
  >> measureInduct_on `LENGTH x`
  >> dsimp[Once serialise_long_list_def,AllCaseEqs()]
  >> reverse $ rpt strip_tac
  >- (
    simp[Once deserialise_long_list_def]
    >> gs[MIN_DEF,arithmeticTheory.NOT_LESS]
    >> drule_all ser_deser_long_list_FOLDL_FUNPOW
    >> fs[]
  )
  >> gs[MIN_DEF,arithmeticTheory.NOT_LESS]
  >> ONCE_REWRITE_TAC[deserialise_long_list_def]
  >> dsimp[MIN_DEF,arithmeticTheory.NOT_LESS,AllCaseEqs()]
  >> drule_all ser_deser_long_list_FOLDL_FUNPOW
  >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> fs[LENGTH_TAKE] >> disch_then kall_tac
  >> qexists_tac `EL 254 x`
  >> qexists_tac `DROP (SUC 254) x`
  >> Ho_Rewrite.REWRITE_TAC[GSYM CONS_APPEND,GSYM APPEND_ASSOC]
  >> drule_then (ONCE_REWRITE_TAC o single o GSYM) DROP_CONS_EL
  >> fs[TAKE_DROP]
QED

Theorem deser_ser_long_list_FUNPOW:
  !f f' n ts ts'' ls.
  deser_imp_ser f f'
  /\ FUNPOW (deserialise_long_list_ff f') n (SOME ([],ts)) = SOME (ls,ts'')
  ==>
    ?ts'. FOLDL (λe x. OPTION_MAP2 (λx y. x ++ y) e $ f x) (SOME []) ls = SOME ts'
    /\ ts = ts' ++ ts''
    /\ n = LENGTH ls
Proof
  ntac 2 gen_tac
  >> fs[FOLDL_FOLDR_REVERSE]
  >> Induct >> rw[]
  >> gvs $ [FUNPOW_SUC,AllCaseEqs()]
    @ (single $ REWRITE_RULE[FUN_EQ_THM] deserialise_long_list_ff_def)
  >> first_x_assum $ drule_then strip_assume_tac
  >> fs[REVERSE_APPEND,PULL_EXISTS,deser_imp_ser_def]
QED

Theorem deser_imp_ser_long_list:
  !f f'. deser_imp_ser f f'
  ==> deser_imp_ser (serialise_long_list f) (deserialise_long_list f')
Proof
  rpt strip_tac
  >> simp[deser_imp_ser_def]
  >> qx_gen_tac `x`
  >> measureInduct_on `LENGTH x`
  >> dsimp[Once deserialise_long_list_def,AllCaseEqs()]
  >> rpt strip_tac
  >> gs[MIN_DEF,arithmeticTheory.NOT_LESS]
  >> ONCE_REWRITE_TAC[serialise_long_list_def]
  >> dsimp[MIN_DEF,arithmeticTheory.NOT_LESS,AllCaseEqs()]
  >~ [`w2n t < 255`]
  >- (
    disj2_tac
    >> dxrule_all_then strip_assume_tac deser_ser_long_list_FUNPOW
    >> fs[EQ_SYM_EQ,n2w_w2n]
  )
  >> disj1_tac
  >> fs[AND_IMP_INTRO,PULL_FORALL]
  >> drule_then (dxrule_then strip_assume_tac) deser_ser_long_list_FUNPOW
  >> first_x_assum $ drule_at_then Any assume_tac
  >> gvs[TAKE_APPEND,DROP_APPEND,TAKE_LENGTH_ID_rwt,DROP_LENGTH_NIL_rwt]
QED

(* assumes strings are shorter than 256 character *)
Definition serialise_string_def:
  serialise_string str :word8 list option =
    if 0 < LENGTH str /\ LENGTH str < 256 then
      SOME $ n2w (LENGTH str)::MAP (n2w o ORD) (EXPLODE str)
    else NONE
End

Theorem ser_ok_string:
  ser_ok serialise_string
Proof
  fs[ser_ok_def,serialise_string_def]
QED

Definition deserialise_string_def:
  deserialise_string (ts: word8 list) =
  case ts of
  | [] => NONE
  | t::ts =>
    let len = w2n t in
      if 0 < len /\ len <= LENGTH ts then
        SOME ( MAP (CHR o w2n) $ TAKE len ts, DROP len ts)
      else NONE
End

Theorem deser_ok_string:
  deser_ok deserialise_string
Proof
  rw[deser_ok_def,deserialise_string_def,AllCaseEqs()]
  >> fs[IS_SUFFIX_APPEND]
  >> Q.REFINE_EXISTS_TAC `_::_`
  >> fs[]
  >> irule_at Any $ GSYM TAKE_DROP
QED

Theorem serialise_string_thm:
  !str ts. serialise_string str = SOME ts
  ==> deserialise_string ts = SOME (str, [])
Proof
  rw[deserialise_string_def,serialise_string_def]
  >> fs[MAP_TAKE,MAP_MAP_o,o_DEF,ORD_BOUND,GSYM STRLEN_EXPLODE_THM,dimword_8,IMPLODE_EXPLODE_I]
QED

Theorem serialise_string_thm':
  !str ts ts'. serialise_string str = SOME ts
  ==> deserialise_string (ts++ts') = SOME (str, ts')
Proof
  rw[deserialise_string_def,serialise_string_def]
  >> fs[MAP_TAKE,MAP_MAP_o,o_DEF,ORD_BOUND,MAP_APPEND,
    DROP_APPEND,TAKE_APPEND1,GSYM STRLEN_EXPLODE_THM,IMPLODE_EXPLODE_I,dimword_8]
QED

Theorem deserialise_string_thm:
  !ts ts' str.
    deserialise_string ts = SOME (str, ts')
    ==> ?ts''. serialise_string str = SOME ts'' /\ ts = ts'' ++ ts'
Proof
  fs[deserialise_string_def,serialise_string_def]
  >> Cases
  >> fs[MAP_MAP_o,o_DEF,IMPLODE_EXPLODE_I] >> strip_tac
  >> assume_tac $ INST_TYPE [alpha |-> ``:8``] w2n_lt
  >> fs[dimword_8,iffLR ORD_CHR]
QED

Theorem ser_imp_deser_string:
  ser_imp_deser serialise_string deserialise_string (λx. T)
Proof
  fs[ser_imp_deser_def,serialise_string_thm']
QED

Theorem deser_imp_ser_string:
  deser_imp_ser serialise_string deserialise_string
Proof
  fs[deser_imp_ser_def,deserialise_string_thm]
QED

Definition serialise_opt_def:
  serialise_opt (f :'a -> word8 list option) v =
    case v of
    | SOME v =>
      (case f v of
      | SOME fv => SOME $ (0w:word8) :: fv
      | NONE => NONE)
    | NONE => SOME [1w]
End

Definition deserialise_opt_def:
  deserialise_opt (f : word8 list -> ('a # word8 list) option) (ts : word8 list) =
    case ts of
    | 0w::ts =>
      (case f ts of
      | NONE => NONE
      | SOME (v,ts) => SOME (SOME v, ts))
    | 1w::ts => SOME (NONE, ts)
    | _ => NONE
End

Theorem ser_imp_deser_opt:
  !f f'. ser_imp_deser f f' (λx. T)
  ==> ser_imp_deser (serialise_opt f) (deserialise_opt f') (λx. T)
Proof
  dsimp[AllCaseEqs(),ser_imp_deser_def,serialise_opt_def,deserialise_opt_def]
QED

Theorem deser_imp_ser_opt:
  !f f'. deser_imp_ser f f'
  ==> deser_imp_ser (serialise_opt f) (deserialise_opt f')
Proof
  dsimp[deser_imp_ser_def,AllCaseEqs(),serialise_opt_def,deserialise_opt_def]
QED

Theorem ser_ok_opt:
  !f. ser_ok f ==> ser_ok $ serialise_opt f
Proof
  dsimp[serialise_opt_def,AllCaseEqs(),ser_ok_def]
QED

Theorem deser_ok_opt:
  !f. deser_ok f ==> deser_ok $ deserialise_opt f
Proof
  dsimp[deser_ok_def,deserialise_opt_def,AllCaseEqs(),rich_listTheory.IS_SUFFIX_CONS,arithmeticTheory.LT_SUC_LE,arithmeticTheory.LESS_OR_EQ]
QED

Theorem ser_ok_opt_string:
  ser_ok $ serialise_opt serialise_string
Proof
  fs[ser_ok_string,ser_ok_opt]
QED

Theorem deser_ok_opt_string:
  deser_ok $ deserialise_opt deserialise_string
Proof
  fs[deser_ok_opt,deser_ok_string]
QED

(* pair *)

Definition serialise_pair_def:
  serialise_pair
    (f :'a -> word8 list option)
    (f' :'b -> word8 list option)
    pair : word8 list option =
    case f $ FST pair of
    | NONE => NONE
    | SOME x =>
      (case f' $ SND pair of
      | NONE => NONE
      | SOME y => SOME $ x ++ y)
End

Theorem ser_ok_pair:
  !f f'. ser_ok f \/ ser_ok f' ==> ser_ok $ serialise_pair f f'
Proof
  rw[ser_ok_def,serialise_pair_def,AllCaseEqs(),PULL_EXISTS,FORALL_PROD]
  >> first_x_assum drule
  >> fs[]
QED

Definition deserialise_pair_def:
  deserialise_pair
    (f : word8 list -> ('a # word8 list) option)
    (f' : word8 list -> ('b # word8 list) option)
    (ts : word8 list) =
    case f ts of
    | NONE => NONE
    | SOME (x,ts) =>
      (case f' ts of
      | NONE => NONE
      | SOME (y,ts) => SOME ((x,y),ts))
End

Theorem deser_ok_pair:
  !deser1 deser2. deser_ok deser1 /\ deser_ok deser2
  ==> deser_ok (deserialise_pair deser1 deser2)
Proof
  csimp[AllCaseEqs(),PULL_EXISTS,deser_ok_def,PULL_FORALL,AND_IMP_INTRO,deserialise_pair_def]
  >> rpt gen_tac >> strip_tac
  >> fs[GSYM PULL_FORALL]
  >> rpt $ first_x_assum $ dxrule_then strip_assume_tac
  >> fs[]
  >> rpt (
    irule rich_listTheory.IS_SUFFIX_TRANS
    >> goal_assum dxrule
  )
  >> rewrite_tac[rich_listTheory.IS_SUFFIX_REFL]
QED

Theorem ser_imp_deser_pair:
  !ser1 ser2 deser1 deser2.
  ser_imp_deser ser1 deser1 (λx. T) /\ ser_imp_deser ser2 deser2 (λx. T)
  ==> ser_imp_deser (serialise_pair ser1 ser2)
    (deserialise_pair deser1 deser2) (λx. T)
Proof
  dsimp $ [AllCaseEqs(),PULL_EXISTS,optionTheory.IS_SOME_EXISTS,ser_imp_deser_def]
    @ [serialise_pair_def,deserialise_pair_def]
  >> rpt strip_tac
  >> rpt (
    first_x_assum $ dxrule_then $ irule_at Any
    >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  )
  >> REFL_TAC
QED

Theorem deser_imp_ser_pair:
  !ser1 ser2 deser1 deser2.
  deser_imp_ser ser1 deser1
  /\ deser_imp_ser ser2 deser2
  ==> deser_imp_ser (serialise_pair ser1 ser2)
    (deserialise_pair deser1 deser2)
Proof
  csimp $ [deser_imp_ser_def,AllCaseEqs(),PULL_EXISTS]
    @ [serialise_pair_def,deserialise_pair_def]
  >> rpt strip_tac
  >> rpt $ first_x_assum $ dxrule_then strip_assume_tac
  >> fs[]
QED

(* automatically derivable *)

Definition serialise_sum_def:
  serialise_sum f f' x = case x of
    | INL x =>
      (case f x of
      | SOME y => SOME $ (0w:word8)::y
      | NONE => NONE)
    | INR x =>
      (case f' x of
      | SOME y => SOME $ 1w::y
      | NONE => NONE)
End

Definition deserialise_sum_def:
  deserialise_sum f f' ts = case ts of
    | (0w:word8)::ts =>
      (case f ts of
      | SOME (y,ts :word8 list) => SOME (INL y,ts)
      | NONE => NONE)
    | 1w::ts =>
      (case f' ts of
      | SOME (y,ts :word8 list) => SOME (INR y,ts)
      | NONE => NONE)
    | _ => NONE
End

Theorem ser_imp_deser_sum:
  !fl fl' fr fr'.
  ser_imp_deser fl fl' (λx. T) /\ ser_imp_deser fr fr' (λx. T)
  ==> ser_imp_deser (serialise_sum fl fr)
        (deserialise_sum fl' fr') (λx. T)
Proof
  dsimp[AllCaseEqs(),ser_imp_deser_def,serialise_sum_def,deserialise_sum_def]
QED

Theorem deser_imp_ser_sum:
  !fl fl' fr fr'.
  deser_imp_ser fl fl' /\ deser_imp_ser fr fr'
  ==> deser_imp_ser (serialise_sum fl fr) (deserialise_sum fl' fr')
Proof
  dsimp[deser_imp_ser_def,AllCaseEqs(),serialise_sum_def,deserialise_sum_def]
QED

Theorem ser_ok_sum:
  !f f'. ser_ok f /\ ser_ok f' ==> ser_ok $ serialise_sum f f'
Proof
  dsimp[ser_ok_def,serialise_sum_def,AllCaseEqs()]
QED

Theorem deser_ok_sum:
  !f f'. deser_ok f /\ deser_ok f' ==> deser_ok $ deserialise_sum f f'
Proof
  csimp[AllCaseEqs(),PULL_EXISTS,deser_ok_def,PULL_FORALL,AND_IMP_INTRO,deserialise_sum_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[GSYM PULL_FORALL,rich_listTheory.IS_SUFFIX_CONS,rich_listTheory.IS_SUFFIX_REFL]
  >> rpt $ first_assum $ dxrule_then strip_assume_tac
  >> fs[]
QED

val _ = export_theory ();
