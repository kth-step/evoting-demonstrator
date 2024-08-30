open HolKernel boolLib bossLib Parse;
open combinTheory numposrepTheory rich_listTheory listTheory ASCIInumbersTheory
     wordsTheory numposrepLib wordsLib arithmeticTheory bitstringTheory
     pairTheory

val _ = new_theory "bytes";

(* TODO move upstream *)

Theorem EXISTS_dropWhile:
  !P ls. EXISTS P $ dropWhile ($~ o P) ls = EXISTS P ls
Proof
  gen_tac >> Induct
  >> dsimp[COND_RAND,EQ_IMP_THM,DISJ_EQ_IMP]
QED

Theorem dropWhile_idem:
  !P ls. dropWhile P $ dropWhile P ls = dropWhile P ls
Proof
  gen_tac >> Induct >> fs[dropWhile_def,COND_RAND]
QED

Theorem SUM_MAP_MULT:
  !ls a. a:num * SUM ls = SUM $ MAP (λx. a * x) ls
Proof
  Induct >> rw[arithmeticTheory.LEFT_ADD_DISTRIB]
QED

Theorem SUC_256_EXP_LOG:
  !m n. SUC n <= 256 ** m ==> LOG 256 (SUC n) <= m
Proof
  rpt strip_tac
  >> dxrule_at_then Any assume_tac $ MP_CANON logrootTheory.LOG_LE_MONO
  >> rename1 `256 ** m`
  >> qspecl_then [`m`,`256`,`1`] mp_tac logrootTheory.LOG_EXP
  >> impl_tac >- fs[]
  >> qspec_then `256` mp_tac logrootTheory.LOG_1
  >> impl_tac >- fs[]
  >> disch_then $ REWRITE_TAC o single
  >> REWRITE_TAC[arithmeticTheory.ADD_0,arithmeticTheory.MULT_RIGHT_1]
  >> disch_then $ ONCE_REWRITE_TAC o single o GSYM
  >> first_x_assum irule
  >> fs[]
QED

Theorem PAD_LEFT_REVERSE_REVERSE_PAD_RIGHT:
  !ls x n. PAD_LEFT x n $ REVERSE ls = REVERSE $ PAD_RIGHT x n ls
Proof
  Induct
  >> fs[PAD_LEFT,PAD_RIGHT,REVERSE_GENLIST,K_THM,ADD1]
  >> qx_gen_tac `x`
  >> `K x = λm:num. x` by fs[K_THM,FUN_EQ_THM]
  >> fs[]
QED

Theorem REVERSE_PAD_LEFT_PAD_RIGHT_REVERSE:
  !ls x n. REVERSE $ PAD_LEFT x n ls = PAD_RIGHT x n $ REVERSE ls
Proof
  Induct
  >> fs[PAD_LEFT,PAD_RIGHT,REVERSE_GENLIST,K_THM,ADD1]
  >> qx_gen_tac `x`
  >> `K x = λm:num. x` by fs[K_THM,FUN_EQ_THM]
  >> fs[]
QED

Theorem LOG_SUC_LESS_EQ:
  !a b n. 1 < b /\ 0 < n /\ n < b ** a ==> SUC $ LOG b n <= a
Proof
  Induct >> rw[]
  >> Cases_on `b ** a <= n` >> fs[]
  >- (drule_all logrootTheory.LOG_UNIQUE >> fs[])
  >> fs[NOT_LESS_EQUAL]
  >> first_x_assum drule_all
  >> fs[]
QED

Theorem w2n_MOD_eq:
  !w:word8. w2n w MOD 256 = w2n w
Proof
  gen_tac
  >> irule arithmeticTheory.LESS_MOD
  >> REWRITE_TAC[GSYM dimword_8]
  >> fs[w2n_lt]
QED

Theorem PAD_LEFT_SUC:
  !ls m k. LENGTH ls <= m ==> PAD_LEFT k (SUC m) ls = k::PAD_LEFT k m ls
Proof
  rw[PAD_LEFT]
  >> `SUC m - LENGTH ls = SUC (m - LENGTH ls)` by fs[]
  >> pop_assum $ REWRITE_TAC o single
  >> fs[GENLIST_CONS]
QED

Theorem dropWhile_PAD_LEFT:
  !m ls k. LENGTH ls <= m
  ==> dropWhile ($= k) (PAD_LEFT k m ls) = dropWhile ($= k) ls
Proof
  Induct
  >- fs[dropWhile_def,PAD_LEFT,dropWhile_eq_nil,EVERY_GENLIST]
  >> rw[]
  >> dxrule_then strip_assume_tac $ iffLR LESS_OR_EQ
  >> fs[PAD_LEFT_SUC]
  >> fs[PAD_LEFT]
QED

(* TODO end move upstream *)

Definition bytes_def[nocompute]:
  bytes = n2lA [] (n2w : num -> word8) 256
End

Theorem bytes_thm[compute] =
  SIMP_RULE(srw_ss())[numposrepTheory.n2lA_n2l,FUN_EQ_THM] bytes_def

Theorem bytes_NOT_NULL:
  !n. bytes n <> []
Proof
  rw[GSYM NULL_EQ,GSYM LENGTH_NOT_NULL,bytes_thm,LENGTH_n2l]
QED

Theorem bytes_LENGTH:
  !m n. n < 256 ** m /\ 0 < m ==> LENGTH $ bytes n <= m
Proof
  rw[bytes_thm,LENGTH_n2l]
  >> irule LOG_SUC_LESS_EQ
  >> fs[]
QED

Definition unbytes_def:
  unbytes = l2n 256 o MAP (w2n : word8 -> num) o REVERSE
End

(*

⊢ bytes 256 = [1w; 0w]

EVAL o Term $ `bytes 256`

⊢ unbytes [1w; 0w] = 256

EVAL o Term $ `unbytes [1w; 0w]`

*)

Theorem MAP_dropWhile_inj_w2n:
  !ls. MAP w2n $ dropWhile ($= 0w) ls = dropWhile ($= 0) $ MAP w2n ls
Proof
  Induct >> rw[]
QED

Theorem unbytes_dropWhile_zero:
  !ls. unbytes $ dropWhile ($= 0w) ls = unbytes ls
Proof
  rw[unbytes_def,MAP_REVERSE,MAP_dropWhile_inj_w2n]
  >> qmatch_goalsub_abbrev_tac `dropWhile _ mwl`
  >> qspec_then `mwl` mp_tac REVERSE_REVERSE
  >> disch_then $ ONCE_REWRITE_TAC o single o GSYM
  >> qmatch_goalsub_abbrev_tac `dropWhile _ $ REVERSE rmwl`
  >> REWRITE_TAC[REVERSE_REVERSE]
  >> irule l2n_dropWhile_0
  >> fs[]
QED

Theorem unbytes_zero:
  !ls. unbytes $ 0w :: ls = unbytes ls
Proof
  rw[unbytes_def,MAP_REVERSE]
  >> fs o single $ REWRITE_RULE[SNOC_APPEND] l2n_SNOC_0
QED

Triviality n2l_one:
  1 < b ==> n2l b 1 = [1]
Proof
  fs[Once n2l_def]
QED

Theorem MAP_MOD_n2l:
  !n b. 1 < b ==> MAP (λx. x MOD b) $ n2l b n = n2l b n
Proof
  completeInduct_on `LOG b n`
  >> ONCE_REWRITE_TAC[n2l_def]
  >> rw[]
  >> fs[PULL_FORALL,AND_IMP_INTRO,arithmeticTheory.NOT_LESS,arithmeticTheory.LESS_OR_EQ,n2l_one]
  >> fs[logrootTheory.LOG_RWT]
QED

Theorem unbytes_bytes':
  unbytes o bytes = I
Proof
  rw[FUN_EQ_THM,bytes_thm,unbytes_def,MAP_REVERSE,MAP_MAP_o,o_DEF,w2n_n2w,wordsTheory.dimword_8,MAP_MOD_n2l,l2n_n2l]
QED

Theorem unbytes_bytes =
  SIMP_RULE(srw_ss())[FUN_EQ_THM,o_DEF] unbytes_bytes'

Theorem unbytes_TAKE_PAD_LEFT_bytes:
  !m n. n < 256 ** m /\ 0 < m ==> unbytes (TAKE m $ PAD_LEFT 0w m $ bytes n) = n
Proof
  rpt strip_tac
  >> drule_all_then assume_tac bytes_LENGTH
  >> qmatch_goalsub_abbrev_tac `TAKE m ls`
  >> `LENGTH ls = m` by (unabbrev_all_tac >> fs[PAD_LEFT])
  >> fs[TAKE_LENGTH_ID_rwt]
  >> unabbrev_all_tac
  >> fs[arithmeticTheory.LESS_OR_EQ]
  >~ [`LENGTH $ bytes n  = m`]
  >- gvs[PAD_LEFT,unbytes_bytes]
  >> ONCE_REWRITE_TAC[GSYM unbytes_dropWhile_zero]
  >> fs[dropWhile_PAD_LEFT]
  >> REWRITE_TAC[unbytes_dropWhile_zero,unbytes_bytes]
QED

Theorem bytes_unbytes_special[local]:
  !m ls : word8 list n.
  LENGTH ls = m
  /\ l2n 256 (REVERSE (MAP w2n ls)) <> 0
  /\ Abbrev (n = SUC (LOG 256 (l2n 256 (REVERSE (MAP w2n ls)))))
  /\ n <= m
  ==> EVERY ($= 0w) (TAKE (m − n) ls)
Proof
  rpt strip_tac
  >> fs[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_TAKE]
  >> qho_match_abbrev_tac `!n. P n`
  >> CCONTR_TAC
  >> PRED_ASSUM is_neg $ mp_tac o SIMP_RULE std_ss [NOT_FORALL_THM]
  >> qho_match_abbrev_tac `(?m. Q m) ==> _`
  >> disch_then assume_tac
  >> dxrule_then strip_assume_tac arithmeticTheory.WOP
  >> map_every qunabbrev_tac [`P`,`Q`]
  >> fs[NOT_LESS,DISJ_EQ_IMP,AND_IMP_INTRO]
  >> fs[Once $ GSYM numposrepTheory.l2n_dropWhile_0]
  >> qmatch_asmsub_rename_tac `EL n' ls`
  >> `MAP w2n ls = (MAP w2n $ TAKE n' ls) ++ (MAP w2n $ DROP n' ls)` by (
    rewrite_tac[GSYM MAP_APPEND]
    >> rewrite_tac[TAKE_DROP]
  )
  >> pop_assum $ fs o single o Once
  >> `EVERY ($= 0) $ MAP w2n $ TAKE n' ls` by (
    rw[EVERY_MEM,MEM_MAP,MEM_EL]
    >> fs[EL_TAKE,w2n_eq_0]
  )
  >> fs[MAP_TAKE,dropWhile_APPEND_EVERY]
  >> qhdtm_x_assum `EVERY` kall_tac
  >> PRED_ASSUM is_forall kall_tac
  >> `DROP n' ls = [EL n' ls] ++ DROP (SUC n') ls` by
    fs[GSYM DROP_CONS_EL]
  >> pop_assum $ fs o single
  >> gs[numposrepTheory.l2n_APPEND,logrootTheory.LOG_MULT,l2n_def]
  >> qmatch_asmsub_abbrev_tac `wel MOD 256`
  >> `wel MOD 256 = wel` by (
    irule arithmeticTheory.LESS_MOD
    >> qunabbrev_tac `wel`
    >> rewrite_tac[GSYM dimword_8,w2n_lt]
  )
  >> pop_assum $ fs o single
  >> qunabbrev_tac `wel`
  >> unabbrev_all_tac
  >> fs[ADD1] >> fs[SUB_LEFT_LESS]
  >> qmatch_asmsub_abbrev_tac `LOG _ (a * 256 ** c + b)`
  >> `n' + LOG 256 (256 ** c) <= n' + LOG 256 (b + a * 256 ** c)` by (
    fs[]
    >> irule logrootTheory.LOG_LE_MONO
    >> qunabbrev_tac `a`
    >> fs[]
    >> irule LESS_EQ_TRANS
    >> irule_at Any LESS_EQ_ADD
    >> qexists_tac `b`
    >> fs[w2n_eq_0,GSYM NOT_ZERO_LT_ZERO]
  )
  >> qmatch_asmsub_abbrev_tac `ntc <= n' + _`
  >> dxrule_then (assume_tac o Q.SPEC `1n`) $ iffRL LESS_EQ_MONO_ADD_EQ
  >> dxrule_then assume_tac LESS_EQ_LESS_TRANS
  >> fs[]
  >> first_x_assum $ drule_then assume_tac
  >> `0 < 256 ** c` by fs[]
  >> dxrule_at_then Any assume_tac logrootTheory.LOG_ADD
  >> map_every qunabbrev_tac [`ntc`,`c`]
  >> fs[]
QED

Theorem unbytes_POW_LENGTH:
  !ls m. LENGTH ls <= m ==> unbytes ls < 256 ** m
Proof
  rw[unbytes_def]
  >> irule LESS_LESS_EQ_TRANS
  >> irule_at Any l2n_lt
  >> fs[]
QED

Theorem bytes_unbytes:
  !m ls. unbytes ls < 256 ** m /\ LENGTH ls = m
  ==> TAKE m $ PAD_LEFT 0w m $ bytes $ unbytes ls = ls
Proof
  rw[unbytes_def,bytes_thm,MAP_REVERSE]
  >> qmatch_goalsub_abbrev_tac `l2n _ ll`
  >> `1 < 256` by decide_tac
  >> `EVERY ($> 256) ll` by (
    unabbrev_all_tac
    >> fs[EVERY_MAP,arithmeticTheory.GREATER_DEF]
    >> REWRITE_TAC[GSYM dimword_8]
    >> fs[w2n_lt]
  )
  >> dxrule_all numposrepTheory.n2l_l2n
  >> unabbrev_all_tac
  >> CASE_TAC
  >- (
    rw[]
    >> `0 < 256` by decide_tac
    >> dxrule_then (fs o single) l2n_eq_0
    >> fs[EVERY_MAP,arithmeticTheory.GREATER_DEF,w2n_MOD_eq,EVERY_MEM]
    >> ONCE_REWRITE_TAC[LIST_EQ_REWRITE]
    >> fs[LENGTH_TAKE,length_pad_left,EL_TAKE,PAD_LEFT,EL_APPEND_EQN,EL_MEM,COND_RAND,COND_RATOR]
    >> fs[DISJ_EQ_IMP,AND_IMP_INTRO,NOT_LESS,GSYM ADD1]
    >> dsimp[LESS_OR_EQ]
  )
  >> disch_then kall_tac
  >> qmatch_goalsub_abbrev_tac `MAP _ $ TAKE n _`
  >> simp[MAP_TAKE,MAP_REVERSE,n2w_w2n,MAP_MAP_o,o_DEF]
  >> `n <= LENGTH ls` by (
    unabbrev_all_tac
    >> irule LOG_SUC_LESS_EQ
    >> fs[]
  )
  >> fs[TAKE_REVERSE]
  >> `EVERY ($= 0w) $ TAKE ((LENGTH ls) - n) ls` by (
    drule_at_then Any irule bytes_unbytes_special
    >> fs[]
  )
  >> qspecl_then [`n`,`(LENGTH ls) - n`,`ls`] mp_tac APPEND_TAKE_LASTN
  >> impl_tac >- fs[]
  >> disch_then $ CONV_TAC o RHS_CONV o ONCE_REWRITE_CONV o single o GSYM
  >> fs[PAD_LEFT,TAKE_LENGTH_ID_rwt,LENGTH_LASTN]
  >> ONCE_REWRITE_TAC[LIST_EQ_REWRITE]
  >> fs[MEM_EL,PULL_EXISTS,EVERY_MEM]
QED

(* encoding of number as list of words (least significant bit first) *)

Definition n2ws_def[nocompute]:
  n2ws (n : num) : 'a word list =
    if n = 0 then [0w :'a word]
    else
      let
        md = n MOD (dimword(:'a));
        dv = n DIV (dimword(:'a))
      in
        n2w md :: if dv = 0 then [] else n2ws dv
Termination
  WF_REL_TAC `measure I`
  >> fs[arithmeticTheory.NOT_ZERO_LT_ZERO]
End

Theorem n2ws_eq_n2l:
  !n. 2 <= dimword(:'a) ==> n2ws n : 'a word list = MAP n2w $ n2l (dimword (:'a)) n
Proof
  completeInduct_on `n` >> strip_tac
  >> fs[]
  >> simp[Once n2ws_def]
  >> BasicProvers.TOP_CASE_TAC
  >> fs[]
  >- (qexists_tac `0` >> fs[Once numposrepTheory.n2l_def])
  >> BasicProvers.TOP_CASE_TAC >> fs[]
  >- (
    fs[Once numposrepTheory.n2l_def]
    >> BasicProvers.TOP_CASE_TAC
    >> fs[NOT_LESS,DIV_EQ_0]
  )
  >> CONV_TAC $ RAND_CONV $ ONCE_REWRITE_CONV[numposrepTheory.n2l_def]
  >> BasicProvers.TOP_CASE_TAC >> gs[NOT_LESS,DIV_EQ_0]
QED

Theorem n2ws_eq_n2l' = REWRITE_RULE[TWO, GSYM LESS_EQ,ONE_LT_dimword] n2ws_eq_n2l

Theorem n2ws_eq_REVERSE_n2lA:
  n2ws : num -> 'a word list = REVERSE o n2lA [] n2w (dimword (:'a))
Proof
  fs[numposrepTheory.n2lA_n2l,FUN_EQ_THM,n2ws_eq_n2l',MAP_REVERSE]
QED

Theorem n2ws_word1_thm[compute]:
  !n. n2ws n : word1 list =
    if n = 0 then [0w]
    else
      n2w (n MOD 2) :: if n DIV 2 = 0 then [] else n2ws (n DIV 2)
Proof
  Induct using (INST_TYPE [alpha |-> ``:1``] n2ws_ind)
  >> qmatch_asmsub_rename_tac `n <> 0`
  >> Cases_on `n`
  >> ONCE_REWRITE_TAC[SimpLHS,n2ws_def]
  >> fs[wordsTheory.dimword_1]
QED

(*
EVAL`` (n2ws (256)) : word1 list``
*)

Theorem n2ws_word8_thm[compute]:
  !n. n2ws n : word8 list =
    if n = 0 then [0w]
    else
      n2w (n MOD 256) :: if n DIV 256 = 0 then [] else n2ws (n DIV 256)
Proof
  Induct using (INST_TYPE [alpha |-> ``:8``] n2ws_ind)
  >> qmatch_asmsub_rename_tac `n <> 0`
  >> Cases_on `n`
  >> ONCE_REWRITE_TAC[SimpLHS,n2ws_def]
  >> fs[wordsTheory.dimword_8]
QED

(*
EVAL`` (n2ws (259)) : word8 list``
*)

Definition ws2n_acc_def[nocompute]:
  ws2n_acc (mul : num) (acc : num) (ls : ('a word) list) =
    case ls of
    | [] => acc
    | l::ls =>
      ws2n_acc (mul * dimword(:'a)) (acc + (w2n l) * mul) ls
End

Theorem ws2n_acc_eq:
  !mul acc ls.
  ws2n_acc mul acc (ls : 'a word list) =
    acc +
    (SUM $ MAP (λ(x,y :num). x * y) $
      ZIP (MAP w2n ls,
        (GENLIST (λn. mul * FUNPOW (λx. x * dimword(:'a)) n 1)
          (LENGTH ls))))
Proof
  qabbrev_tac `P = λmul acc ls.
    ws2n_acc mul acc (ls : 'a word list) =
      acc +
      (SUM $ MAP (λ(x,y :num). x * y) $
        ZIP (MAP w2n ls,
          (GENLIST (λn. mul * FUNPOW (λx. x * dimword(:'a)) n 1)
            (LENGTH ls))))`
  >> qspec_then `P` mp_tac ws2n_acc_ind
  >> reverse impl_tac >- metis_tac[]
  >> ntac 2 gen_tac >> Cases >> rw[Abbr`P`]
  >> simp[Once ws2n_acc_def]
  >> simp[listTheory.GENLIST_CONS,combinTheory.o_DEF]
  >> ntac 3 (MK_COMB_TAC >> fs[])
  >> rw[listTheory.GENLIST_FUN_EQ,arithmeticTheory.FUNPOW_SUC]
QED

Definition ws2n_def:
  ws2n ls = ws2n_acc 1 0 ls
End

Theorem ws2n_l2n_eq:
  !x. ws2n x = l2n (dimword (:'a)) $ MAP w2n (x : 'a word list)
Proof
  Induct >> fs[ws2n_def,ws2n_acc_eq,numposrepTheory.l2n_def]
  >> gen_tac
  >> fs[GENLIST_CONS,wordsTheory.w2n_lt]
  >> qmatch_goalsub_abbrev_tac `a + w2n h = w2n h + b`
  >> qsuff_tac `a = b` >> fs[Abbr`a`,Abbr`b`]
  >> pop_assum $ ONCE_REWRITE_TAC o single o GSYM
  >> fs[SUM_MAP_MULT,MAP_MAP_o,o_DEF,FUNPOW_SUC]
  >> MK_COMB_TAC >- fs[]
  >> irule LIST_EQ
  >> rw[EL_MAP,LAMBDA_PROD,EL_ZIP]
QED

Theorem ws2n_zero:
  !x. ws2n $ SNOC 0w x = ws2n x
Proof
  fs[ws2n_l2n_eq,l2n_SNOC_0,MAP_SNOC]
QED

Theorem ws2n_dropWhile:
  !x. ws2n $ REVERSE $ dropWhile ($=0w) $ REVERSE x = ws2n x
Proof
  fs[ws2n_l2n_eq,l2n_dropWhile_0,MAP_REVERSE,MAP_dropWhile_inj_w2n]
QED

Theorem ws2n_acc_word8_thm[compute]:
  !mul acc ls.
  ws2n_acc (mul : num) (acc : num) (ls : word8 list) =
    case ls of
    | [] => acc
    | l::ls =>
      ws2n_acc (mul * 256) (acc + (w2n l) * mul) ls
Proof
  ho_match_mp_tac (INST_TYPE [alpha |-> ``:8``] ws2n_acc_ind)
  >> rpt strip_tac
  >> qmatch_asmsub_rename_tac `ls : word8 list`
  >> Cases_on `ls`
  >> ONCE_REWRITE_TAC[SimpLHS,ws2n_acc_def]
  >> fs[wordsTheory.dimword_8]
QED

(*
ws2n_acc (dimword (:α)) (x MOD dimword (:α)) (n2ws (x DIV dimword (:α))) =
ws2n_acc 1 0 (n2ws (x DIV dimword (:α))) * dimword (:α) + x MOD dimword (:α)
*)

Theorem ws2n_acc_thm:
  !mul acc ls. ws2n_acc mul acc ls = mul * ws2n_acc 1 0 ls + acc
Proof
  rpt strip_tac
  >> fs[ws2n_acc_eq]
  >> qmatch_goalsub_abbrev_tac `FUNPOW f`
  >> fs[SUM_MAP_MULT]
  >> MK_COMB_TAC >> fs[listTheory.MAP_MAP_o]
  >> rw[Once listTheory.LIST_EQ_REWRITE]
  >> fs[listTheory.EL_MAP,pairTheory.ELIM_UNCURRY,listTheory.EL_ZIP]
QED

Theorem ws2n_eq_l2n:
  !ls. ws2n (ls : 'a word list) = l2n (dimword (:'a)) $ MAP w2n ls
Proof
  gen_tac
  >> completeInduct_on `LENGTH ls`
  >> rpt strip_tac
  >> gs[PULL_FORALL,ws2n_def]
  >> Cases_on `ls`
  >- simp[ws2n_acc_def,l2n_def]
  >> simp[Once ws2n_acc_def,l2n_def,ws2n_acc_thm]
  >> fs[w2n_lt,LESS_MOD]
QED

(*
EVAL``ws2n (n2ws 0 : word8 list)   ``
EVAL``ws2n (n2ws 1 : word8 list)   ``
EVAL``ws2n (n2ws 256 : word8 list)   ``
EVAL``ws2n (n2ws 257 : word8 list)   ``
EVAL``ws2n ([0w;1w] ++ GENLIST (λx. 0w) 4 : word8 list)   ``
*)

Theorem ws2n_n2ws:
  !x. ws2n (n2ws x) = x
Proof
  completeInduct_on `x`
  >> Cases_on `x = 0`
  >- (
    ONCE_REWRITE_TAC[n2ws_def]
    >> fs[]
    >> fs[ws2n_def,ws2n_acc_def]
  )
  >> ONCE_REWRITE_TAC[n2ws_def]
  >> simp[ws2n_def,Once ws2n_acc_def]
  >> rw[]
  >- (
    fs[Once ws2n_acc_def]
    >> fs[wordsTheory.ONE_LT_dimword,arithmeticTheory.DIV_EQ_0]
  )
  >> fs[ws2n_def]
  >> `x DIV dimword (:'a) < x` by (
    fs[wordsTheory.ONE_LT_dimword,arithmeticTheory.DIV_LESS]
  )
  >> qspecl_then [`dimword(:'a)`,`x`] mp_tac $
    cj 1 $ Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,FORALL_AND_THM]
      $ MP_CANON arithmeticTheory.DIVISION
  >> impl_tac >- fs[wordsTheory.ONE_LT_dimword]
  >> first_x_assum drule
  >> metis_tac[ws2n_acc_thm,arithmeticTheory.MULT_COMM]
QED

(*
EVAL``n2ws $ ws2n ([0w;1w] :word8 list)``
EVAL``n2ws 257 : word8 list``
EVAL `` 0w = (256w  : word8)``
*)

Theorem n2ws_ws2n_zeros:
  !x. EVERY ($=0) $ MAP w2n x
  ==> n2ws $ ws2n (x :'a word list) = [0w] :'a word list
Proof
  fs[ws2n_l2n_eq,n2ws_eq_n2l']
  >> rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `l2n _ ls`
  >> qspecl_then [`dimword(:'a)`,`ls`] mp_tac n2l_l2n
  >> impl_tac >- fs[GREATER_DEF,EVERY_MEM,EVERY_MAP,w2n_lt]
  >> fs[] >> disch_then kall_tac
  >> unabbrev_all_tac
  >> fs[l2n_eq_0,C_DEF,o_DEF,EVERY_MAP,w2n_lt]
QED

Theorem n2ws_ws2n_non_zero:
  !x. EXISTS ($<>0) $ MAP w2n x
  ==>
  (n2ws $ ws2n (x :'a word list)) :'a word list
  = REVERSE $ dropWhile ($=(0w :'a word)) $ REVERSE x
Proof
  rpt strip_tac
  >> ONCE_REWRITE_TAC[GSYM ws2n_dropWhile]
  >> fs[ws2n_l2n_eq,n2ws_eq_n2l']
  >> qmatch_goalsub_abbrev_tac `l2n _ $ MAP _ ls'`
  >> qmatch_goalsub_abbrev_tac `l2n _ ls`
  >> qspecl_then [`dimword(:'a)`,`ls`] mp_tac n2l_l2n
  >> qunabbrev_tac `ls`
  >> impl_tac >- fs[GREATER_DEF,EVERY_MEM,EVERY_MAP,w2n_lt]
  >> fs[l2n_eq_0,EVERY_MAP,EXISTS_MAP]
  >> disch_then kall_tac
  >> fs[C_DEF,o_DEF,EVERY_MAP,w2n_lt]
  >> REWRITE_TAC[EVERY_NOT_EXISTS]
  >> CONV_TAC $ DEPTH_CONV BETA_CONV
  >> qmatch_goalsub_abbrev_tac `COND (~c)`
  >> `c` by (
    unabbrev_all_tac
    >> fs[EXISTS_REVERSE]
    >> qmatch_goalsub_abbrev_tac `EXISTS P $ dropWhile _ ls`
    >> qspecl_then [`P`,`ls`] mp_tac EXISTS_dropWhile
    >> unabbrev_all_tac
    >> fs[EXISTS_REVERSE,o_DEF]
    >> qmatch_goalsub_abbrev_tac `EXISTS _ $ dropWhile P ls ==> EXISTS _ $ dropWhile P' ls`
    >> qsuff_tac `P=P'` >- fs[]
    >> unabbrev_all_tac
    >> fs[FUN_EQ_THM]
  )
  >> asm_rewrite_tac[]
  >> fs[MAP_TAKE,MAP_MAP_o,n2w_w2n,o_DEF,TAKE_LENGTH_ID_rwt2]
  >> qmatch_goalsub_abbrev_tac `l2n b ls`
  >> qspecl_then [`b`,`ls`] mp_tac LOG_l2n_dropWhile
  >> unabbrev_all_tac
  >> impl_tac >- fs[GREATER_DEF,EVERY_MEM,EVERY_MAP,w2n_lt,EXISTS_MAP]
  >> fs[] >> disch_then kall_tac
  >> fs[GSYM MAP_REVERSE,GSYM MAP_dropWhile_inj_w2n,dropWhile_idem]
QED

Theorem n2ws_ws2n:
  !x. (n2ws $ ws2n (x :'a word list)) :'a word list
  = if EXISTS ($<>0w) x then REVERSE $ dropWhile ($=0w) $ REVERSE x else [0w]
Proof
  fs[COND_RAND,EXISTS_MAP,n2ws_ws2n_non_zero,DISJ_EQ_IMP,o_DEF,EVERY_MAP,n2ws_ws2n_zeros]
QED

val _ = export_theory ();
