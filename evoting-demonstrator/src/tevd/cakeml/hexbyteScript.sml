open HolKernel boolLib bossLib Parse;
open arithmeticTheory wordsTheory rich_listTheory listTheory

val _ = new_theory "hexbyte";

(*
    function hexbyte(b) {
        const digits = "0123456789abcdef";
        return digits[b >> 4 & 0xF] + digits[b & 0xF];
    }
    function byteArrayToHex(bytes) {
        let hexString = "";
        for (i = 0; i < bytes.length; i++) {
            hexString += hexbyte(bytes[i]);
        }
        return hexString;
    }
*)

Definition hexbyteLE_def:
  hexbyteLE (b : word8) =
  let m = 2 ** 4 in
    let b = w2n b in [b MOD m; b DIV m]
End

(* little-endian *)
Theorem hexbyteLE_eq_n2l:
  hexbyteLE x = if w2n x < 16 then [w2n x; 0n] else n2l 16 $ w2n x
Proof
  fs[hexbyteLE_def,FUN_EQ_THM,Once numposrepTheory.n2l_def]
  >> rename1`w2n x`
  >> Cases_on `w2n x < 16`
  >> fs[DIV_EQ_0]
  >> once_rewrite_tac[numposrepTheory.n2l_def]
  >> qmatch_goalsub_abbrev_tac `COND c _ _`
  >> qsuff_tac `c` >- fs[]
  >> unabbrev_all_tac
  >> fs[DIV_LT_X]
  >> once_rewrite_tac[GSYM dimword_8]
  >> fs[w2n_lt]
QED

(*
EVAL `` hexbyteLE 118w ``
⊢ hexbyteLE 118w = [118 MOD 16; 118 DIV 16] = [6; 7;]
*)

Theorem hexbyteLE_LENGTH:
  LENGTH $ hexbyteLE x = 2
Proof
  fs[hexbyteLE_def]
QED

Theorem hexbyteLE_EVERY:
  !x. EVERY ($> 16) $ hexbyteLE x
Proof
  gen_tac
  >> fs[hexbyteLE_eq_n2l]
  >> rename1`w2n x`
  >> Cases_on `w2n x < 16`
  >> fs[numposrepTheory.n2l_BOUND]
QED

Definition hexbyteBE_def:
  hexbyteBE (b : word8) =
  let m = 2 ** 4 in
    let b = w2n b in [b DIV m; b MOD m]
End

(* big-endian *)
Theorem hexbyteBE_eq_n2l:
  hexbyteBE x = if w2n x < 16 then [0n; w2n x] else REVERSE $ n2l 16 $ w2n x
Proof
  fs[hexbyteBE_def,FUN_EQ_THM,Once numposrepTheory.n2l_def]
  >> rename1`w2n x`
  >> Cases_on `w2n x < 16`
  >> fs[DIV_EQ_0]
  >> once_rewrite_tac[numposrepTheory.n2l_def]
  >> qmatch_goalsub_abbrev_tac `COND c _ _`
  >> qsuff_tac `c` >- fs[]
  >> unabbrev_all_tac
  >> fs[DIV_LT_X]
  >> once_rewrite_tac[GSYM dimword_8]
  >> fs[w2n_lt]
QED

Theorem hexbyteBE_LENGTH:
  LENGTH $ hexbyteBE x = 2
Proof
  fs[hexbyteBE_def]
QED

Theorem hexbyteBE_EVERY:
  !x. EVERY ($> 16) $ hexbyteBE x
Proof
  gen_tac
  >> fs[hexbyteBE_eq_n2l]
  >> rename1`w2n x`
  >> Cases_on `w2n x < 16`
  >> fs[numposrepTheory.n2l_BOUND]
QED

Definition byteArrayToHexLE_def:
  byteArrayToHexLE (b : word8 list) = FLAT $ MAP hexbyteLE b
End

Theorem byteArrayToHexLE_LENGTH:
  !b. LENGTH $ byteArrayToHexLE b = 2 * LENGTH b
Proof
  Induct >> fs[byteArrayToHexLE_def,hexbyteLE_LENGTH]
QED

Theorem byteArrayToHexLE_EVERY:
  !b. EVERY ($> 16) $ byteArrayToHexLE b
Proof
  fs[byteArrayToHexLE_def,EVERY_FLAT,EVERY_MAP,hexbyteLE_EVERY]
QED

Definition byteArrayToHexBE_def:
  byteArrayToHexBE (b : word8 list) = FLAT $ MAP hexbyteBE b
End

Theorem byteArrayToHexBE_LENGTH:
  !b. LENGTH $ byteArrayToHexBE b = 2 * LENGTH b
Proof
  Induct >> fs[byteArrayToHexBE_def,hexbyteBE_LENGTH]
QED

Theorem byteArrayToHexBE_EVERY:
  !b. EVERY ($> 16) $ byteArrayToHexBE b
Proof
  fs[byteArrayToHexBE_def,EVERY_FLAT,EVERY_MAP,hexbyteBE_EVERY]
QED

Definition take_map_def:
  take_map 0 _ _ = [] (* only for totality *)
  /\ take_map (SUC n) f [] = []
  /\ take_map (SUC n) f ls =
    ((f (TAKE (SUC n) ls)) :: (take_map (SUC n) f $ DROP (SUC n) ls))
Termination
  WF_REL_TAC `measure $ LENGTH o SND o SND` >> fs[]
End

Theorem take_map_thm:
  !n f ls. 0 < n ==>
  take_map n f ls =
    if NULL ls then [] else
    ((f (TAKE n ls)) :: (take_map n f $ DROP n ls))
Proof
  Cases >> fs[]
  >> qmatch_goalsub_rename_tac `SUC n`
  >> qid_spec_tac `n`
  >> ho_match_mp_tac take_map_ind
  >> conj_tac
  >- (gen_tac >> Cases >> fs[take_map_def])
  >> conj_tac
  >- fs[take_map_def]
  >> fs[take_map_def]
QED

Theorem take_map_thm1:
  !n f ls. 0 < n /\ ~NULL ls ==>
  take_map n f ls = ((f (TAKE n ls)) :: (take_map n f $ DROP n ls))
Proof
  fs[Once take_map_thm]
QED

Theorem take_map_all:
  !n f ls. 0 < n /\ n = LENGTH ls ==>
  take_map n f ls = [f ls]
Proof
  fs[Once take_map_thm,NULL_EQ]
  >> rw[DROP_LENGTH_NIL,take_map_thm]
QED

Definition bytehexLE_def:
  bytehexLE [x;y] = [n2w $ y * (2 ** 4) + x] : word8 list
  /\ bytehexLE _ = []
End

Theorem bytehexLE_len:
  !ls. LENGTH ls = 2 ==> ?x. bytehexLE ls = [x]
Proof
  qx_gen_tac `ls` >> Cases_on `ls` >> fs[]
  >> rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> fs[bytehexLE_def]
QED

Theorem bytehexLE_eq_l2n:
  EVERY ($> 16) ls /\ LENGTH ls = 2
  ==> bytehexLE ls = [n2w $ l2n 16 ls]
Proof
  rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> fs[numposrepTheory.l2n_def,bytehexLE_def]
QED

Theorem bytehexLE_hexbyteLE:
  bytehexLE (hexbyteLE b) = [b]
Proof
  fs[hexbyteLE_LENGTH,hexbyteLE_EVERY,bytehexLE_eq_l2n,hexbyteLE_eq_n2l]
  >> qmatch_goalsub_abbrev_tac `COND c`
  >> Cases_on `c` >> fs[numposrepTheory.l2n_def]
  >> fs[numposrepTheory.l2n_n2l]
QED

Theorem hexbyteLE_bytehexLE:
  !b. EVERY ($> 16) b /\ LENGTH b = 2
  ==> hexbyteLE $ HD $ bytehexLE b = b
Proof
  qx_gen_tac `ls` >> Cases_on `ls` >> fs[]
  >> rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> fs[bytehexLE_def,hexbyteLE_def,GREATER_DEF]
  >> strip_tac
  >> qmatch_goalsub_abbrev_tac `a MOD dimword (:8)`
  >> `a MOD dimword (:8) = a` by (
    unabbrev_all_tac
    >> irule LESS_MOD
    >> fs[dimword_8]
  )
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac
  >> fs[DIV_EQ_0]
QED

Definition bytehexBE_def:
  bytehexBE [x;y] = [n2w $ x * (2 ** 4) + y] : word8 list
  /\ bytehexBE _ = []
End

Theorem bytehexBE_len:
  !ls. LENGTH ls = 2 ==> ?x. bytehexBE ls = [x]
Proof
  qx_gen_tac `ls` >> Cases_on `ls` >> fs[]
  >> rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> fs[bytehexBE_def]
QED

Theorem bytehexBE_eq_l2n:
  EVERY ($> 16) ls /\ LENGTH ls = 2
  ==> bytehexBE ls = [n2w $ l2n 16 $ REVERSE ls]
Proof
  rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> fs[numposrepTheory.l2n_def,bytehexBE_def]
QED

Theorem bytehexBE_hexbyteBE:
  bytehexBE (hexbyteBE b) = [b]
Proof
  fs[hexbyteBE_LENGTH,hexbyteBE_EVERY,bytehexBE_eq_l2n,hexbyteBE_eq_n2l]
  >> qmatch_goalsub_abbrev_tac `COND c`
  >> Cases_on `c` >> fs[numposrepTheory.l2n_def]
  >> fs[numposrepTheory.l2n_n2l]
QED

Theorem hexbyteBE_bytehexBE:
  !b. EVERY ($> 16) b /\ LENGTH b = 2
  ==> hexbyteBE $ HD $ bytehexBE b = b
Proof
  qx_gen_tac `ls` >> Cases_on `ls` >> fs[]
  >> rename1 `LENGTH ls` >> Cases_on `ls` >> fs[]
  >> fs[bytehexBE_def,hexbyteBE_def,GREATER_DEF]
  >> strip_tac
  >> qmatch_goalsub_abbrev_tac `a MOD dimword (:8)`
  >> `a MOD dimword (:8) = a` by (
    unabbrev_all_tac
    >> irule LESS_MOD
    >> fs[dimword_8]
  )
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac
  >> fs[DIV_EQ_0]
QED

Definition hexToByteArrayLE_def:
  hexToByteArrayLE ls = FLAT $ take_map 2 bytehexLE ls
End

Theorem byteArrayToHexLE_hexToByteArrayLE:
  !ls. EVEN $ LENGTH ls /\ EVERY ($> 16) ls
  ==> byteArrayToHexLE $ hexToByteArrayLE ls = ls
Proof
  qx_gen_tac `ls` >> completeInduct_on `LENGTH ls`
  >> Cases
  >- (
    rewrite_tac[hexToByteArrayLE_def,take_map_def,TWO]
    >> fs[byteArrayToHexLE_def]
  )
  >> rename1`LENGTH $ h::t` >> Cases_on `t` >> fs[]
  >> fs[EVEN]
  >> rw[Once take_map_thm,hexToByteArrayLE_def,byteArrayToHexLE_def]
  >> fs[GSYM hexToByteArrayLE_def,byteArrayToHexLE_def,GREATER_DEF]
  >> qmatch_goalsub_abbrev_tac `bytehexLE a`
  >> qspec_then `a` assume_tac bytehexLE_len
  >> qspec_then `a` assume_tac hexbyteLE_bytehexLE
  >> unabbrev_all_tac
  >> gs[GREATER_DEF]
QED

Theorem hexToByteArrayLE_byteArrayToHexLE:
  !ls. hexToByteArrayLE $ byteArrayToHexLE ls = ls
Proof
  Induct
  >- (
    fs[byteArrayToHexLE_def,hexToByteArrayLE_def]
    >> rewrite_tac[take_map_def,TWO,FLAT]
  )
  >> gen_tac
  >> rw[byteArrayToHexLE_def,hexToByteArrayLE_def,Once take_map_thm]
  >> fs[hexbyteLE_LENGTH,NULL_LENGTH,Excl"LENGTH_NIL"]
  >> fs[GSYM hexToByteArrayLE_def,GSYM byteArrayToHexLE_def,hexbyteLE_LENGTH,TAKE_APPEND,DROP_APPEND,DROP_LENGTH_NIL_rwt,TAKE_LENGTH_ID_rwt]
  >> fs[bytehexLE_hexbyteLE]
QED

Definition hexToByteArrayBE_def:
  hexToByteArrayBE ls = FLAT $ take_map 2 bytehexBE ls
End

Theorem byteArrayToHexBE_hexToByteArrayBE:
  !ls. EVEN $ LENGTH ls /\ EVERY ($> 16) ls
  ==> byteArrayToHexBE $ hexToByteArrayBE ls = ls
Proof
  qx_gen_tac `ls` >> completeInduct_on `LENGTH ls`
  >> Cases
  >- (
    rewrite_tac[hexToByteArrayBE_def,take_map_def,TWO]
    >> fs[byteArrayToHexBE_def]
  )
  >> rename1`LENGTH $ h::t` >> Cases_on `t` >> fs[]
  >> fs[EVEN]
  >> rw[Once take_map_thm,hexToByteArrayBE_def,byteArrayToHexBE_def]
  >> fs[GSYM hexToByteArrayBE_def,byteArrayToHexBE_def,GREATER_DEF]
  >> qmatch_goalsub_abbrev_tac `bytehexBE a`
  >> qspec_then `a` assume_tac bytehexBE_len
  >> qspec_then `a` assume_tac hexbyteBE_bytehexBE
  >> unabbrev_all_tac
  >> gs[GREATER_DEF]
QED

Theorem hexToByteArrayBE_byteArrayToHexBE:
  !ls. hexToByteArrayBE $ byteArrayToHexBE ls = ls
Proof
  Induct
  >- (
    fs[byteArrayToHexBE_def,hexToByteArrayBE_def]
    >> rewrite_tac[take_map_def,TWO,FLAT]
  )
  >> gen_tac
  >> rw[byteArrayToHexBE_def,hexToByteArrayBE_def,Once take_map_thm]
  >> fs[hexbyteBE_LENGTH,NULL_LENGTH,Excl"LENGTH_NIL"]
  >> fs[GSYM hexToByteArrayBE_def,GSYM byteArrayToHexBE_def,hexbyteBE_LENGTH,TAKE_APPEND,DROP_APPEND,DROP_LENGTH_NIL_rwt,TAKE_LENGTH_ID_rwt]
  >> fs[bytehexBE_hexbyteBE]
QED


(* conversion from/to string *)

Definition hexint_to_string_def:
  hexint_to_string alph x = oEL x alph
End

Theorem hexint_to_string_some:
  IS_SOME $ hexint_to_string alph x <=> x < LENGTH alph
Proof
  fs[oEL_THM,hexint_to_string_def,COND_RAND]
QED

Theorem hexint_to_string_MEM:
  hexint_to_string alpha x = SOME y <=> x < LENGTH alpha /\ EL x alpha = y
Proof
  csimp[hexint_to_string_def,oEL_THM]
QED

Definition string_to_hexint_def:
  string_to_hexint alph x = INDEX_OF x alph
End

Theorem string_to_hexint_some:
  ALL_DISTINCT alph ==> IS_SOME $ string_to_hexint alph x = MEM x alph
Proof
  rw[string_to_hexint_def]
  >> rename1 `MEM x alph`
  >> Cases_on `MEM x alph` >> fs[GSYM INDEX_OF_eq_NONE]
  >> fs[MEM_EL,ALL_DISTINCT_INDEX_OF_EL]
QED

Theorem string_to_hexint_some2:
  ALL_DISTINCT alph /\ string_to_hexint alph x = SOME y
  ==> y < LENGTH alph /\ EL y alph = x
Proof
  rw[string_to_hexint_def,INDEX_OF_eq_SOME]
QED

Definition until_none_def:
  until_none f = FOLDL (λe x. OPTION_MAP2 (λx e. SNOC x e) (f x) e) (SOME [])
End

Theorem FOLDL_OPTION_MAP2_NONE:
  !f f' ls. FOLDL (λe x. OPTION_MAP2 f (f' x) e) NONE ls = NONE
Proof
  ntac 2 gen_tac >> Induct >> fs[FOLDL_FOLDR_REVERSE,optionTheory.OPTION_MAP2_DEF]
QED

Theorem FOLDL_OPTION_MAP2_IS_PREFIX:
  !x s f x'.
  FOLDL (λe x. OPTION_MAP2 (λx e. e ++ [x]) (f x) e) (SOME s) x = SOME x'
  ==> IS_PREFIX x' s
Proof
  Induct >> rw[]
  >> Cases_on `f h` >> fs[FOLDL_OPTION_MAP2_NONE]
  >> first_x_assum $ drule_then assume_tac
  >> drule_then irule IS_PREFIX_APPEND1
QED

Theorem FOLDL_OPTION_MAP2_acc:
  !f acc x x'.
  FOLDL (λe x. OPTION_MAP2 (λx e. e ++ [x]) (f x) e) (SOME $ acc) x = SOME $ acc++x'
  ==> FOLDL (λe x. OPTION_MAP2 (λx e. e ++ [x]) (f x) e) (SOME []) x = SOME $ x'
Proof
  ntac 2 gen_tac
  >> fs[FOLDL_FOLDR_REVERSE]
  >> Induct using SNOC_INDUCT >- fs[NULL_EQ]
  >> rw[]
  >> gvs[REVERSE_SNOC]
  >> fs[FOLDR_FOLDL_REVERSE]
  >> imp_res_tac FOLDL_OPTION_MAP2_IS_PREFIX
  >> gvs[IS_PREFIX_APPEND]
QED

Theorem FOLDL_OPTION_MAP2_acc2:
  !f acc x x'.
  FOLDL (λe x. OPTION_MAP2 (λx e. e ++ [x]) (f x) e) (SOME []) x = SOME $ x'
  ==> FOLDL (λe x. OPTION_MAP2 (λx e. e ++ [x]) (f x) e) (SOME $ acc) x = SOME $ acc++x'
Proof
  ntac 2 gen_tac
  >> fs[FOLDL_FOLDR_REVERSE]
  >> Induct using SNOC_INDUCT >- fs[NULL_EQ]
  >> rw[]
  >> gvs[REVERSE_SNOC]
QED

Theorem until_none_some:
  !ls. IS_SOME $ until_none f ls <=> EVERY (IS_SOME o f) ls
Proof
  Induct >> rewrite_tac[until_none_def] >- fs[]
  >> qx_gen_tac `h` >> Cases_on `f h`
  >- fs[FOLDL_OPTION_MAP2_NONE]
  >> rw[EQ_IMP_THM]
  >- (
    qpat_x_assum `_ <=> _` $ rewrite_tac o single o GSYM
    >> fs[optionTheory.IS_SOME_EXISTS,SNOC_APPEND]
    >> imp_res_tac FOLDL_OPTION_MAP2_IS_PREFIX
    >> rename1`FOLDL _ _ _ = SOME x'` >> Cases_on `x'`
    >> fs[IS_PREFIX_APPEND]
    >> qmatch_asmsub_abbrev_tac `FOLDL _ (SOME acc) ls`
    >> qspecl_then [`f`,`acc`,`ls`] assume_tac FOLDL_OPTION_MAP2_acc
    >> unabbrev_all_tac
    >> gs[until_none_def,SNOC_APPEND]
  )
  >> gvs[optionTheory.IS_SOME_EXISTS,until_none_def,SNOC_APPEND]
  >> drule_then (irule_at Any) FOLDL_OPTION_MAP2_acc2
QED

Theorem until_none_EVERY =
  Ho_Rewrite.REWRITE_RULE[PULL_EXISTS,optionTheory.IS_SOME_EXISTS]
  $ iffLR until_none_some

Theorem until_none_LENGTH:
  !f ls. EVERY (IS_SOME o f) ls
  ==> LENGTH $ THE $ until_none f ls = LENGTH ls
Proof
  gen_tac >> fs[FOLDL_FOLDR_REVERSE,until_none_def]
  >> Induct using SNOC_INDUCT >- fs[NULL_EQ]
  >> rw[]
  >> gvs[REVERSE_SNOC]
  >> gvs[FOLDR_FOLDL_REVERSE]
  >> qmatch_goalsub_abbrev_tac `OPTION_MAP2 _ _ foldl`
  >> `IS_SOME foldl` by (
    unabbrev_all_tac >> fs[until_none_some,GSYM until_none_def,SNOC_APPEND]
  )
  >> unabbrev_all_tac
  >> gvs[optionTheory.IS_SOME_EXISTS,optionTheory.OPTION_MAP2_THM,SNOC_APPEND]
QED

Theorem until_none_EL:
  !f i ls ls'. until_none f ls = SOME ls'
  /\ i < LENGTH ls
  ==> IS_SOME $ f $ EL i ls /\ EL i ls' = THE $ f $ EL i ls
Proof
  ntac 2 gen_tac >> fs[FOLDL_FOLDR_REVERSE,until_none_def]
  >> Induct using SNOC_INDUCT >- fs[NULL_EQ]
  >> rpt gen_tac >> strip_tac
  >> gvs[REVERSE_SNOC]
  >> gvs[FOLDR_FOLDL_REVERSE,GSYM until_none_def]
  >> fs[prim_recTheory.LESS_THM,SNOC_APPEND]
  >> imp_res_tac until_none_EVERY
  >> imp_res_tac until_none_LENGTH
  >> gvs[EL_LENGTH_APPEND_rwt,EL_APPEND1]
QED

Definition stringlist_to_hexintlist_def:
  stringlist_to_hexintlist alph = until_none $ string_to_hexint alph
End

Theorem stringlist_to_hexintlist_some:
  ALL_DISTINCT alph
  ==> IS_SOME $ stringlist_to_hexintlist alph ls = EVERY (λx. MEM x alph) ls
Proof
  fs[stringlist_to_hexintlist_def,until_none_some,combinTheory.o_DEF,string_to_hexint_some]
QED

Theorem stringlist_to_hexintlist_el:
  ALL_DISTINCT alpha
  /\ stringlist_to_hexintlist alpha ls = SOME ls'
  ==> EVERY (λx. x < LENGTH alpha) ls'
Proof
  rw[stringlist_to_hexintlist_def,EVERY_EL]
  >> imp_res_tac until_none_EVERY
  >> imp_res_tac until_none_LENGTH
  >> gs[]
  >> dxrule until_none_EL
  >> disch_then $ drule_then strip_assume_tac
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> imp_res_tac string_to_hexint_some2
QED

Theorem stringlist_to_hexintlist_LENGTH:
  stringlist_to_hexintlist alpha ls = SOME ls'
  ==> LENGTH ls = LENGTH ls'
Proof
  rw[stringlist_to_hexintlist_def]
  >> imp_res_tac until_none_EVERY
  >> imp_res_tac until_none_LENGTH
  >> gs[]
QED

Theorem stringlist_to_hexintlist_EVERY:
  ALL_DISTINCT alpha
  /\ stringlist_to_hexintlist alpha ls = SOME ls'
  ==> EVERY ($> $ LENGTH alpha) ls'
Proof
  rw[stringlist_to_hexintlist_def]
  >> imp_res_tac until_none_EVERY
  >> imp_res_tac until_none_LENGTH
  >> gs[EVERY_EL,GREATER_DEF]
  >> rw[]
  >> dxrule until_none_EL
  >> disch_then $ drule_then strip_assume_tac
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> imp_res_tac string_to_hexint_some2
QED

Definition hexintlist_to_stringlist_def:
  hexintlist_to_stringlist alph = until_none $ hexint_to_string alph
End

Theorem hexintlist_to_stringlist_some:
  IS_SOME $ hexintlist_to_stringlist alph ls = EVERY (λx. x < LENGTH alph) ls
Proof
  fs[hexintlist_to_stringlist_def,until_none_some,hexint_to_string_some,combinTheory.o_DEF]
QED

Theorem hexintlist_to_stringlist_el:
  hexintlist_to_stringlist alph ls = SOME ls'
  ==> EVERY (λx. MEM x alph) ls'
Proof
  rw[hexintlist_to_stringlist_def,EVERY_EL]
  >> imp_res_tac until_none_EVERY
  >> imp_res_tac until_none_LENGTH
  >> gs[]
  >> dxrule until_none_EL
  >> disch_then $ drule_then strip_assume_tac
  >> imp_res_tac $ iffLR hexint_to_string_some
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> imp_res_tac $ iffLR hexint_to_string_MEM
  >> gvs[MEM_EL]
  >> irule_at Any EQ_SYM
  >> goal_assum $ drule_all
QED

Theorem hexintlist_to_stringlist_LENGTH:
  hexintlist_to_stringlist alpha ls = SOME ls'
  ==> LENGTH ls = LENGTH ls'
Proof
  rw[hexintlist_to_stringlist_def]
  >> imp_res_tac until_none_EVERY
  >> imp_res_tac until_none_LENGTH
  >> gs[]
QED

Theorem h2s_s2h:
  ALL_DISTINCT alpha
  /\ EVERY (λx. MEM x alpha) ls
  ==> hexintlist_to_stringlist alpha $ THE $ stringlist_to_hexintlist alpha ls = SOME ls
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `hexintlist_to_stringlist _ $ THE $ s2h = _`
  >> qmatch_goalsub_abbrev_tac `h2s = _`
  >> `IS_SOME s2h` by (
    unabbrev_all_tac
    >> fs[stringlist_to_hexintlist_some]
  )
  >> `IS_SOME h2s` by (
    unabbrev_all_tac
    >> imp_res_tac $ iffLR stringlist_to_hexintlist_some
    >> rw[hexintlist_to_stringlist_some,EVERY_EL]
    >> gs[EVERY_EL,optionTheory.IS_SOME_EXISTS]
    >> imp_res_tac stringlist_to_hexintlist_el
    >> gs[EVERY_EL]
  )
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> rename1`s2h = SOME x`
  >> rename1`h2s = SOME x'`
  >> `LENGTH x = LENGTH x' /\ LENGTH x = LENGTH ls` by (
    unabbrev_all_tac
    >> imp_res_tac hexintlist_to_stringlist_LENGTH
    >> imp_res_tac stringlist_to_hexintlist_LENGTH
    >> gs[]
  )
  >> qunabbrev_tac `h2s`
  >> fs[hexintlist_to_stringlist_def]
  >> irule LIST_EQ
  >> rw[]
  >> dxrule until_none_EL
  >> fs[]
  >> disch_then $ drule_then strip_assume_tac
  >> fs[stringlist_to_hexintlist_def]
  >> dxrule until_none_EL
  >> fs[]
  >> disch_then $ drule_then strip_assume_tac
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> gvs[hexint_to_string_MEM,string_to_hexint_some2]
QED

Theorem s2h_h2s:
  !ls' ls alpha.
    ALL_DISTINCT alpha
    /\ EVERY (λx. x < LENGTH alpha) ls
    ==> stringlist_to_hexintlist alpha $
      THE $ hexintlist_to_stringlist alpha ls = SOME ls
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `stringlist_to_hexintlist _ $ THE $ h2s = _`
  >> qmatch_goalsub_abbrev_tac `s2h = _`
  >> `IS_SOME h2s` by (
    unabbrev_all_tac
    >> fs[hexintlist_to_stringlist_some]
  )
  >> `IS_SOME s2h` by (
    unabbrev_all_tac
    >> imp_res_tac $ iffLR hexintlist_to_stringlist_some
    >> rw[stringlist_to_hexintlist_some,EVERY_EL]
    >> gs[EVERY_EL,optionTheory.IS_SOME_EXISTS]
    >> imp_res_tac hexintlist_to_stringlist_el
    >> gs[EVERY_EL]
  )
  >> fs[optionTheory.IS_SOME_EXISTS]
  >> rename1`s2h = SOME x'`
  >> rename1`h2s = SOME x`
  >> `LENGTH x = LENGTH x' /\ LENGTH x = LENGTH ls` by (
    unabbrev_all_tac
    >> imp_res_tac hexintlist_to_stringlist_LENGTH
    >> imp_res_tac stringlist_to_hexintlist_LENGTH
    >> gs[]
  )
  >> qunabbrev_tac `h2s`
  >> fs[stringlist_to_hexintlist_def]
  >> irule LIST_EQ
  >> rw[]
  >> dxrule until_none_EL
  >> fs[]
  >> disch_then $ drule_then strip_assume_tac
  >> fs[hexintlist_to_stringlist_def]
  >> dxrule until_none_EL
  >> fs[]
  >> disch_then $ drule_then strip_assume_tac
  >> gvs[optionTheory.IS_SOME_EXISTS]
  >> imp_res_tac string_to_hexint_some2
  >> imp_res_tac $ iffLR hexint_to_string_MEM
  >> gvs[]
  >> dxrule_all ALL_DISTINCT_EL_IMP
  >> fs[]
QED

Definition hexstr_to_bytelistLE_def:
  hexstr_to_bytelistLE alpha = hexToByteArrayLE o THE o stringlist_to_hexintlist alpha
End

Definition bytelist_to_hexstrLE_def:
  bytelist_to_hexstrLE alpha = THE o hexintlist_to_stringlist alpha o byteArrayToHexLE
End

(* the two main correctness results *)

Theorem hexstr_to_bytelistLE_bytelist_to_hexstrLE:
  !alpha.
  ALL_DISTINCT alpha /\ LENGTH alpha = 16
  ==> hexstr_to_bytelistLE alpha o bytelist_to_hexstrLE alpha = I
Proof
  rw[FUN_EQ_THM,combinTheory.o_DEF]
  >> fs[bytelist_to_hexstrLE_def,hexstr_to_bytelistLE_def,hexToByteArrayLE_byteArrayToHexLE]
  >> qmatch_goalsub_abbrev_tac `hexintlist_to_stringlist _ bath`
  >> `EVERY (λx. x < LENGTH alpha) bath` by (
    rename1`byteArrayToHexLE x`
    >> qspec_then `x` mp_tac byteArrayToHexLE_EVERY
    >> unabbrev_all_tac
    >> ho_match_mp_tac $ Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC
    >> fs[GREATER_DEF]
  )
  >> unabbrev_all_tac
  >> fs[s2h_h2s,hexToByteArrayLE_byteArrayToHexLE]
QED

Theorem bytelist_to_hexstrLE_hexstr_to_bytelistLE:
  !alpha ls.
  ALL_DISTINCT alpha /\ LENGTH alpha = 16 /\ EVEN $ LENGTH ls
  /\ EVERY (λx. MEM x alpha) ls
  ==> bytelist_to_hexstrLE alpha (hexstr_to_bytelistLE alpha ls) = ls
Proof
  rpt strip_tac
  >> fs[bytelist_to_hexstrLE_def,hexstr_to_bytelistLE_def,byteArrayToHexLE_hexToByteArrayLE]
  >> qmatch_goalsub_abbrev_tac `hexToByteArrayLE $ THE sl2hl`
  >> `IS_SOME sl2hl /\ LENGTH $ THE sl2hl = LENGTH ls` by (
    unabbrev_all_tac
    >> conj_asm1_tac >- fs[stringlist_to_hexintlist_some]
    >> fs[optionTheory.IS_SOME_EXISTS]
    >> imp_res_tac stringlist_to_hexintlist_LENGTH
    >> fs[]
  )
  >> `byteArrayToHexLE $ hexToByteArrayLE $ THE sl2hl = THE sl2hl` by (
    irule byteArrayToHexLE_hexToByteArrayLE
    >> unabbrev_all_tac
    >> fs[optionTheory.IS_SOME_EXISTS]
    >> imp_res_tac stringlist_to_hexintlist_EVERY
    >> gs[]
  )
  >> unabbrev_all_tac
  >> fs[h2s_s2h]
QED

Definition hexstr_to_bytelistBE_def:
  hexstr_to_bytelistBE alpha ls =
    THE $ OPTION_CHOICE
      (OPTION_MAP hexToByteArrayBE $ stringlist_to_hexintlist alpha ls)
      (SOME [])
End

Definition bytelist_to_hexstrBE_def:
  bytelist_to_hexstrBE alpha ls =
    if ALL_DISTINCT alpha /\ LENGTH alpha = 16
    then THE $ hexintlist_to_stringlist alpha $ byteArrayToHexBE ls
    else []
End

Theorem hexstr_to_bytelistBE_bytelist_to_hexstrBE:
  !alpha.
  ALL_DISTINCT alpha /\ LENGTH alpha = 16
  ==> hexstr_to_bytelistBE alpha o bytelist_to_hexstrBE alpha = I
Proof
  rw[FUN_EQ_THM,combinTheory.o_DEF]
  >> fs[bytelist_to_hexstrBE_def,hexstr_to_bytelistBE_def]
  >> qmatch_goalsub_abbrev_tac `hexintlist_to_stringlist _ bath`
  >> `EVERY (λx. x < LENGTH alpha) bath` by (
    rename1`byteArrayToHexBE x`
    >> qspec_then `x` mp_tac byteArrayToHexBE_EVERY
    >> unabbrev_all_tac
    >> ho_match_mp_tac $ Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC
    >> fs[GREATER_DEF]
  )
  >> unabbrev_all_tac
  >> fs[s2h_h2s,hexToByteArrayBE_byteArrayToHexBE]
QED

Theorem bytelist_to_hexstrBE_hexstr_to_bytelistBE:
  !alpha ls.
  ALL_DISTINCT alpha /\ LENGTH alpha = 16 /\ EVEN $ LENGTH ls
  /\ EVERY (λx. MEM x alpha) ls
  ==> bytelist_to_hexstrBE alpha (hexstr_to_bytelistBE alpha ls) = ls
Proof
  rpt strip_tac
  >> fs[bytelist_to_hexstrBE_def,hexstr_to_bytelistBE_def]
  >> qmatch_goalsub_abbrev_tac `OPTION_MAP _ sl2hl`
  >> `IS_SOME sl2hl /\ LENGTH $ THE sl2hl = LENGTH ls` by (
    unabbrev_all_tac
    >> conj_asm1_tac >- fs[stringlist_to_hexintlist_some]
    >> fs[optionTheory.IS_SOME_EXISTS]
    >> imp_res_tac stringlist_to_hexintlist_LENGTH
    >> fs[]
  )
  >> unabbrev_all_tac
  >> qmatch_goalsub_abbrev_tac `OPTION_CHOICE a b`
  >> `OPTION_CHOICE a b = a` by (
    unabbrev_all_tac
    >> fs[optionTheory.IS_SOME_EXISTS]
  )
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac
  >> qmatch_goalsub_abbrev_tac `byteArrayToHexBE $ THE $ OPTION_MAP hexToByteArrayBE sl2h`
  >> `byteArrayToHexBE $ THE $ OPTION_MAP hexToByteArrayBE sl2h = THE sl2h` by (
    unabbrev_all_tac
    >> fs[optionTheory.IS_SOME_EXISTS]
    >> irule byteArrayToHexBE_hexToByteArrayBE
    >> imp_res_tac stringlist_to_hexintlist_EVERY
    >> gs[]
  )
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac
  >> gs[h2s_s2h]
QED

Definition hex_alphabet_def:
  hex_alphabet = "0123456789ABCDEF"
End

Theorem hex_alphabet_props:
  ALL_DISTINCT hex_alphabet /\ LENGTH hex_alphabet = 16
Proof
  EVAL_TAC
QED

Theorem b2h_h2b_LE_alpha =
  Q.ISPEC `hex_alphabet` bytelist_to_hexstrLE_hexstr_to_bytelistLE
  |> REWRITE_RULE[hex_alphabet_props]

Theorem h2b_b2h_LE_alpha =
  Q.ISPEC `hex_alphabet` hexstr_to_bytelistLE_bytelist_to_hexstrLE
  |> REWRITE_RULE[hex_alphabet_props]

Theorem b2h_h2b_BE_alpha =
  Q.ISPEC `hex_alphabet` bytelist_to_hexstrBE_hexstr_to_bytelistBE
  |> REWRITE_RULE[hex_alphabet_props]

Theorem h2b_b2h_BE_alpha =
  Q.ISPEC `hex_alphabet` hexstr_to_bytelistBE_bytelist_to_hexstrBE
  |> REWRITE_RULE[hex_alphabet_props]

(*
EVAL `` bytelist_to_hexstrBE hex_alphabet [0w; 15w; 255w; 37w; 183w] ``
EVAL `` hexstr_to_bytelistBE hex_alphabet $ FLAT ["FF"; "AB"; "CD"; "E0"; "12"; "34"; "56"; "67"; "90"] ``

EVAL `` bytelist_to_hexstrLE hex_alphabet [0w; 15w; 255w; 37w; 183w] ``
EVAL `` hexstr_to_bytelistLE hex_alphabet $ FLAT ["FF"; "AB"; "CD"; "E0"; "12"; "34"; "56"; "67"; "90"] ``
*)

val _ = export_theory ();
