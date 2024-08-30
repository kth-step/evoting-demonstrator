(*
  Automation of (de)serialisation of algebraic datatypes, combining basic types

  Type of serialisation function for type `'a`
  ```
  :'a -> word8 list option
  ```

  Type of deserialisation function for type `'a`
  ```
  :(word8 list -> ('a # word8 list) option)
  ```

*)

structure serialiseLib :> serialiseLib =
struct

open HolKernel boolLib bossLib Parse;
open serialiseTheory wordsLib wordsSyntax;

val ERR = mk_HOL_ERR "serialiseLib";

fun n2w8 i = wordsSyntax.mk_word (Arbnum.fromInt i, Arbnum.fromInt 8)
val ser_elem_type = type_of $ n2w8 0
(* ``:word8 list`` *)
val deser_in_ty = listSyntax.mk_list_type ser_elem_type;
(* ``:word8 list option`` *)
val ser_out_ty = optionSyntax.mk_option deser_in_ty

(*
ser_default_ty alpha
deser_default_ty alpha
*)
fun ser_default_ty ty = mk_type("fun",[ty,ser_out_ty])
fun deser_default_ty ty = mk_type("fun", [deser_in_ty, optionSyntax.mk_option(pairSyntax.mk_prod(ty,deser_in_ty))])

fun type_name ty = fst $ dest_type ty

(*
val ty = ``:bool -> num -> mlstring``
dest_fun_ty ty
list_mk_fun $ strip_fun ty
*)
(* destructs 'a -> 'b -> 'c to list ['a,'b,'c] *)
fun dest_fun_ty ty = case dest_type ty of
    ("fun",dom::rng::[]) => dom ::
      (if can dest_fun_ty rng then dest_fun_ty rng else [])
  | _ => [ty]

fun lookup _ [] _ = NONE
  | lookup eq ((key, value)::xs) key' =
      if eq (key', key) then SOME value
      else lookup eq xs key';

(*
tyvars alpha
tyvars $ alpha --> beta
*)
fun tyvars ty =
  if can dest_type ty
  then (* sort (curry (curry (op =) EQUAL o Type.compare)) $ *)
    flatten $ map tyvars $ #2 $ dest_type ty
  else [ty]
fun mk_list_imp ante_lst conseq =
  if List.null ante_lst then conseq
    else mk_imp(boolSyntax.list_mk_conj ante_lst, conseq)

(* from cv_compute *)
fun thy_name_prefix ty = let
  val thy_name = ty |> dest_thy_type |> #Thy
  in if thy_name <> current_theory() then thy_name ^ "_" else "" end

fun find_mutrec_types ty = let (* e.g. input ``:v`` gives [``:exp``,``:v``]  *)
  fun is_pair_ty ty = fst (dest_type ty) = "prod"
  val xs = TypeBase.axiom_of ty
           |> SPEC_ALL |> concl |> strip_exists
           |> #1 |> map (hd o dest_fun_ty o type_of)
           |> (fn ls => filter (fn ty => intersect ((#2 o dest_type) ty) ls = []) ls)
  in if is_pair_ty ty then [ty] else if length xs = 0 then [ty] else xs end

fun auto_prove proof_name (goal,tac:tactic) = let
  val (rest,validation) = tac ([],goal)
    handle HOL_ERR r => Raise (ERR "auto_prove" "tactic failure")
      | Empty => Raise (ERR "auto_prove" "tactic raised Empty")
  in if length rest = 0 then validation [] else let
  in failwith("auto_prove failed for " ^ proof_name) end end

(******************************************************************************)
(* Manage state ***************************************************************)
(******************************************************************************)

(*
(* Updates the set given a delta  *)
fun apply_delta (ThmSetData.ADD(_, th)) thml = th :: thml
  | apply_delta _ _ = failwith "unimplemented case of apply_delta"

(*
ser_ok
deser_ok
ser_imp_deser
deser_imp_ser
*)

(* Defines/Setups the theorem set *)

val {update_global_value = ser_ok_apply_global_update,
     record_delta        = ser_ok_record_delta,
     get_deltas          = ser_ok_get_deltas,
     get_global_value    = ser_ok_thm_list,
     DB = eval_ruleuction_map_by_theory,...} =
    ThmSetData.export_with_ancestry {
      settype = "ser_ok",
      delta_ops = {apply_to_global = apply_delta,
                   uptodate_delta = K true,
                   thy_finaliser = NONE,
                   initial_value = [],
                   apply_delta = apply_delta}
    }

val {update_global_value = deser_ok_apply_global_update,
     record_delta        = deser_ok_record_delta,
     get_deltas          = deser_ok_get_deltas,
     get_global_value    = deser_ok_thm_list,
     DB = eval_ruleuction_map_by_theory,...} =
    ThmSetData.export_with_ancestry {
      settype = "deser_ok",
      delta_ops = {apply_to_global = apply_delta,
                   uptodate_delta = K true,
                   thy_finaliser = NONE,
                   initial_value = [],
                   apply_delta = apply_delta}
    }

val {update_global_value = ser_imp_deser_apply_global_update,
     record_delta        = ser_imp_deser_record_delta,
     get_deltas          = ser_imp_deser_get_deltas,
     get_global_value    = ser_imp_deser_thm_list,
     DB = eval_ruleuction_map_by_theory,...} =
    ThmSetData.export_with_ancestry {
      settype = "ser_imp_deser",
      delta_ops = {apply_to_global = apply_delta,
                   uptodate_delta = K true,
                   thy_finaliser = NONE,
                   initial_value = [],
                   apply_delta = apply_delta}
    }

val {update_global_value = ser_ok_apply_global_update,
     record_delta        = ser_ok_record_delta,
     get_deltas          = ser_ok_get_deltas,
     get_global_value    = ser_ok_thm_list,
     DB = eval_ruleuction_map_by_theory,...} =
    ThmSetData.export_with_ancestry {
      settype = "ser_ok",
      delta_ops = {apply_to_global = apply_delta,
                   uptodate_delta = K true,
                   thy_finaliser = NONE,
                   initial_value = [],
                   apply_delta = apply_delta}
    }
*)


(* variable prefix *)
val var_prefix = "x"
val thm_prefix_se = "serialise_";
val thm_prefix_de = "de" ^ thm_prefix_se;


(* returns no of arguments and type of a serialisation function *)
(*
val ty = type_of ``serialise_long_list``
ser_fun_tys ty
 *)
fun ser_fun_tys ty = let
    val tys = dest_fun_ty ty
    (* serialised type *)
    val (ls,ser_to) = front_last tys
    val (ser_fns,ser_ty) = front_last ls
  in if ser_to = ser_out_ty
      (* andalso tyvars ser_ty = nub $ flatten $ map tyvars ser_fns *)
      andalso List.all (can ser_fun_tys) ser_fns
    then (ser_ty, ser_fns)
    else Raise (ERR "" "")
  end handle _ =>
    Raise (ERR "ser_fun_tys"
      ("no type of serialisation function: " ^ (type_to_string ty)))

(*
val deser_fn = ``deserialise_long_list``
val ty = type_of deser_fn
deser_fun_tys ty
*)
(* returns no of arguments and type of a deserialisation function *)
fun deser_fun_tys ty = let
    val tys = dest_fun_ty ty
    val len = length tys
    val (ls,deser_to') = front_last tys
    val (deser_fns,deser_from) = front_last ls
    val ("option",option_args) = Type.dest_type $ deser_to'
    val ("prod", prod_args) = Type.dest_type $ List.hd option_args
    (* deserialised type *)
    val deser_ty = List.hd prod_args
  in if deser_in_ty = deser_from
      andalso List.all (can deser_fun_tys) deser_fns
    then (deser_ty, deser_fns)
    else Raise (ERR "" "")
  end handle HOL_ERR _ =>
    Raise (ERR "deser_fun_tys"
      ("cannot extract type from type: " ^ (type_to_string ty)))

(*
val ser_fn = ``serialise_long_list``
val ser_fn = ``serialise_pair``
ser_types_fn ser_fn
*)
fun ser_types_fn ser_fn =
  let
    val ser_fn_ty = type_of ser_fn
    val (ser_arg_ty, fn_arg_tys) = ser_fun_tys ser_fn_ty
    (*
    val subst = Type.match_type ``:'a -> word8 list option`` ser_fn_ty
    val arg_type = Type.type_subst subst ``:'a``
    *)
  in
    (ser_arg_ty, (ser_fn, map (fn ty => (ty, ser_fun_tys ty)) fn_arg_tys))
  end

val ser_types = map ser_types_fn [
  ``serialise_string``,
  ``serialise_opt``,
  ``serialise_sum``,
  ``serialise_long_list``,
  ``serialise_pair``,
  ``serialise_num``,
  ``serialise_word8``,
  ``serialise_word16``,
  ``serialise_word32``,
  ``serialise_word64``
]

(*
val deser_fn = ``deserialise_string``
val deser_fn = ``deserialise_pair``
val deser_fn = ``deserialise_test``
*)
fun deser_types_fn deser_fn =
  let
    val deser_fn_ty = type_of deser_fn
    val (deser_arg_ty, fn_arg_tys) = deser_fun_tys deser_fn_ty
  in
    (deser_arg_ty, (deser_fn, map (fn ty => (ty, deser_fun_tys ty)) fn_arg_tys))
  end

val deser_types = map deser_types_fn [
  ``deserialise_string``,
  ``deserialise_opt``,
  ``deserialise_sum``,
  ``deserialise_long_list``,
  ``deserialise_pair``,
  ``deserialise_num``,
  ``deserialise_word8``,
  ``deserialise_word16``,
  ``deserialise_word32``,
  ``deserialise_word64``
]

val ser_ok_thms = [
  ser_ok_string,
  ser_ok_opt,
  ser_ok_sum,
  ser_ok_long_list,
  ser_ok_pair,
  ser_ok_num,
  ser_ok_word8,
  ser_ok_word16,
  ser_ok_word32,
  ser_ok_word64
]

val deser_ok_thms = [
  deser_ok_string,
  deser_ok_opt,
  deser_ok_sum,
  deser_ok_long_list,
  deser_ok_pair,
  deser_ok_num,
  deser_ok_word8,
  deser_ok_word16,
  deser_ok_word32,
  deser_ok_word64
]

val ser_imp_deser_thms = [
  ser_imp_deser_string,
  ser_imp_deser_opt,
  ser_imp_deser_sum,
  ser_imp_deser_long_list,
  ser_imp_deser_pair,
  ser_imp_deser_num,
  ser_imp_deser_word8,
  ser_imp_deser_word16,
  ser_imp_deser_word32,
  ser_imp_deser_word64
]

val deser_imp_ser_thms = [
  deser_imp_ser_string,
  deser_imp_ser_opt,
  deser_imp_ser_sum,
  deser_imp_ser_long_list,
  deser_imp_ser_pair,
  deser_imp_ser_num,
  deser_imp_ser_word8,
  deser_imp_ser_word16,
  deser_imp_ser_word32,
  deser_imp_ser_word64
]

exception Missing_fn of hol_type;

(*
val ty_arg = ``:(num # num) option list``
val ty_arg = ``:(num # 'b) option list``
val ty_arg = ``:data``
val lst = ser_types;
val lst = deser_types;
val default_type_fn = ser_default_ty
val default_type_fn = deser_default_ty
ty_to_fnname default_type_fn lst ty_arg
*)
(* constructs function from lst that can (de)serialise ty_arg *)
fun ty_to_fnname default_type_fn lst ty_arg =
  if is_vartype ty_arg then
    mk_var("f", default_type_fn ty_arg)
  else let
    val fn_filter = fn (ty,_) => can (Type.match_type ty) ty_arg
    val (ty',(fn_term,fn_args)) = List.hd $ List.filter fn_filter lst
      handle _ => Raise (Missing_fn ty_arg)
    (* length ... == length (Type.type_vars ser_ty) *)
    val fn_subst = Type.match_type ty' ty_arg
    val has_tyvars = 0 < length fn_args
    val fn_term' = Term.inst fn_subst fn_term
    val fn_subst_type = Type.type_subst fn_subst
    (*
    val (full_ty, (arg_ty, ls)) = hd fn_args
     *)
    val fn_args_inst = map (fn (full_ty, (arg_ty, ls)) =>
      (fn_subst_type full_ty, (fn_subst_type arg_ty, map fn_subst_type ls))
    ) fn_args
    (*
    val fn_term = fn_term'
    val (_,(ty_arg,_)) = List.hd fn_args_inst
     *)
    val fn_term' =
      List.foldl (fn ((_,(ty_arg,_)),fn_term) =>
        Term.mk_comb (fn_term, ty_to_fnname default_type_fn lst ty_arg)
      ) fn_term' fn_args_inst
  in fn_term' end

(*
val varname = var_prefix ^ Int.toString 0
val ty_arg = ``:mlstring # mlstring``
val ty_arg = ``:testl``
val x = ty_ser_deser ty_arg varname ser_types deser_types
*)
(* construct terms that (de)serialise the variable
  (var_prefix ^ i_var) of type ty_arg*)
fun ty_ser_fn ty_arg varname ser_types =
  mk_comb (ty_to_fnname ser_default_ty ser_types ty_arg, mk_var(varname, ty_arg))
fun ty_deser_fn ty_arg varname deser_types =
  mk_comb (ty_to_fnname deser_default_ty deser_types ty_arg, mk_var(varname, deser_in_ty))
fun ty_ser_deser ty_arg varname ser_types deser_types =
  (ty_ser_fn ty_arg varname ser_types, ty_deser_fn ty_arg varname deser_types)

(*
 ser_fns_lst       : contains (ser, deser) functions
 ser_const         : the ser function
 deser_const       : the deser function
 alg_data_name     : string of the datatype
 ser_thm           : ser definition theorem
 deser_thm         : deser definition theorem
*)
fun ser_imp_deser_thm_fn thm_name thms ser_deser_fsts_lst ser_const deser_const ser_thm deser_thm = let
  val ante_lst =
    map (fn (ser_tm,deser_tm) => mk_ucomb(mk_icomb(mk_icomb(``ser_imp_deser``, ser_tm), deser_tm), ``λx. T``)) ser_deser_fsts_lst
  val conseq = Term `ser_imp_deser ^ser_const ^deser_const (λx. T)`
  val ser_imp_deser_tm = mk_list_imp ante_lst conseq
in
  (* see ser_imp_deser_pair *)
  auto_prove thm_name (ser_imp_deser_tm,
    dsimp $ [AllCaseEqs(),PULL_EXISTS,optionTheory.IS_SOME_EXISTS,ser_imp_deser_def]
      @ [deser_thm,ser_thm]
    >> rpt strip_tac
    >> rpt (
      first_assum $ dxrule_then $ irule_at Any
      >> ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC]
    )
  )
end

(*
 ser_fns_lst       : contains (ser, deser) functions
 ser_const         : the ser function
 deser_const       : the deser function
 alg_data_name     : string of the datatype
 ser_thm           : ser definition theorem
 deser_thm         : deser definition theorem
*)
fun deser_imp_ser_thm_fn thm_name thms ser_deser_fsts_lst ser_const deser_const ser_thm deser_thm = let
  val ante_lst =
    map (fn (ser_tm,deser_tm) => mk_icomb(mk_icomb(``deser_imp_ser``, ser_tm), deser_tm)) ser_deser_fsts_lst
  val conseq = Term `deser_imp_ser ^ser_const ^deser_const`
  val deser_imp_ser_tm = mk_list_imp ante_lst conseq
in
  (* see deser_imp_ser_pair *)
  auto_prove thm_name (deser_imp_ser_tm,
    csimp $ [deser_imp_ser_def,AllCaseEqs(),PULL_EXISTS]
      @ [ser_thm,deser_thm]
    >> rpt strip_tac
    >> gvs[]
    >> rpt $ first_assum $ dxrule_then strip_assume_tac
    >> fs[]
  )
end

(*
 ser_fns_lst       : contains deser functions
 ser_const         : the function
 alg_data_name     : string of the datatype
 ser_thm           :  deser definition theorem
*)
fun ser_ok_thm_fn thm_name thms ser_fns_lst ser_const ser_thm = let
  val ante_lst =
    map (fn x => mk_icomb(``ser_ok``,x)) ser_fns_lst
  val conseq = Term `ser_ok ^ser_const`
  val ser_ok_tm = mk_list_imp ante_lst conseq
in
  (* see ser_ok_pair *)
  auto_prove thm_name (ser_ok_tm,
    rw[ser_ok_def,ser_thm,AllCaseEqs(),PULL_EXISTS,pairTheory.FORALL_PROD]
    >> fs[optionTheory.IS_SOME_EXISTS]
    >> TRY $ first_x_assum dxrule
  )
end

(*
 deser_fns_lst     : contains deser functions
 deser_const       : the function
 alg_data_name     : string of the datatype
 deser_thm         :  deser definition theorem
*)
fun deser_ok_thm_fn thm_name thms deser_fns_lst deser_const deser_thm = let
  val ante_lst =
      map (fn x => mk_icomb(``deser_ok``,x)) deser_fns_lst
  val conseq = Term `deser_ok ^deser_const`
  val deser_ok_tm = mk_list_imp ante_lst conseq
in
  (* see deser_ok_pair *)
  auto_prove thm_name (deser_ok_tm,
    csimp[AllCaseEqs(),PULL_EXISTS,deser_ok_def,PULL_FORALL,AND_IMP_INTRO,deser_thm]
    >> rpt gen_tac >> strip_tac
    >> gvs[GSYM PULL_FORALL,rich_listTheory.IS_SUFFIX_CONS,rich_listTheory.IS_SUFFIX_REFL]
    >> rpt $ first_assum $ dxrule_then strip_assume_tac
    >> fs[]
    >> rpt (
      irule rich_listTheory.IS_SUFFIX_TRANS
      >> TRY $ irule_at (Pos $ el 1) rich_listTheory.IS_SUFFIX_CONS
      >> goal_assum dxrule
    )
    >> rewrite_tac[rich_listTheory.IS_SUFFIX_REFL]
  )
end

(*
val (constr,(ser,inner_tys)) = el 2 constr_tys
*)
fun ser_cases_fn constr_tys ser_types deser_types =
  TypeBase.mk_pattern_fn $
  List.map (fn (constr,(ser,inner_tys)) =>
    let
      val ser_deser_pairs = mapi (fn i => fn ty =>
        ty_ser_deser ty (var_prefix ^ Int.toString i) ser_types deser_types) inner_tys
      val hd_tm = listSyntax.mk_list([ser], ser_elem_type)
      val ser_tms = map fst ser_deser_pairs
      val ser_res_term =
        List.foldl (listSyntax.mk_append o swap) hd_tm $
          map optionSyntax.mk_the ser_tms
    in
      if null ser_tms then (constr,optionSyntax.mk_some hd_tm) else
      (
        List.foldl (mk_comb o swap) constr $
          mapi (fn i => fn ty => mk_var(var_prefix ^ Int.toString i, ty)) inner_tys
      ,
        mk_cond(
          List.foldl boolSyntax.mk_conj T $ map optionSyntax.mk_is_some ser_tms,
          optionSyntax.mk_some ser_res_term , optionSyntax.mk_none deser_in_ty)
      )
    end
  ) constr_tys

(*
  val (constr,(ser,inner_tys)) = List.hd constr_tys
*)
fun deser_cases_lst alg_data_ty constr_tys ser_types deser_types = let
  val ts = mk_var("ts", deser_in_ty)
  in TypeBase.mk_pattern_fn (
  (
    List.map (fn (constr,(ser,inner_tys)) =>
      let
        val var_val_fn = fn i => fn ty => mk_var("val" ^ Int.toString i, ty)
        val ser_deser_pairs = mapi (fn i => fn ty =>
          (ty_ser_deser ty "ts" ser_types deser_types, var_val_fn i ty)) inner_tys
        (* inner most term *)
        val succ_term =
          optionSyntax.mk_some $
            pairSyntax.mk_pair (
            (List.foldl (mk_comb o swap) constr
              $ map snd ser_deser_pairs), ts)
        (*
        val ((_,deser_fn),var) = List.hd ser_deser_pairs
        val term = succ_term
        *)
        val deser_res_term = List.foldl (fn (((_,deser_fn),var),term) =>
          let
            val pair = pairSyntax.mk_pair(var,ts)
          in
            mk_comb(
              TypeBase.mk_pattern_fn [
                (optionSyntax.mk_none $ type_of $ pair,
                  optionSyntax.mk_none $ optionSyntax.dest_option $
                    type_of $ succ_term),
                (optionSyntax.mk_some pair, term)
              ],
              deser_fn
            )
          end
        ) succ_term $ List.rev ser_deser_pairs
      in
        (listSyntax.mk_cons(ser, ts), deser_res_term)
      end
    ) constr_tys
  ) @ [(ts, optionSyntax.mk_none $ pairSyntax.mk_prod(alg_data_ty,deser_in_ty))])
  end

(*
val ty = ``:test``;
val ty = ``:('d, 'c) b``
val ignore_tyvars = []
val alg_data_ty = ty;
val ser_types = !rser_types
val deser_types = !rdeser_types
*)
(* expects non-polymorphic datatype *)
fun gen_serialise_thms ignore_tyvars thms ser_types deser_types alg_data_ty = let
(* get algebraic datatype constructors with their inner types *)
(*
  val mutrec_count = length $ find_mutrec_types alg_data_ty
  val ind = TypeBase.induction_of alg_data_ty
  val inputs = ind |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCTS |> map (fst o dest_forall o concl)
  val tyvars = dest_type (type_of (hd inputs)) |> snd
               |> filter (fn tyvar => not (mem tyvar ignore_tyvars))
  val alg_data_name = inputs |> hd |> type_of |> dest_type |> fst
*)
  val alg_data_name = type_name alg_data_ty
  val thy_prefix = thy_name_prefix alg_data_ty
  (* String.extract (type_to_string alg_data_ty, 1, NONE) *)
  val constructors = TypeBase.constructors_of alg_data_ty
  val constr_ser_alist = mapi (fn i => fn constr => (constr, n2w8 i)) constructors
  val cmp_term = uncurry Term.term_eq
  val constr_to_ser = lookup cmp_term constr_ser_alist
  val ser_to_constr = lookup cmp_term $ map swap constr_ser_alist
  (* check that each type arg of each constructor is defined *)
  (*
    val i = 1
    val constr = List.nth (constructors,i)
    constr_to_ser constr
    ser_to_constr $ n2w8 0
  *)
  val constr_tys = mapi (fn i => fn constr =>
    let
      val tys = dest_fun_ty $ type_of constr
    in
      if length tys < 2
      then (constr, (n2w8 i, [])) (* no arguments to constructor *)
      else let
        val inner_typs = fst $ front_last tys
        (* guarantees that all inner types can be serialised *)
        val r = map (ty_to_fnname ser_default_ty ser_types) inner_typs
      in
        (* TODO make check polymorphic *)
        (*
        val x = List.nth (inner_typs,1)
        *)
(*
        if not $ List.all (fn x => mem x $ map fst base_types) inner_typs
        then
          Raise (ERR "gen_serialise_thms"
            ("cannot (de)serialise some arg type to constructor "
              ^ (term_to_string constr)
              ^ " " ^ (type_to_string $ type_of constr)
              ^ ". Not in the base_types"))
        else
*)
          (constr, (n2w8 i, inner_typs))
      end
    end
  ) constructors

  (*
  val ser_thm = fetch "-" (ser_name ^ "_def")
  val deser_thm = fetch "-" (deser_name ^ "_def")
   *)
  val ser_name = thm_prefix_se ^ thy_prefix ^ alg_data_name
  val rhs = ser_cases_fn constr_tys ser_types deser_types
  val ser_type = type_of rhs
  val ser_var = mk_var(ser_name, ser_type)
  val ser_thm =
    Ho_Rewrite.REWRITE_RULE[FUN_EQ_THM] $
      xDefine ser_name `^ser_var = ^rhs`
  val ser_const = mk_const(ser_name, ser_type)

  val deser_name = thm_prefix_de ^ thy_prefix ^ alg_data_name
  val rhs = deser_cases_lst alg_data_ty constr_tys ser_types deser_types
  val deser_type = type_of rhs
  val deser_var = mk_var(deser_name, deser_type)
  val deser_thm =
    Ho_Rewrite.REWRITE_RULE[FUN_EQ_THM] $
      xDefine deser_name `^deser_var = ^rhs`
      |> CONV_RULE (DEPTH_CONV BETA_CONV)
  val deser_const = mk_const(deser_name, deser_type)

(* construct thms
 * deser_ok_def , ser_ok_def
 * deser_imp_ser_def , ser_imp_deser_def
 *)

  val ser_deser_lst =
    List.map (fn (ser,deser) =>
        ((fst $ dest_comb ser, type_of $ fst $ dest_comb ser),
          (fst $ dest_comb deser, type_of $ fst $ dest_comb deser))) $
    flatten $ List.map (fn (constr,(ser,inner_tys)) =>
      mapi (fn i => fn ty =>
        ty_ser_deser ty (var_prefix ^ Int.toString i) ser_types deser_types) inner_tys
    ) constr_tys

  val ser_fns_lst = map (fst o fst) ser_deser_lst
  val so_thm_name = "ser_ok_" ^ alg_data_name
  val ser_ok_thm = ser_ok_thm_fn so_thm_name thms ser_fns_lst ser_const ser_thm

  val deser_fns_lst = map (fst o snd) ser_deser_lst
  val do_thm_name = "deser_ok_" ^ alg_data_name
  val deser_ok_thm = deser_ok_thm_fn do_thm_name thms deser_fns_lst deser_const deser_thm

  val ser_deser_fsts_lst = map (fn (x,y) => (fst x, fst y)) ser_deser_lst
  val sid_thm_name = "ser_imp_deser_" ^ alg_data_name
  val ser_imp_deser_thm = ser_imp_deser_thm_fn sid_thm_name thms ser_deser_fsts_lst ser_const deser_const ser_thm deser_thm
  val dis_thm_name = "deser_imp_ser_" ^ alg_data_name
  val deser_imp_ser_thm = deser_imp_ser_thm_fn dis_thm_name thms ser_deser_fsts_lst ser_const deser_const ser_thm deser_thm
  val simp_rules = SIMP_RULE std_ss thms
  val new_thms = map simp_rules
                      [ser_ok_thm,deser_ok_thm,ser_imp_deser_thm,deser_imp_ser_thm]
  val new_thm_names = [so_thm_name,do_thm_name,sid_thm_name,dis_thm_name]
  val tms = map save_thm $ zip new_thm_names new_thms

(*
  val base_types' = (alg_data_ty,(ser_name,deser_name)) :: base_types
*)
in
  (ser_thm, ser_name,
    (ser_types_fn $ mk_const(ser_name, ser_type)) :: ser_types,
    ser_ok_thm, ser_imp_deser_thm,
  deser_thm, deser_name,
    (deser_types_fn $ mk_const(deser_name, deser_type)) :: deser_types,
    deser_ok_thm, deser_imp_ser_thm
  )
end


(* setup statefullness *)

val rser_types = ref ser_types
val rdeser_types = ref deser_types

val rser_ok_thms = ref ser_ok_thms
val rdeser_ok_thms = ref deser_ok_thms
val rser_imp_deser_thms = ref ser_imp_deser_thms
val rdeser_imp_ser_thms = ref deser_imp_ser_thms

fun print_db () = (!rser_types @ !rdeser_types,
  !rser_ok_thms @ !rdeser_ok_thms
  @ !rser_imp_deser_thms @ !rdeser_imp_ser_thms)

(* stateful version *)
fun define_ser_de ty =
let
  val thms = !rser_ok_thms @ !rdeser_ok_thms @ !rser_imp_deser_thms @ !rdeser_imp_ser_thms
  val (ser_thm, ser_name, ser_types, ser_ok_thm, ser_imp_deser_thm,
    deser_thm, deser_name, deser_types, deser_ok_thm, deser_imp_ser_thm)
    = gen_serialise_thms [] thms (!rser_types) (!rdeser_types) ty
  val _ = (rser_types := ser_types)
  val _ = (rdeser_types := deser_types)
  val _ = rser_ok_thms := ser_ok_thm::(!rser_ok_thms)
  val _ = rdeser_ok_thms := deser_ok_thm::(!rdeser_ok_thms)
  val _ = rser_imp_deser_thms := ser_imp_deser_thm::(!rser_imp_deser_thms)
  val _ = rdeser_imp_ser_thms := deser_imp_ser_thm::(!rdeser_imp_ser_thms)
  val new_thms = [ser_ok_thm,deser_ok_thm,ser_imp_deser_thm,deser_imp_ser_thm]
in
  (ser_thm, deser_thm, new_thms)
end

(* extend database *)
fun extend_db (ser_const,ser_ok_thm,ser_imp_deser_thm)
  (deser_const,deser_ok_thm,deser_imp_ser_thm) = let
  val _ = rser_types := (ser_types_fn ser_const)::(!rser_types)
  val _ = rdeser_types := (deser_types_fn deser_const)::(!rdeser_types)
  val _ = rser_ok_thms := ser_ok_thm::(!rser_ok_thms)
  val _ = rdeser_ok_thms := deser_ok_thm::(!rdeser_ok_thms)
  val _ = rser_imp_deser_thms := ser_imp_deser_thm::(!rser_imp_deser_thms)
  val _ = rdeser_imp_ser_thms := deser_imp_ser_thm::(!rdeser_imp_ser_thms)
in () end


(* from cv_compute *)
fun rec_define_ser_de ty = let
  fun loop acc ty =
    let
      val (ser_def,deser_def,thms) = define_ser_de ty
      val _ = print ("Finished de/serialisation for " ^ type_name ty ^ "\n\n")
      val _ = print_thm $ el 3 thms
      val _ = print "\n\n"
    in thms @ acc end
    handle Missing_fn needs_ty =>
    let
      val _ = print ("Interrupting " ^ type_name ty ^
                     " since " ^ type_name needs_ty ^ " needed.\n")
      val acc = loop acc needs_ty
      val _ = print ("Continuing " ^ type_name ty ^
                     " since " ^ type_name needs_ty ^ " exists.\n")
    in loop acc ty end
  in loop [] ty end

(*

Datatype:
  test = Constructor1 mlstring (num list) | Constructor2 (word32 # word16)
End

Datatype:
  testl = Testl ((test + word64) list)
End

  val (ser_thm, ser_name, ser_types, ser_ok_thm, ser_imp_deser_thm,
    deser_thm, deser_name, deser_types, deser_ok_thm, deser_imp_ser_thm) =
  gen_serialise_thms [] [] ser_types deser_types ``:test``

val ty = ``:test``
val (ser_thm, deser_thm, other_thms) = define_ser_de ty

val thms = rec_define_ser_de ``:testl``

print_db()

*)

end
