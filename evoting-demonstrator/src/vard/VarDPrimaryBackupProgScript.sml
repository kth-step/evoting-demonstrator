open preamble ml_translatorLib ml_translatorTheory ml_progTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib astPP comparisonTheory totoTheory fromSexpTheory
open VarDPrimaryBackupTheory VarDPrimaryBackupCakeTheory serialiseTheory VarDPrimaryBackupSerialiseTheory;

val _ = new_theory "VarDPrimaryBackupProg";

val _ = translation_extends "basisProg";

fun readfile x = TextIO.inputAll (TextIO.openIn x);

(* adds CakeML file to translation *)
fun load_file name =
  let
    val read = readfile name;
    val res = process_topdecs `^read`
  in
    append_prog res
  end;

val files = ["functionslib.cml", "networkffilib.cml"];
val files = List.map (fn x => "../../cakeml_ffi/" ^ x) files;
val loads = List.map load_file files

val _ = register_type ``:PB_name``;

val _ = ml_prog_update (open_module "VarDPrimaryBackup");

val _ = translate getk_cake;
val _ = translate setk_cake;
val _ = translate delk_cake;
val _ = translate resp;

val _ = translate VarDHandler_cake;
val res = translate init_state_cake;

val _ = next_ml_names := ["init"];
val _ = translate PB_init_cake;

val _ = translate append_queue_def;
val _ = translate get_queue_def;
val _ = translate get_state_def;
val _ = translate set_state_def;

val _ = next_ml_names := ["input_handler"];
val _ = translate PB_input_handler_cake;

val _ = next_ml_names := ["net_handler"];
val _ = translate PB_net_handler_cake;

val r = translate opt_tostring_def;
val r = translate list_tostring_def;
val r = translate pair_tostring_def;
val r = translate map_tostring_def;
val r = translate sum_tostring_def;

val r = translate pb_name_tostring_def;
val r = translate kv_input_tostring_def;
val r = translate pb_input_tostring_def;
val r = translate kv_output_tostring_def;
val r = translate pb_data_cake_tostring_def;

val r = translate pb_out_tostring_def;
val r = translate msg_tostring_def;
val r = translate trace_tostring_def;
val r = translate handler_out_tostring_def;

val r = translate   serialise_string_translate_thm;
val r = translate deserialise_string_translate_thm;
val _ = translate   serialise_opt_def;
val _ = translate deserialise_opt_def;

val _ = translate   serialise_key_def;
val _ = translate deserialise_key_def;
val _ = translate   serialise_value_def;
val _ = translate deserialise_value_def;

val _ = next_ml_names := ["serialise_kv_output"];
val r = translate   serialise_KV_output_def;
val _ = next_ml_names := ["deserialise_kv_output"];
val r = translate deserialise_KV_output_def;
val _ = next_ml_names := ["serialise_kv_input"];
val r = translate   serialise_KV_input_def;
val _ = next_ml_names := ["deserialise_kv_input"];
val r = translate deserialise_KV_input_def;
val _ = next_ml_names := ["serialise_pb_input"];
val r = translate   serialise_PB_input_def;
val _ = next_ml_names := ["deserialise_pb_input"];
val r = translate deserialise_PB_input_def;
val _ = translate   serialise_msg_def;
val _ = translate deserialise_msg_def;

val r = translate   serialise_map_translate_thm;

val _ = next_ml_names := ["serialise_pb_output"];
val r = translate $
  REWRITE_RULE[GSYM Word8ProgTheory.Word8_fromInt_def] serialise_PB_output_cake_def;

val load_vard_pre = load_file "../../cakeml_ffi/vard_pre.cml"

(* str_to_PB_name *)
val _ = append_prog o process_topdecs $ `
  fun str_to_kind str = if String.isPrefix "primary" str then Primary else Backup;
  fun kind_to_str kind = case kind of Primary => "primary" | Backup => "backup";
`

val _ = ml_prog_update (close_module NONE);

val res = append_prog o process_topdecs $ `
fun process_fd log self hmap net_h input_h
  serialise_msg deserialise_msg deserialise_input serialise_output
  (active_fd : int) (fds : int list,state) =
let val logfn = log "cml process_fd" in
  case socket_receive log active_fd of
    Ok (NewClient fd) => (fd::fds,state)
  | Ok (UDPBuffer addr ls size) =>
      let
        val _ = logfn 1 ("UDP message on fd " ^ (Int.toString active_fd)
          ^ " from addr " ^ addr
          (* size - 1 = removes trailing line feed *)
          ^ ": " ^ byte_list_to_string (List.take ls (min 20 (List.length ls))) (Int.- size 1));
        (* find the source's name *)
        val src_lst =
          List.filter
            (fn (x,y) => snd y = addr andalso fst y = active_fd) hmap
        val deser = deserialise_msg (List.take ls size)
        val (trace,(state,msgs)) =
          if List.length src_lst = 1 andalso Option.isSome deser then
            net_h self (fst (List.hd src_lst)) (fst (Option.valOf deser)) state
          else (
            (if List.length src_lst <> 1 then
              logfn 0 ("unknown sender addr " ^ addr ^ " fd " ^
                Int.toString active_fd)
            else
              logfn 1 ("could not deserialise message"));
            ([],(state,[]))
          )
      in (
        (* order irrelevant - note: evaluation order is rtl *)
        List.map (fn (id,msg) =>
          let
            val fd_addr = Alist.lookup hmap id;
            val ser = serialise_msg msg;
          in
            if Option.isSome ser andalso Option.isSome fd_addr then
              case socket_send_udp log
                (fst (Option.valOf fd_addr))
                (Option.valOf ser)
                (snd (Option.valOf fd_addr)) of
                Ok _ => logfn 1 "UDP message sent"
              | Error n str => logfn 1 "could not send UDP message"
            else if Option.isNone ser then
              logfn 1 "could not serialise UDP message"
            else
              logfn 1 "could not find UDP destination identifier"
          end) msgs;
        (fds,state)
      ) end
  | Ok (Buffer ls size) =>
      let
        val _ = logfn 1 ("message on fd " ^ (Int.toString active_fd)
          ^ ": " ^ (String.concatWith " " (List.map (Int.toString o Word8.toInt) (List.take ls (min size (min 20 (List.length ls)))))));
        val _ = logfn 1 "call deserialise";
        val deser = deserialise_input (List.take ls size)
        val _ = logfn 1 ("deserialise " ^ (Bool.toString (Option.isSome deser)));
      in
        if Option.isNone deser then (
          logfn 1 ("could not deserialise Buffer ls");
          (fds,state)
        ) else
          let
            val _ = logfn 1 "call input_h";
            val x = input_h self (fst (Option.valOf deser)) state;
            val (trace,(state,msgs)) = x;
            val _ = logfn 1 ("returns \n\t" ^ VarDPrimaryBackup.handler_out_tostring x);
            val output_msgs = List.concat (List.map
              (fn x => case snd x of Inr x => [x] | _ => []) trace)
            val _ = logfn 1 ("called input_h msgs length "
                      ^ (Int.toString (List.length msgs)) ^ " out msgs length: "
                      ^ (Int.toString (List.length output_msgs)));
            (* order irrelevant - note evaluation order is rtl *)
            val _ = List.map (fn (id,msg) =>
              let
                val _ = logfn 1 "before Alist.lookup";
                val fd_addr = Alist.lookup hmap id;
                val _ = logfn 1 "before serialise_msg";
                val ser = serialise_msg msg;
                val _ = logfn 1 ("after serialise_msg: " ^ (VarDPrimaryBackup.msg_tostring msg));
              in
                if Option.isSome ser andalso Option.isSome fd_addr then (
                  logfn 1 ("addr" ^ (snd (Option.valOf fd_addr)));
                  case socket_send_udp log
                    (fst (Option.valOf fd_addr))
                    (Option.valOf ser)
                    (snd (Option.valOf fd_addr)) of
                    Ok _ => logfn 1 "udp message sent"
                  | Error n str => logfn 1 "could not send udp message"
                ) else if Option.isNone ser then
                  logfn 1 "could not serialise udp message"
                else
                  logfn 1 ("could not find udp destination identifier")
              end) msgs
            val _ = logfn 1 ("send input response(s): "
              ^ (Int.toString (List.length output_msgs)));
            val _ = List.map (fn msg =>
              let
                val ser = serialise_output msg; (* serialise_pb_output *)
              in
                if Option.isSome ser then (
                  logfn 1 ("fd " ^ (Int.toString active_fd));
                  case socket_send log active_fd (Option.valOf ser) of
                    Ok _ => logfn 1 "message sent"
                  | Error n str => logfn 1 "could not send message"
                )
                else
                  logfn 1 "could not serialise UD message"
              end) output_msgs
          in (fds,state) end
      end
  | Ok Disconnect => (
      logfn 1 ("disconnect client " ^ (Int.toString active_fd));
      (case socket_close log active_fd of
        Ok n => ()
      | Error n str =>
        logfn 1 ("error closing socket of fd " ^ Int.toString active_fd));
      (* remove the fd *)
      (List.filter (fn x => x <> active_fd) fds, state)
    )
  | Error code str => (
      (* TODO treat each error *)
      logfn 1 ("error code " ^ (Int.toString code)
        ^ " fd " ^ (Int.toString active_fd) ^ " " ^ str);
      (fds,state)
    )
end;
`
*)

(*
max_print_depth := -1

val tm = QCONV EVAL res |> concl |> rand
val prog_tm = tm
val pick_name = I
val ts = fst (listSyntax.dest_list prog_tm)
val dec_tm = hd ts
val s = get_ml_prog_state ()

 $CAKEMLDIR/translator/ml_progLib.sml
add_dec dec_tm pick_name s
astSyntax.is_Dletrec dec_tm
open ml_progTheory ml_progLib
ml_progLib.let_env_abbrev

val (loc,x1) = astSyntax.dest_Dletrec dec_tm
val prefix = get_mod_prefix s
fun f str = prefix ^ pick_name str ^ "_v"
(* main_v *)
val xs = listSyntax.dest_list x1 |> fst
            |> map (f o stringSyntax.fromHOLstring o rand o rator)

add_Dletrec loc x1 xs s

enable_astPP();

val funs = x1
val v_names = xs

fun add_Dletrec loc funs v_names = let

fun proc nm (th, (ML_code (ss,envs,vs,mlth))) = let
    val th = CONV_RULE (RAND_CONV (SIMP_CONV std_ss [write_rec_def,FOLDR,
        semanticPrimitivesTheory.build_rec_env_def])) th
    val _ = is_let (concl th) orelse failwith "add_Dletrec: not let"
    val (_, tm) = dest_let (concl th)
    val tms = rev (find_terms (can (match_term Recclosure_pat)) tm)
    val xs = zip v_names tms
    val v_defs = map (fn (x,y) => define_abbrev false x y) xs
    val th = CONV_RULE (RAND_CONV (REWRITE_CONV (map GSYM v_defs))) th
  in let_env_abbrev ALL_CONV nm
    (th, ML_code (ss,envs,v_defs @ vs,mlth)) end


ML_code_upd nm mp_thm adjs
ML_code_upd "add_Dletrec"
  (SPECL [funs, loc] ML_code_Dletrec)
  [solve_ml_imp_conv EVAL,
    solve_ml_imp_conv eval_every_exp_one_con_check,
    let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
    proc] s
val nm = "add_Dletrec"
val mp_thm = (SPECL [funs, loc] ML_code_Dletrec)
val adjs = [solve_ml_imp_conv EVAL,
    solve_ml_imp_conv eval_every_exp_one_con_check,
    let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
    proc]
val (ML_code code) = s


open preamble;
open ml_progTheory astSyntax packLib alist_treeLib comparisonTheory;


fun ML_code_upd nm mp_thm adjs (ML_code code) = let
    (* when updating an ML_code thm by forward reasoning, first
       abstract over all the program components (which can be large
       snoc-lists or cons-lists) and process on the smaller abstracted
       theorem, connecting to the original ML_code thm with a single
       final MATCH_MP step. *)
    val orig_th = #4 code
    val blocks = ML_code_blocks (concl orig_th)
    val (f, xs) = strip_comb (concl orig_th)
    val abs_blocks = mapi (fn i => pairSyntax.list_mk_pair o
        (mapi (fn j => if j = 2 then (fn _ =>
            mk_var ("prog_var_" ^ Int.toString i, decs_ty)) else I))) blocks
    val abs_blocks_tm = listSyntax.mk_list (abs_blocks, type_of (hd abs_blocks))
    val abs_concl = list_mk_comb (f,
        mapi (fn i => if i = 1 then K abs_blocks_tm else I) xs)
    val preproc_th = MATCH_MP mp_thm (ASSUME abs_concl)

disable_astPP();


  val (preproc_th', ML_c)
      = foldl (fn (adj, x) => adj nm x) (preproc_th, ML_code code) $ List.take(adjs,1)

 val (preproc_th1, ML_c1) = solve_ml_imp_conv EVAL nm (preproc_th, ML_code code)
 o

(* fails *)

 val (preproc_th2, ML_c2) =
  solve_ml_imp (prove_assum_by_conv eval_every_exp_one_con_check) nm (preproc_th1, ML_c1)
  prove_assum_by_conv eval_every_exp_one_con_check preproc_th1

val conv =
  SIMP_CONV (srw_ss()) [semanticPrimitivesTheory.do_con_check_def,ML_code_env_def]
  THENC DEPTH_CONV nsLookup_conv
  THENC reduce_conv;

val th = preproc_th1
  val (x,y) = dest_imp (concl th)


SIMP_CONV (srw_ss()) [semanticPrimitivesTheory.do_con_check_def,ML_code_env_def]
x
|> CONV_RULE $ DEPTH_CONV nsLookup_conv


DEPTH_CONV nsLookup_conv
        ``nsLookup (merge_env VarDPrimaryBackupProg_env_18 init_env).c (Short "[]")``

DEPTH_CONV nsLookup_conv
       ``nsLookup (merge_env VarDPrimaryBackupProg_env_18 init_env).c
         (Short "Config")``

  val lemma1 = conv x
  val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV lemma1)) th


val adjs = [solve_ml_imp_conv EVAL,
    solve_ml_imp_conv eval_every_exp_one_con_check,
    let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
    proc]

  val (proc_th, ML_code (ss, envs, vs, _)) =
  List.nth(adjs,2) nm (preproc_th', ML_c)

    val (proc_th, ML_code (ss, envs, vs, _))
        = foldl (fn (adj, x) => adj nm x) (preproc_th, ML_code code) adjs
    val _ = same_const ML_code_tm (fst (strip_comb (concl proc_th)))
        orelse failwith ("ML_code_upd: " ^ nm ^ ": unfinished: "
            ^ Parse.thm_to_string proc_th)
    val th = MATCH_MP (DISCH abs_concl proc_th) orig_th
  in ML_code (ss, envs, vs, th) end


fun add_prog prog_tm pick_name s = let
  val ts = fst (listSyntax.dest_list prog_tm)
  in remove_snocs (foldl (fn (x,y) => add_dec x pick_name y) s ts) end

ml_progLib.add_prog tm I $ get_ml_prog_state ()

EVAL `` EVERY (λ(f,n,e). every_exp (one_con_check (ML_code_env init_env []). c) e) ^tm``

open astPP
val _  = astPP.disable_astPP();


  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]

  ,
                   fetch "-" (current_theory() ^ "_env_def")];

  get_ml_prog_state ()

ml_translatorLib.ml_prog_update
  $ ml_progLib.add_prog tm I

*)

val res = append_prog o process_topdecs $ `
fun main () =
let
  val c = VarDPrimaryBackup.parse_flags (CommandLine.arguments()) (VarDPrimaryBackup.Config "" [] 0 "");
  val loglevel = VarDPrimaryBackup.get_debug c;
  val logfn = log loglevel "main";
  val _ = logfn 1 ("Debug level: " ^ (Int.toString loglevel));
  val self = VarDPrimaryBackup.get_id c;
  val _ = logfn 1 ("Identifier: " ^ self);
  val log = logid loglevel self;
  val logfn = log "main";
  val _ = logfn 1 ("Socket: " ^ VarDPrimaryBackup.get_socket c);
  val _ = logfn 1 ("Nodes: ");
  val _ = List.map
    (logfn 1 o (fn (x,(y,z)) => x ^ " " ^ y ^ " " ^ Int.toString z))
    (VarDPrimaryBackup.get_nodes c);
  val self = VarDPrimaryBackup.str_to_kind (VarDPrimaryBackup.get_id c);
  val nodes = List.map
    (fn (name,(ip,port)) => (VarDPrimaryBackup.str_to_kind name, ip ^ ":" ^ Int.toString port))
    (VarDPrimaryBackup.get_nodes c);
  val addr = List.hd (List.map snd (List.filter (fn x => fst x = self) nodes))
  val _ = logfn 1 ("own address: " ^ addr);
  val fd_udp = (
    case socket_create_udp log addr of
      Ok fd => fd
    | Error n str =>
      let
        val _ = logfn 0 ("failed to create udp socket at addr " ^ addr);
        val _ = Runtime.fail ();
      in 0 end
  )
  val nodes = List.map (fn (kind,ip_port) => (kind,(fd_udp,ip_port))) nodes;
  val hmap =
    List.foldl (fn (key,value) => fn map => (
      logfn 1 ((VarDPrimaryBackup.kind_to_str key) ^ " " ^ Int.toString (fst value)
        ^ " " ^ (snd value));
      Alist.update map (key,value)
    )) [] nodes;
  val _ = logfn 1 ("hmap size: " ^ (Int.toString (List.length hmap)));
  val fds =
    [fd_udp] @ (
      if 0 < String.size (VarDPrimaryBackup.get_socket c) then
        (case socket_create log (VarDPrimaryBackup.get_socket c) of
          Ok socket_fd => [socket_fd]
        | Error n msg =>
            let val _ = logfn 1 "skipping creation of unix domain socket" in [] end)
      else []
    )
  val _ = logfn 1 (snd (Option.valOf (Alist.lookup hmap Backup)))
  val _ = logfn 1 (snd (Option.valOf (Alist.lookup hmap Primary)))
  val _ = List.map (logfn 1 o VarDPrimaryBackup.kind_to_str o fst) hmap;
  val _ = event_loop log (fds,VarDPrimaryBackup.init self)
    (process_fd log self hmap
      VarDPrimaryBackup.net_handler
      VarDPrimaryBackup.input_handler
      VarDPrimaryBackup.serialise_msg
      VarDPrimaryBackup.deserialise_msg
      VarDPrimaryBackup.deserialise_pb_input
      VarDPrimaryBackup.serialise_pb_output
    )
in
  ()
end;
`

val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

val _ = astToSexprLib.write_ast_to_file "vardProg.sexp" prog;

val _ = export_theory ();
