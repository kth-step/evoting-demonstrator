(*
   (De)serialises arguments and output of PB_net_handler_cake and
   PB_input_handler_cake
 *)

open preamble mlstringTheory StringProgTheory mlmapTheory;
open serialiseTheory VarDPrimaryBackupTheory VarDPrimaryBackupCakeTheory;

val _ = new_theory "VarDPrimaryBackupSerialise";

Definition serialise_key_def:
  serialise_key = serialise_string
End

Definition deserialise_key_def:
  deserialise_key = deserialise_string
End

Definition serialise_value_def:
  serialise_value = serialise_string
End

Definition deserialise_value_def:
  deserialise_value = deserialise_string
End

Definition serialise_KV_input_def:
  serialise_KV_input (input : KV_input) : word8 list option =
  case input of
  | Put k v =>
      let sk = serialise_key k;
          sv = serialise_value v in
      if IS_SOME sk /\ IS_SOME sv then
        SOME $ 0w:: ((THE sk) ++ (THE sv))
      else NONE
  | Get k =>
      let sk = serialise_key k in
      if IS_SOME sk then
        SOME $ 1w:: (THE sk)
      else NONE
  | Del k =>
      let sk = serialise_key k in
      if IS_SOME sk then
        SOME $ 2w:: (THE sk)
      else NONE
  | CAS k opt v =>
      let sk = serialise_key k;
          so = serialise_opt serialise_value opt;
          sv = serialise_value v in
      if IS_SOME sk /\ IS_SOME so /\ IS_SOME sv then
        SOME $ 3w:: ((THE sk) ++ (THE so) ++ (THE sv))
      else NONE
  | CAD k v =>
      let sk = serialise_key k;
          sv = serialise_value v in
      if IS_SOME sk /\ IS_SOME sv then
        SOME $ 4w:: ((THE sk) ++ (THE sv))
      else NONE
End

Definition deserialise_KV_input_def:
  deserialise_KV_input ts =
  case ts of
  | 0w::ts =>
    (case deserialise_key ts of
    | NONE => NONE
    | SOME (k,ts) =>
      (case deserialise_value ts of
      | NONE => NONE
      | SOME (v,ts) => SOME (Put k v, ts)))
  | 1w::ts =>
    (case deserialise_key ts of
    | NONE => NONE
    | SOME (k,ts) => SOME (Get k, ts))
  | 2w::ts =>
    (case deserialise_key ts of
    | NONE => NONE
    | SOME (k,ts) => SOME (Del k, ts))
  | 3w::ts =>
    (case deserialise_key ts of
    | NONE => NONE
    | SOME (k,ts) =>
      (case deserialise_opt deserialise_value ts of
      | NONE => NONE
      | SOME (opt,ts) =>
        case deserialise_value ts of
        | NONE => NONE
        | SOME (v,ts) => SOME (CAS k opt v, ts)))
  | 4w::ts =>
    (case deserialise_key ts of
    | NONE => NONE
    | SOME (k,ts) =>
      (case deserialise_value ts of
      | NONE => NONE
      | SOME (v,ts) => SOME (CAD k v, ts)))
  | _ => NONE
End

Theorem serialise_KV_input_thm:
  !ts input ts'.
  serialise_KV_input input = SOME ts
  ==> deserialise_KV_input (ts++ts') = SOME (input,ts')
Proof
  rw[serialise_KV_input_def]
  >> BasicProvers.every_case_tac
  >> gvs[deserialise_key_def,deserialise_value_def,serialise_key_def,
    serialise_value_def,deserialise_KV_input_def,IS_SOME_EXISTS]
  >> imp_res_tac serialise_string_thm
  >> imp_res_tac serialise_string_thm'
  >> imp_res_tac serialise_opt_string_thm
  >> imp_res_tac serialise_opt_string_thm'
  >> gvs[]
  >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> fs[Excl"APPEND_ASSOC"]
QED

Theorem deserialise_KV_input_thm:
  !ts input ts'.
    deserialise_KV_input ts = SOME (input, ts')
  ==> ?ts''. serialise_KV_input input = SOME ts'' /\ ts = ts'' ++ ts'
Proof
  Cases >> rw[deserialise_KV_input_def]
  >> gvs[AllCaseEqs(),deserialise_key_def,deserialise_value_def,
    serialise_key_def,serialise_value_def]
  >> gvs[serialise_KV_input_def]
  >> imp_res_tac deserialise_string_thm
  >> imp_res_tac deserialise_opt_string_thm
  >> gvs[serialise_key_def,serialise_value_def]
QED

Definition serialise_KV_output_def:
  serialise_KV_output (output : KV_output) : word8 list option =
  case output of
  | Response key val_opt val_opt' =>
    let sk = serialise_key key;
        so = serialise_opt serialise_value val_opt;
        so' = serialise_opt serialise_value val_opt';
    in
      if IS_SOME sk /\ IS_SOME so /\ IS_SOME so' then
        SOME $ 0w :: ((THE sk) ++ (THE so) ++ (THE so'))
      else NONE
End

Definition deserialise_KV_output_def:
  deserialise_KV_output (ts : word8 list) =
  case ts of
  | 0w::ts =>
    (case deserialise_key ts of
    | NONE => NONE
    | SOME (k,ts) =>
      (case deserialise_opt deserialise_value ts of
      | NONE => NONE
      | SOME (opt,ts) =>
        (case deserialise_opt deserialise_value ts of
        | NONE => NONE
        | SOME (opt',ts) => SOME (Response k opt opt',ts))))
  | _ => NONE
End

Theorem serialise_KV_output_thm:
  !output ts ts'.
  serialise_KV_output output = SOME ts
  ==> deserialise_KV_output (ts ++ ts') = SOME (output,ts')
Proof
  Cases >> rw[serialise_KV_output_def]
  >> fs[IS_SOME_EXISTS,serialise_key_def,serialise_value_def]
  >> imp_res_tac serialise_string_thm'
  >> imp_res_tac serialise_opt_string_thm'
  >> fs[deserialise_KV_output_def,deserialise_key_def,deserialise_value_def]
  >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> fs[Excl"APPEND_ASSOC"]
QED

Theorem deserialise_KV_output_thm:
  !output ts ts' ts''.
  deserialise_KV_output ts = SOME (output,ts'')
  ==> ?ts'. serialise_KV_output output = SOME ts' /\ ts = ts' ++ ts''
Proof
  Cases >> rw[deserialise_KV_output_def]
  >> gvs[serialise_KV_output_def,AllCaseEqs()]
  >> fs[deserialise_key_def,deserialise_value_def,serialise_key_def,serialise_value_def]
  >> imp_res_tac deserialise_string_thm
  >> imp_res_tac deserialise_opt_string_thm
  >> fs[deserialise_KV_output_def,deserialise_key_def,deserialise_value_def]
  >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> fs[Excl"APPEND_ASSOC"]
QED

Definition serialise_msg_def:
  serialise_msg msg : word8 list option =
  case msg of
  | Ack => SOME [0w]
  | BackItUp kv_in =>
    (case serialise_KV_input kv_in of
    | SOME ts => SOME $ 1w :: ts
    | NONE => NONE)
End

Definition deserialise_msg_def:
  deserialise_msg (ts : word8 list) =
  case ts of
  | 0w::ts => SOME (Ack, ts)
  | 1w::ts =>
    (case deserialise_KV_input ts of
    | SOME (kv_in, ts) => SOME (BackItUp kv_in, ts)
    | NONE => NONE)
  | _ => NONE
End

Theorem serialise_msg_thm:
  !msg ts ts'.
  serialise_msg msg = SOME ts
  ==> deserialise_msg (ts ++ ts') = SOME (msg,ts')
Proof
  rw[serialise_msg_def]
  >> gvs[deserialise_msg_def,AllCaseEqs()]
  >> dxrule_then (fs o single) serialise_KV_input_thm
QED

Theorem deserialise_msg_thm:
  !msg ts ts'' ts'.
  deserialise_msg ts = SOME (msg, ts')
  ==> ?ts''. serialise_msg msg = SOME ts'' /\ ts = ts'' ++ ts'
Proof
  rw[deserialise_msg_def]
  >> gvs[AllCaseEqs(),serialise_msg_def]
  >> dxrule_then strip_assume_tac deserialise_KV_input_thm
  >> fs[]
QED

Definition serialise_PB_input_def:
  serialise_PB_input x : word8 list option =
  case x of
  | Read => SOME [0w]
  | Request kv_in =>
    (case serialise_KV_input kv_in of
    | SOME ts => SOME $ 1w :: ts
    | NONE => NONE)
End

Definition deserialise_PB_input_def:
  deserialise_PB_input (ts : word8 list) =
  case ts of
  | 0w::ts => SOME (Read, ts)
  | 1w::ts =>
    (case deserialise_KV_input ts of
    | SOME (kv_in, ts) => SOME (Request kv_in, ts)
    | NONE => NONE)
  | _ => NONE
End

Theorem serialise_PB_input_thm:
  !pb_in ts ts'.
  serialise_PB_input pb_in = SOME ts
  ==> deserialise_PB_input (ts ++ ts') = SOME (pb_in,ts')
Proof
  rw[serialise_PB_input_def]
  >> gvs[deserialise_PB_input_def,AllCaseEqs()]
  >> dxrule_then (fs o single) serialise_KV_input_thm
QED

Theorem deserialise_PB_input_thm:
  !pb_in ts ts'' ts'.
  deserialise_PB_input ts = SOME (pb_in, ts')
  ==> ?ts''. serialise_PB_input pb_in = SOME ts'' /\ ts = ts'' ++ ts'
Proof
  rw[deserialise_PB_input_def]
  >> gvs[AllCaseEqs(),serialise_PB_input_def]
  >> dxrule_then strip_assume_tac deserialise_KV_input_thm
  >> fs[]
QED

Theorem deserialise_PB_input_thm:
  !map ts ts'' ts'.
  deserialise_str_map ts = SOME (map, ts')
  ==> ?ts''. serialise_map serialise_string serialise_string map = SOME ts''
    /\ ts = ts'' ++ ts'
Proof
  Cases >> rw[deserialise_str_map_def]
  >> gvs[AllCaseEqs(),serialise_map_def]
  >> cheat
QED

Definition serialise_PB_output_cake_def:
  serialise_PB_output_cake x : word8 list option =
  case x of
  | RequestResponse_cake kv_in kv_out =>
    (case serialise_KV_input kv_in of
    | NONE => NONE
    | SOME kv_in =>
        (case serialise_KV_output kv_out of
        | NONE => NONE
        | SOME kv_out => SOME $ [0w] ++ kv_in ++ kv_out))
  | ReadResponse_cake kv_map =>
    (case serialise_map serialise_key serialise_value kv_map of
    | SOME kv_map => SOME $ 1w :: kv_map
    | NONE => NONE)
End

(*
Examples

EVAL o Term $ `serialise_PB_input $ Read` |> concl |> rhs
SOME [0w]

EVAL o Term $ `serialise_PB_input $ Request $ Put (strlit "key") (strlit "b")` |> concl |> rhs
SOME [1w; 0w; 3w; 107w; 101w; 121w; 1w; 98w]

EVAL o Term $ `serialise_PB_input $ Request $ Get (strlit "key")` |> concl |> rhs
SOME [1w; 1w; 3w; 107w; 101w; 121w]

EVAL o Term $ `serialise_PB_input $ Request $ Del (strlit "key")` |> concl |> rhs
SOME [1w; 2w; 3w; 107w; 101w; 121w]

EVAL o Term $ `serialise_PB_input $ Request $ CAS (strlit "key") NONE (strlit "val")` |> concl |> rhs
SOME [1w; 3w; 3w; 107w; 101w; 121w; 1w; 3w; 118w; 97w; 108w]

EVAL o Term $ `serialise_PB_input $ Request $ CAD (strlit "key") (strlit "val2")` |> concl |> rhs
SOME [1w; 4w; 3w; 107w; 101w; 121w; 4w; 118w; 97w; 108w; 50w]

*)

(* serialise to string *)

Definition pb_name_tostring_def:
  pb_name_tostring x =
  case x of
   Primary => strlit "Primary"
 | Backup => strlit "Backup"
End

Definition kv_input_tostring_def:
  kv_input_tostring x =
  case x of
    Put k v => String_concat [«Put »; k; strlit " "; v]
  | Get k   => String_concat [«Get »; k]
  | Del k   => String_concat [«Del »; k]
  | CAS k v_opt v => String_concat [«CAS »; k; « »; opt_tostring v_opt; « »; v]
  | CAD k v   => String_concat [«CAD »; k; strlit " "; v]
End

Definition pb_input_tostring_def:
  pb_input_tostring x =
  case x of
    Request kv_in => strcat (strlit "Request ") (kv_input_tostring kv_in)
  | Read => strlit "Read"
End

Definition kv_output_tostring_def:
  kv_output_tostring x =
  case x of Response k v_opt v_opt' =>
  let v = opt_tostring v_opt and v' = opt_tostring v_opt';
  in
    String_concat [«Response »; k; « »; v; « »; v']
End

Definition pb_data_cake_tostring_def:
  pb_data_cake_tostring x =
  case x of PB_data_cake kv_in_lst kv_map =>
  String_concat [«PB_data_cake »;
    list_tostring kv_input_tostring kv_in_lst;
    « »;
    map_tostring kv_map
  ]
End

Definition pb_out_tostring_def:
  pb_out_tostring (x : PB_output_cake) =
  case x of
    RequestResponse_cake kv_in kv_out =>
      String_concat [«RequestResponse_cake (»; kv_input_tostring kv_in;
        «) (»; kv_output_tostring kv_out; «)»]
  | ReadResponse_cake data =>
      String_concat [strlit "ReadResponse_cake ("; map_tostring data; strlit ")"]
End

Definition msg_tostring_def:
  msg_tostring x =
  case x of
   BackItUp kv_in => String_concat [«BackItUp »; kv_input_tostring kv_in]
 | Ack => «Ack»
End

Definition trace_tostring_def:
  trace_tostring =
    list_tostring $ pair_tostring pb_name_tostring (sum_tostring pb_input_tostring pb_out_tostring)
End

(* convert handler output to string *)
Definition handler_out_tostring_def:
  handler_out_tostring x = case x of (trace,st,msgs) =>
    String_concat [«(»;
      trace_tostring trace; «, »;
      pb_data_cake_tostring st; «, »;
      list_tostring (pair_tostring pb_name_tostring msg_tostring) msgs; «)»
    ]
End

val _ = export_theory ();
