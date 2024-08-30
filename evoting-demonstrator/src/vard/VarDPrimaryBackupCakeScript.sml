open preamble mlstringTheory mllistTheory mlmapTheory totoTheory VarDPrimaryBackupTheory;

val _ = new_theory "VarDPrimaryBackupCake";

Type data_cake = ``:((key,value) mlmap$map)``

Datatype:
 PB_output_cake =
  | RequestResponse_cake KV_input KV_output
  | ReadResponse_cake ((key,value) mlmap$map)
End

(* PB_data_cake queue state *)
Datatype:
  pb_data_cake_t = PB_data_cake (KV_input list) ((key,value) mlmap$map)
End

Definition set_queue_def:
  set_queue x v =
  case x of
  | PB_data_cake q s => PB_data_cake v s
End

Definition get_queue_def:
  get_queue x =
  case x of
  | PB_data_cake q st => q
End

Definition append_queue_def:
  append_queue x v =
  case x of
  | PB_data_cake q st => PB_data_cake (q++v) st
End

Definition set_state_def:
  set_state x v =
  case x of
  | PB_data_cake q st => PB_data_cake q v
End

Definition get_state_def:
  get_state x =
  case x of
  | PB_data_cake q st => st
End


Definition getk_cake:
 getk_cake (k:key) (d:data_cake) = lookup d k
End

Definition setk_cake:
 setk_cake (k:key) (v:value) (d:data_cake) = insert d k v
End

Definition delk_cake:
 delk_cake (k:key) (d:data_cake) = delete d k
End

Definition VarDHandler_cake:
 VarDHandler_cake x (d:data_cake) =
  case x of
  | Put k v =>
      let old = getk_cake k d in
      let d' = setk_cake k v d in
      (resp k (SOME v) old, d')
  | Get k =>
      let v = getk_cake k d in
      (resp k v v, d)
  | Del k =>
    let old = getk_cake k d in
    let d' = delk_cake k d in
    (resp k NONE old, d')
  | CAS k v v' =>
    let old = getk_cake k d in
    if old = v then
      let d' = setk_cake k v' d in
      (resp k (SOME v') old, d')
    else
      (resp k old old, d)
  | CAD k v =>
    let old = getk_cake k d in
    if old = SOME v then
      let d' = delk_cake k d in
      (resp k NONE old, d')
    else
    (resp k old old, d)
End

Definition init_state_cake:
 init_state_cake : data_cake = mlmap$empty compare
End

Definition PB_init_cake:
 PB_init_cake (n:PB_name) = PB_data_cake [] init_state_cake
End

Definition PB_input_handler_cake:
  PB_input_handler_cake x (i:PB_input) (d:pb_data_cake_t)
  : (PB_name # (PB_input + PB_output_cake)) list # pb_data_cake_t # ((PB_name # msg) list) =
  case x of
  | Primary =>
  (case i of
    | Request r =>
      let d' = append_queue d [r] in
      let os = [(Primary, INL (Request r))] in
      if get_queue d = []
      then (os, d', [(Backup, BackItUp r)])
      else (os, d', [])
    | Read => ([(Primary, INL Read); (Primary, INR (ReadResponse_cake (get_state d)))], d, []))
  | Backup =>
    (case i of
    | Request r => ([(Backup, INL (Request r))], d, [])
    | Read => ([(Backup, INL Read); (Backup, INR (ReadResponse_cake (get_state d)))], d, []))
End

Definition PB_net_handler_cake:
 PB_net_handler_cake x (src:PB_name) (m:msg) (d:pb_data_cake_t)
  : (PB_name # (PB_input + PB_output_cake)) list # pb_data_cake_t # ((PB_name # msg) list) =
  case x of
  | Primary =>
    (case m of
    | Ack =>
      (case get_queue d of
      | [] => ([], d, [])
      | x::xs =>
        let (os, st') = VarDHandler_cake x (get_state d) in
        let d' = PB_data_cake xs st' in
        let os' = [(Primary, INR (RequestResponse_cake x os))] in
        case xs of
        | [] => (os', d', [])
        | y::ys =>
          (os', d', [(Backup, BackItUp y)]))
    | _ => ([], d, []))
  | Backup =>
    (case m of
    | BackItUp i =>
      ([], set_state d $ SND $ VarDHandler_cake i $ get_state d, [(Primary, Ack)])
    | _ => ([], d, []))
End

val _ = export_theory ();
