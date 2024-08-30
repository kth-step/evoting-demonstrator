open HolKernel boolLib Parse bossLib listTheory pairTheory optionTheory combinTheory relationTheory mlstringTheory finite_mapTheory;

val _ = new_theory "VarDPrimaryBackup";

Type key = ``:mlstring``
Type value = ``:mlstring``
Type data = ``:(key |-> value)``

Datatype:
 KV_input =
 | Put key value
 | Get key
 | Del key
 | CAS key (value option) value
 | CAD key value
End

Datatype:
 KV_output = Response key (value option) (value option)
End

Datatype:
 msg =
 | BackItUp KV_input
 | Ack
End

Datatype:
 PB_input =
  | Request KV_input
  | Read
End

Datatype:
 PB_output =
  | RequestResponse KV_input KV_output
  | ReadResponse data
End

Datatype:
 PB_data =
  <| queue : KV_input list
   ; state : data |>
End

Datatype:
 PB_name =
 | Primary
 | Backup
End

Definition getk:
 getk (k:key) (d:data) = FLOOKUP d k
End

Definition setk:
 setk (k:key) (v:value) (d:data) = d |+ (k,v)
End

Definition delk:
 delk (k:key) (d:data) = d \\ k
End

Definition resp:
 resp k v old = Response k v old
End

Definition VarDHandler:
 (VarDHandler (Put k v) (d:data) =
  let old = getk k d in
  let d' = setk k v d in
  (resp k (SOME v) old, d'))
 /\
 (VarDHandler (Get k) d =
  let v = getk k d in
  (resp k v v, d))
 /\
 (VarDHandler (Del k) d =
  let old = getk k d in
  let d' = delk k d in
  (resp k NONE old, d'))
 /\
 (VarDHandler (CAS k v v') d =
  let old = getk k d in
  if old = v then
    let d' = setk k v' d in
    (resp k (SOME v') old, d')
  else
    (resp k old old, d))
 /\
 (VarDHandler (CAD k v) d =
  let old = getk k d in
  if old = SOME v then
    let d' = delk k d in
    (resp k NONE old, d')
  else
  (resp k old old, d))
End

Definition init_state:
 init_state : data = FEMPTY
End

Definition PB_init:
 PB_init (n:PB_name) =
  <| queue := []
   ; state := init_state |>
End

Definition PB_input_handling:
 PB_input_handling (h:PB_name) (i:PB_input) (d:PB_data)
  (os : (PB_name # (PB_input + PB_output)) list)
  (d' : PB_data) (ms : (PB_name # msg) list) : bool =
 ((h = Primary /\ d'.state = d.state /\
  ?r. i = Request r /\
  d'.queue = d.queue ++ [r] /\
  os = [(Primary, INL (Request r))] /\
  ((ms = [] /\ d.queue <> []) \/ (ms = [(Backup, BackItUp r)] /\ d.queue = [])))
 \/
 (i = Read /\
  d = d' /\
  os = [(h, INL Read); (h, INR (ReadResponse d.state))] /\
  ms = [])
 \/
 (i <> Read /\
  h = Backup /\
  d = d' /\
  os = [(Backup, INL i)] /\
  ms = []))
End

Definition PB_input_handler:
 (PB_input_handler Primary (i:PB_input) (d:PB_data)
  : (PB_name # (PB_input + PB_output)) list # PB_data # ((PB_name # msg) list) =
  case i of
  | Request r =>
    let d' = d with <| queue := d.queue ++ [r] |> in
    let os = [(Primary, INL (Request r))] in
    if d.queue = []
    then (os, d', [(Backup, BackItUp r)])
    else (os, d', [])
  | Read => ([(Primary, INL Read); (Primary, INR (ReadResponse d.state))], d, []))
 /\
 (PB_input_handler Backup i d =
  case i of
  | Request r => ([(Backup, INL (Request r))], d, [])
  | Read => ([(Backup, INL Read); (Backup, INR (ReadResponse d.state))], d, []))
End

Definition PB_net_handling:
 PB_net_handling (dst:PB_name) (src:PB_name) (m:msg) (d:PB_data)
  (os : (PB_name # (PB_input + PB_output)) list)
  (d' : PB_data) (ms : ((PB_name # msg) list)) : bool =
 ((os = [] /\ d' = d /\ ms = [] /\
   ((dst = Primary /\ ?i. m = BackItUp i) \/
    (dst = Backup /\ m = Ack)))
  \/
  (dst = Primary /\ m = Ack /\
   ((d.queue = [] /\ os = [] /\ ms = [] /\ d' = d) \/
    (?h t. d.queue = h :: t /\ d'.queue = t /\
      ((t = [] /\ ms = []) \/
       (?y ys. t = y :: ys /\ ms = [(Backup, BackItUp y)])) /\
      ?us st'. VarDHandler h d.state = (us,st') /\
       os = [(Primary, INR (RequestResponse h us))] /\
       d'.state = st')))
  \/
  (dst = Backup /\ ms = [(Primary, Ack)] /\ d'.queue = d.queue /\ os = [] /\
   (?i. m = BackItUp i /\ d'.state = SND (VarDHandler i d.state))))
End

Definition PB_net_handler:
 (PB_net_handler Primary (src:PB_name) (m:msg) (d:PB_data)
  : (PB_name # (PB_input + PB_output)) list # PB_data # ((PB_name # msg) list) =
  case m of
  | Ack =>
    (case d.queue of
    | [] => ([], d, [])
    | x::xs =>
      let (os, st') = VarDHandler x d.state in
      let d' = <| queue := xs ; state := st' |> in
      let os' = [(Primary, INR (RequestResponse x os))] in
      case xs of
      | [] => (os', d', [])
      | y::ys =>
        (os', d', [(Backup, BackItUp y)]))
  | _ => ([], d, []))
  /\
 (PB_net_handler Backup src m d =
  case m of
  | BackItUp i =>
    ([], d with <| state := SND (VarDHandler i d.state) |>, [(Primary, Ack)])
  | _ => ([], d, []))
End

val _ = export_theory ();
