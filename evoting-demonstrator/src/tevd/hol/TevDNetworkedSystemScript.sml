(*
 Defines datatypes and input/output handlers for the executable voting system
*)

open HolKernel boolLib Parse bossLib;
open listTheory pairTheory combinTheory relationTheory optionTheory stringTheory wordsTheory
     mllistTheory
     executionTheory networkTheory formatTheory vcsStateTheory mixnetStateTheory
     serialiseLib serialiseTheory mlstringTheory
     byteTreeTheory mlintTheory
     mlstringSyntax;

val _ = new_theory "TevDNetworkedSystem";

(* TODO move general thms *)

Theorem partition_aux_PART_eq:
  !ls P pos neg. partition_aux P ls pos neg
    = (REVERSE $ FST $ PART P ls pos neg, REVERSE $ SND $ PART P ls pos neg)
Proof
  Induct
  >> ONCE_REWRITE_TAC[sortingTheory.PART_DEF,partition_aux_def]
  >> rw[]
QED

Theorem partition_PARTITION_eq:
  !ls P. partition P ls
  = (REVERSE $ FST $ PARTITION P ls, REVERSE $ SND $ PARTITION P ls)
Proof
  fs[partition_def,sortingTheory.PARTITION_DEF,partition_aux_PART_eq]
QED

Theorem PERM_partition:
  !ls P. PERM ((FST $ partition P ls) ++ (SND $ partition P ls)) ls
Proof
  fs[partition_PARTITION_eq]
  >> REWRITE_TAC[GSYM REVERSE_APPEND,sortingTheory.PERM_REVERSE_EQ]
  >> ONCE_REWRITE_TAC[sortingTheory.PERM_FUN_APPEND]
  >> ONCE_REWRITE_TAC[sortingTheory.PERM_SYM]
  >> rpt strip_tac
  >> irule miscTheory.PERM_PARTITION
  >> fs[PAIR]
  >> irule_at Any EQ_REFL
QED

(* mlstring serialisation  *)

Definition serialise_mlstring_def:
  serialise_mlstring (str :mlstring) :word8 list option =
  serialise_string $ explode str
End

Theorem ser_ok_mlstring:
  ser_ok serialise_mlstring
Proof
  rw[ser_ok_def,serialise_mlstring_def]
  >> dxrule $ REWRITE_RULE[ser_ok_def] ser_ok_string
  >> fs[]
QED

Definition deserialise_mlstring_def:
  deserialise_mlstring (ts: word8 list) =
    OPTION_MAP (implode ## I) $ deserialise_string ts
End

Theorem deser_ok_mlstring:
  deser_ok deserialise_mlstring
Proof
  fs[deser_ok_def,deserialise_mlstring_def,PULL_EXISTS,pairTheory.FORALL_PROD]
  >> rpt gen_tac >> strip_tac
  >> dxrule_then irule $ REWRITE_RULE[deser_ok_def] deser_ok_string
QED

Theorem ser_imp_deser_mlstring:
  ser_imp_deser serialise_mlstring deserialise_mlstring (λx. T)
Proof
  rw[ser_imp_deser_def,serialise_mlstring_def,deserialise_mlstring_def,pairTheory.EXISTS_PROD]
  >> dxrule_then (irule_at Any) $ REWRITE_RULE[ser_imp_deser_def] ser_imp_deser_string
  >> fs[mlstringTheory.implode_explode]
QED

Theorem deser_imp_ser_mlstring:
  deser_imp_ser serialise_mlstring deserialise_mlstring
Proof
  rw[deser_imp_ser_def,serialise_mlstring_def,deserialise_mlstring_def,pairTheory.EXISTS_PROD]
  >> fs[mlstringTheory.implode_explode]
  >> dxrule_then (irule_at Any) $ REWRITE_RULE[deser_imp_ser_def] deser_imp_ser_string
QED

val _ = extend_db (``serialise_mlstring``,deser_ok_mlstring,ser_imp_deser_mlstring)
  (``deserialise_mlstring``,ser_ok_mlstring,deser_imp_ser_mlstring);

(* /mlstring  *)

val (serialise_voter_def, deserialise_voter_def, _) =
  define_ser_de ``:voter``;

Type log = ``:mlstring -> unit``

Definition request_id_tostring_def:
  request_id_tostring x =
  case x of Request v => concat [«Request (»; num_to_str $ w2n v; «)»]
End

val (serialise_request_id_def, deserialise_request_id_def, _) =
  define_ser_de ``:request_id``

Datatype:
 netsys_name =
 | Name_VCS
 | Name_MixNet
 | Name_Admin
 | Name_Client
End

val (serialise_netsys_name_def, deserialise_netsys_name_def, _) =
  define_ser_de ``:netsys_name``

Datatype:
  cl_msg_cake =
      Vote_cake (* sign voter enc_vote *) data voter data
    | PreVote_cake data request_id data
    | SigningRequest_cake (* hash voter *) data voter
    | Hello_cake voter
End

Datatype:
  log_cake =
  | Voteerror_cake vote_error cl_msg_cake
  | Votesuccess_cake data voter data (* sign enc_vote *)
End

Datatype:
 netsys_msg =
 | Msg_VotingStart (voter list) (* from Admin to VCS *)
 | Msg_VotingEnd                     (* from Admin to VCS *)
  (* sign voter enc_vote, voter is used for identification at the proxy *)
 | Msg_Ballot data request_id data        (* from Client to VCS *)
 | Msg_BallotRecorded request_id voter    (* from VCS to Client *)
 | Msg_BallotError request_id        (* from VCS to Client *)
  (* enc_vote list *)
 | Msg_Ballots data        (* from VCS to MixNet *)
 | Msg_Response request_id data
 | Msg_Confirm
End

val (serialise_netsys_msg_def, deserialise_netsys_msg_def, _) =
  define_ser_de ``:netsys_msg``

Definition netsys_msg_is_inputanswer_def:
  netsys_msg_is_inputanswer x = case x of Msg_Response y z => T | _ => F
End

Definition netsys_msg_partition_def:
  netsys_msg_partition (self : netsys_name)=
  partition (λ(name,msg). name = self /\ netsys_msg_is_inputanswer msg)
End

Theorem netsys_msg_partition_all:
  !self ls x. PERM ((FST $ netsys_msg_partition self ls) ++ (SND $ netsys_msg_partition self ls)) ls
Proof
  fs[PERM_partition,netsys_msg_partition_def]
QED

val (serialise_contestant_def, deserialise_contestant_def, _) =
  define_ser_de ``:contestant``;

Datatype:
  vcs_state_cake = <|
      voted : voter list
    ; eligible : voter list
    ; votes : data list
    ; out_msg : netsys_msg list     (* outstanding messages to voters *)
    ; log : log_cake list
    ; phase : vcsPhase
  |>
End

Definition send_msg_cake_def:
  send_msg_cake (s : vcs_state_cake) request_id msg =
    case msg of
    | Voteerror_cake code vote =>
        s with <| log updated_by (SNOC msg)
            ; out_msg := [Msg_BallotError request_id] |>
    | Votesuccess_cake sign voter enc_vote =>
        s with <| log updated_by (SNOC msg)
            ; out_msg := [Msg_BallotRecorded request_id voter] |>
End

Type fns = ``:
  (data -> bool)
  # (data -> data -> mlstring option)
  # (word8 list -> word8 list)
  ``

Definition process_vote_cake_def:
  process_vote_cake (log:log) ((auth_check,vote_format,t):fns) (sign,enc_vote,request_id) (s : vcs_state_cake) =
    let prevote = PreVote_cake sign request_id enc_vote in
    if s.phase <> Voting then
      let u = log «not accepting any vote» in
      send_msg_cake s request_id $ Voteerror_cake (Inactive s.phase) prevote
    else
      case vote_format sign enc_vote of
      | NONE =>
        let u = log «invalid vote format» in
        send_msg_cake s request_id $ Voteerror_cake Format prevote
      | SOME voter =>
    let voter = Voter voter in
    let vote = Vote_cake sign voter enc_vote in
    if ~is_valid_bytetree enc_vote then
      let u = log «vote: invalid byte tree» in
      send_msg_cake s request_id $ Voteerror_cake ByteFormat vote
    else
    let u = log  «valid vote format, now check auth» in
    if ~auth_check sign then
      let u = log «unauthenticated vote» in
      send_msg_cake s request_id $ Voteerror_cake Unauth vote
    else if ~MEM voter s.eligible then
      let u = log «voter not eligible» in
      send_msg_cake s request_id $ Voteerror_cake Ineligible vote
    else if MEM voter s.voted then
      let u = log «voter has already voted» in
      send_msg_cake s request_id $ Voteerror_cake Voted vote
    else
      let u = log «stored valid vote» in
      s with <|
        voted updated_by (SNOC voter)
      ; votes updated_by (SNOC enc_vote)
      ; out_msg := [Msg_BallotRecorded request_id voter]
      ; log updated_by (SNOC $ Votesuccess_cake sign voter enc_vote)
    |>
End

Definition vcs_state_cake_init_def:
  vcs_state_cake_init = <|
      voted := []
    ; eligible := []
    ; votes := []
    ; out_msg := []
    ; log := []
    ; phase := Init
  |>
End

Datatype:
 netsys_data =
  <| vcs_state : vcs_state_cake
  (* enc_vote list *)
   ; mixnet_ballots : data option |>
End

(* convert message to netsys_name # netsys_msg *)
Definition vcs_msg2netsys_msg_def:
  vcs_msg2netsys_msg vcs_msg =
    case vcs_msg of
    | Msg_BallotRecorded request_id voter => [(Name_Client, Msg_BallotRecorded request_id voter)]
    | Msg_BallotError request_id    => [(Name_Client, Msg_BallotError request_id)]
    | Msg_Ballots votes_data  => [(Name_MixNet, Msg_Ballots votes_data)]
    | _ => []
End

Datatype:
 netsys_input =
 (* signature@0 vote@2 *)
 | Input_Ballot data request_id data
 | Input_VotingStart (voter list)
 | Input_VotingEnd
End

val (serialise_netsys_input_def,
  deserialise_netsys_input_def,
  netsys_input_thms) =
    define_ser_de ``:netsys_input``;

Datatype:
 netsys_output =
 | Output_Ballots data
 | Output_BallotRecorded request_id voter
 | Output_BallotError request_id
 | Confirm
End

val (serialise_netsys_output_def,
  deserialise_netsys_output_def, _) =
    define_ser_de ``:netsys_output``;

Definition netsys_init_def:
 netsys_init (n:netsys_name) =
  <| vcs_state := vcs_state_cake_init
   ; mixnet_ballots := NONE |>
End

(* serialise datatypes to string *)
(* TODO adapt serialiseLib and use it *)

Definition word8_tostring_def:
  word8_tostring :word8 -> mlstring = num_to_str o w2n
End

Definition opt_tostring_def:
  opt_tostring x =
  case x of
    SOME x => concat [strlit " Some("; x; strlit ")"]
  | NONE    => «None»
End

Definition list_tostring_def:
  list_tostring f x =
    let max_len = 30 in
    if LENGTH x <= max_len
    then (concat [«[»; concatWith «; » (MAP f x); «]»])
    else (concat [«[»; concatWith «; » (TAKE max_len $ MAP f x); «; ...]»])
End

Definition pair_tostring_def:
  pair_tostring f f' x = case x of (x,y) => concat [«(»; f x; «, »; f' y; «)»]
End

Definition sum_tostring_def:
  sum_tostring f f' sum =
  case sum of
    INL x => concat [«Inl »; f x]
  | INR x => concat [«Inr »; f' x]
End

Definition netsys_name_tostring_def:
  netsys_name_tostring x =
  case x of
   Name_VCS    => strlit "vcs"
 | Name_MixNet => strlit "mixnet"
 | Name_Admin  => strlit "admin"
 | Name_Client => strlit "client"
End

Definition string_to_netsys_name_def:
  string_to_netsys_name str =
  if isPrefix (strlit "vcs") str then Name_VCS
  else (if isPrefix (strlit "mixnet") str then Name_MixNet
    else (if isPrefix (strlit "admin") str then Name_Admin
      else Name_Client))
End

Definition voter_tostring_def:
  voter_tostring x =
  case x of Voter v => concat [«Voter (»; v; «)»]
End

Definition contestant_tostring_def:
  contestant_tostring x =
  case x of Contestant v => concat [«Contestant »; num_to_str $ w2n v]
End

Definition netsys_input_tostring_def:
  netsys_input_tostring x =
  case x of
  | Input_VotingStart cl => concat [strlit "Input_VotingStart (";
        list_tostring voter_tostring cl; «)» ]
  | Input_VotingEnd => concat [strlit "Input_VotingEnd"]
  | Input_Ballot d1 request_id d2 => concat [strlit "Input_Ballot (";
      list_tostring word8_tostring d1; «) (»;
      request_id_tostring request_id; «) (»;
      list_tostring word8_tostring d2; «)»
    ]
End

Definition phase_tostring_def:
  phase_tostring x =
  case x of
  | Init    => «Init»
  | Voting  => «Voting»
  | Ended   => «Ended»
End

Definition netsys_msg_tostring_def:
  netsys_msg_tostring x =
  case x of
  | Msg_VotingStart cl          => concat [«Msg_VotingStart (»; list_tostring voter_tostring cl; «)»]
  | Msg_VotingEnd               => «Msg_VotingEnd»
  | Msg_Ballot d1 request_id d2      => concat [«Msg_Ballot (»; list_tostring word8_tostring d1; «) (»; request_id_tostring request_id; «) (»; list_tostring word8_tostring d2; «)»]
  | Msg_BallotRecorded request_id voter    => concat [«Msg_BallotRecorded (»; request_id_tostring request_id; «) (»; voter_tostring voter; «)»]
  | Msg_BallotError request_id  => concat [«Msg_BallotError (»; request_id_tostring request_id; «)»]
  | Msg_Ballots data           => concat [«Msg_Ballots (»; list_tostring word8_tostring data; «)»]
  | Msg_Response request_id data => concat [«Msg_Response (»; request_id_tostring request_id; «) (»; list_tostring word8_tostring data; «)»]
  | Msg_Confirm => «Msg_Confirm»
End

Definition log_tostring_def:
  log_tostring x =
  case x of
  | Voteerror_cake err msg => concat [«Voteerror_cake »; «...»]
  | Votesuccess_cake d1 voter d2 => concat [«Votesuccess_cake (sign: »;
  list_tostring word8_tostring d1; «) (voter: »; voter_tostring voter; «) (env: »; list_tostring word8_tostring d2; «)»]
End

Definition vcs_state_tostring_def:
  vcs_state_tostring x =
    concat [
      «vcs_state: »;
      «voted: (»; list_tostring voter_tostring x.voted;
      «) eligible: (»; list_tostring voter_tostring x.eligible;
      «) votes: (»; list_tostring (list_tostring word8_tostring) x.votes;
      «) out_msg: (»; list_tostring netsys_msg_tostring x.out_msg;
      «) log: (»;  list_tostring log_tostring x.log;
      «) phase: (»; phase_tostring x.phase;
    «)»]
End

Definition option_tostring_def:
  option_tostring f x =
  case x of
  | NONE => «NONE»
  | SOME v => concat [«SOME (»; f v; «)»]
End

Definition netsys_data_tostring_def:
  netsys_data_tostring x =
  concat [«netsys_data: (vcs: »;
    vcs_state_tostring x.vcs_state; «) (ballots: »;
    option_tostring (list_tostring word8_tostring) x.mixnet_ballots; «)»
  ]
End

Definition netsys_out_tostring_def:
  netsys_out_tostring x =
  case x of
  | Output_Ballots dl           => concat [«Output_Ballots (»; list_tostring word8_tostring dl; «)»]
  | Output_BallotRecorded request_id voter => concat [«Output_BallotRecorded (»; request_id_tostring request_id; «) (»; voter_tostring voter; «)»]
  | Output_BallotError request_id    => concat [«Output_BallotError (»; request_id_tostring request_id; «)»]
  | Confirm                     => «Confirm»
End

Definition trace_tostring_def:
  netsys_trace_tostring =
    list_tostring $ pair_tostring netsys_name_tostring (sum_tostring netsys_input_tostring netsys_out_tostring)
End

(* convert handler output to string *)
Definition netsys_handler_out_tostring_def:
  netsys_handler_out_tostring x = case x of (trace',st,msgs) =>
    concat [«(»;
      netsys_trace_tostring trace'; «, »;
      netsys_data_tostring st; «, »;
      list_tostring (pair_tostring netsys_name_tostring netsys_msg_tostring) msgs; «)»
    ]
End

(*
Admin:
- input to start election, results in AdminMsg sent to VCS
- input to stop election, results in AdminMsg sent to VCS

VCS/MixNet:
- ignore any inputs sent to it

Client
- receives votes over UD from Proxy server and forwards to VCS over UDP

*)

Definition netsys_input_handler_def:
 (netsys_input_handler (log:log) fns Name_VCS (i:netsys_input) (d:netsys_data) id
  : (netsys_name # (netsys_input + netsys_output)) list #
     netsys_data # ((netsys_name # netsys_msg) list) =
  let u = log «vcs ignored input» in ([], d, []))
 /\
 (netsys_input_handler log fns Name_MixNet i d id =
  let u = log «mixnet ignored input» in ([], d, []))
 /\
 (netsys_input_handler log fns Name_Admin i d id =
  let out_msg_opt = serialise_netsys_output Confirm in
  let outl =
    if IS_SOME out_msg_opt then [(Name_Admin, Msg_Response (Request id) $ THE $ out_msg_opt)]
    else []
  in
    case i of
    | Input_VotingStart vl =>
        let u = log «admin voting start» in
        ([], d, [(Name_VCS, Msg_VotingStart vl)] ++ outl)
    | Input_VotingEnd =>
        let u = log «admin voting end» in
        ([], d, [(Name_VCS, Msg_VotingEnd)] ++ outl)
    | _ =>
        let u = log «admin ignored input» in
        ([], d, []))
 /\
 (netsys_input_handler log fns Name_Client i d id =
  let _ = log (netsys_input_tostring i) in
  case i of
  | Input_Ballot sign request_id enc_vote =>
    let u = log «client ballot input» in
    (* transform the format of the encrypted vote *)
    let new_enc_vote = (SND $ SND fns) enc_vote in
    (* id is set by the FFI shim, instead client-set request_id *)
    let msg = Msg_Ballot sign (Request id) new_enc_vote
    in ([], d, [(Name_VCS,msg)])
  | _ =>
    let u = log «client ignored input» in
    ([], d, []))
End

Definition netsys_input_handling_def:
  netsys_input_handling fns name input data ol data' msgs <=>
    ?log id. netsys_input_handler log fns name input data id = (ol, data', msgs)
End

Definition start_voting_cake_def:
  start_voting_cake vl s = if s.phase = Init
    then SOME (s with <| phase := Voting ; eligible := vl |>) else NONE
End

Definition end_voting_cake_def:
  end_voting_cake s = if s.phase = Init \/ s.phase = Ended then NONE else SOME (s with phase := Ended)
End

Definition pop_out_msgs_cake_def:
  pop_out_msgs_cake s = (s with out_msg := [],s.out_msg)
End

(*
Admin:
- ignore any message sent to it

VCS:
- receive messages from CDN, Admin, etc.

Client:
- forwards net messages to inputs

*)

Definition netsys_net_handler_def:
 (netsys_net_handler (log:log) fns Name_VCS (src:netsys_name) (m:netsys_msg) (d:netsys_data)
  : (netsys_name # (netsys_input + netsys_output)) list #
     netsys_data # ((netsys_name # netsys_msg) list) =
    case (src,m) of
    | (Name_Admin,Msg_VotingStart vl) =>
        (case start_voting_cake vl d.vcs_state of
        | NONE =>
            let u = log «vcs invalid voting start msg from admin» in
              ([], d, [])
        | SOME vcs_state' =>
          let u = log «vcs start voting» in
            ([], d with vcs_state := vcs_state', []))
    | (Name_Admin,Msg_VotingEnd) =>
        (case end_voting_cake d.vcs_state of
        | NONE =>
          let u = log «vcs invalid voting end msg from admin» in ([], d, [])
        | SOME vcs_state' =>
          let u = log «vcs end voting» in
          case prepare_submission vcs_state'.votes of
          | SOME votes_data =>
            let out = (Name_MixNet, Msg_Ballots votes_data) in
            let u = log (concat [«vcs send votes: »; list_tostring word8_tostring votes_data]) in
            let out2_msg_opt = serialise_netsys_output Confirm in
            let out2l = if IS_SOME out2_msg_opt then [(Name_Admin, Msg_Response (Request 0w) $ THE out2_msg_opt)] else []
            in
              ([], d with vcs_state := vcs_state', [out] ++ out2l)
          | NONE => (* TODO prove unreachable *)
            let u = log «vcs cannot merge votes into byte tree» in
              ([], d with vcs_state := vcs_state', []))
    | (Name_Client,Msg_Ballot sign request_id enc_vote) =>
        let u = log «vcs receive client vote» in
        let d' = d with vcs_state updated_by
          (process_vote_cake log fns (sign,enc_vote,request_id))
        in let (vcs_state', out_msgs) = pop_out_msgs_cake d'.vcs_state
        in ([], d' with vcs_state := vcs_state',
          FLAT $ MAP vcs_msg2netsys_msg out_msgs
        )
    | _ =>
        let u = log «vcs: ignore invalid net msg» in ([], d, [])
  )
 /\
 (netsys_net_handler log fns Name_MixNet src m d =
    case (src,m) of
    | (Name_VCS, Msg_Ballots vl) =>
        if IS_NONE d.mixnet_ballots then
          let u = log «mixnet receive ballots» in
            ([], d with mixnet_ballots := SOME vl, [])
        else (* unreachable *)
          let u = log «mixnet: receiving votes twice» in ([], d, [])
    | _ =>
      let u = log «mixnet: ignore invalid net msg» in ([], d, []))
 /\
 (netsys_net_handler log fns Name_Admin src m d =
    let u = log «ignore invalid net msg» in ([], d, []))
 /\
 (netsys_net_handler log fns Name_Client src m d =
  case (src,m) of
  | (Name_VCS,Msg_BallotRecorded request_id voter) =>
      let u = log $ concat [«vcs answers: recorded valid vote »; request_id_tostring request_id] in
      let out_opt = serialise_netsys_output $ Output_BallotRecorded request_id voter in
      let outl = if IS_SOME out_opt then [(Name_Client, Msg_Response request_id $ THE out_opt)] else []
      in
        ([], d, outl)
  | (Name_VCS,Msg_BallotError request_id) =>
      let u = log $ concat [«vcs answers: erroneous vote »; request_id_tostring request_id] in
      let out_opt = serialise_netsys_output $ Output_BallotError request_id in
      let outl = if IS_SOME out_opt then [(Name_Client, Msg_Response request_id $ THE out_opt)] else []
      in
        ([], d, outl)
  | _ =>
      let u = log «ignore invalid net msg» in ([], d, []))
End

Definition netsys_net_handling_def:
  netsys_net_handling fns name src msg data ol data' msgs <=>
    ?log. netsys_net_handler log fns name src msg data = (ol, data', msgs)
End


(* deserialisation of input into the current node from ffi call *)
Datatype:
  requests =
      Input_direct word64 netsys_input
    | Input_network word64 netsys_name netsys_msg
End

val (serialise_requests_def, deserialise_requests_def, _) =
  define_ser_de ``:requests``;

(*
fetch "-" "ser_ok_requests"
fetch "-" "deser_ok_requests"
fetch "-" "deser_imp_ser_requests"
REWRITE_RULE[ser_imp_deser_def] $ fetch "-" "ser_imp_deser_requests"
*)

Datatype:
  response =
    Response word64 ((netsys_name # netsys_msg) list)
  | DeserialiseFail (* failed deserialisation *)
End

val (serialise_response_def, deserialise_response_def, _) =
  define_ser_de ``:response``;

(*
fetch "-" "ser_ok_response"
fetch "-" "deser_ok_response"
fetch "-" "deser_imp_ser_response"
REWRITE_RULE[ser_imp_deser_def] $ fetch "-" "ser_imp_deser_response"
*)

(* the main iteration loop with handlers *)

Definition main_def:
  main log ffi netsys_input_handler netsys_net_handler init_state =
  WHILE (λx. T) (λ(s,answer).
      let _ = log «while loop start»; in
    let
      msg = ffi answer;
    in
      let _ = log «check if msg is none»; in
      if IS_NONE msg
      then
        let _ = log «DeserialiseFail (msg none)»; in (s, DeserialiseFail)
      else
        let
          (id, (trace, s', out)) =
            case THE msg of
            | Input_direct id in_msg =>
              let _ = log «Input_direct»; in
              (id, netsys_input_handler in_msg s id)
            | Input_network id src msg =>
              let _ = log «Input_network»; in
              (id, netsys_net_handler src msg s)
        in
          (s', Response id out)
  ) init_state
End

Definition put_get_def:
  put_get (put_get_ffi : word8 list -> word8 list)
    (response : response) =
  (* serialisation of response is always SOME for small num and short lists *)
  case serialise_response response of
  | NONE => NONE
  | SOME v =>
    (case deserialise_requests $ put_get_ffi v of
    | SOME (r,_) => SOME r (* _ = don't require that deserialise consumes the full byte array *)
    | _ => NONE)
End

(*
  log : (mlstring -> unit)
  fns = (auth_check, format_check)
    : (word8 list -> bool) # (word8 list -> word8 list -> mlstring option)
      # (word8 list -> word8 list)
  self: netsys_name
  ffi : (response) -> (requests) option
    with types as word8 list -> word8 list option
*)
Definition tevd_main_def:
  tevd_main log fns self put_get_ffi =
    main log
      (put_get put_get_ffi)
      (netsys_input_handler log fns self)
      (netsys_net_handler log fns self)
      (netsys_init self, DeserialiseFail) (* init state *)
End

val _ = export_theory ();
