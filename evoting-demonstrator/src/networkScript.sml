open HolKernel boolLib Parse bossLib listTheory pairTheory combinTheory relationTheory executionTheory;

val _ = new_theory "network";

Datatype:
 packet = <|
   src : 'name
 ; dst : 'name
 ; body : 'msg
 |>
End

Definition create_packet_def:
  create_packet src dst body = <|
   src := src
 ; dst := dst
 ; body := body
 |>
End

Datatype:
 network = <|
   state : 'name -> 'data
 ; packets : ('msg,'name) packet list
 |>
End

Definition send_packets_def:
 send_packets src ps =
  MAP (\m. <| src := src; dst := FST m; body := SND m |>) ps
End

Theorem send_packets_nil:
  send_packets _ [] = []
Proof
  fs[send_packets_def]
QED

Definition network_init_def:
 network_init (init_handlers : 'name -> 'data) : ('data,'msg,'name) network =
 <| packets := [] ; state := init_handlers |>
End

(* https://github.com/uwplse/verdi/blob/master/core/Net.v#L332 *)
Inductive network_step:
[~deliver_msg:]
(!(net : ('data,'msg,'name) network) p xs ys (lb : 'label) d msgs.
 net.packets = xs ++ p::ys /\
 net_handling p.dst p.src p.body (net.state p.dst) lb d msgs ==>
 network_step net_handling input_handling net lb
  (net with
   <| packets := (send_packets p.dst msgs) ++ xs ++ ys
    ; state := (p.dst =+ d) net.state |>))
[~deliver_input:]
(!(net : ('data,'msg,'name) network) h (inp : 'input) (lb : 'label) d msgs.
 input_handling h inp (net.state h) lb d msgs ==>
 network_step net_handling input_handling net lb
  (net with
   <| packets := (send_packets h msgs) ++ net.packets
    ; state := (h =+ d) net.state |>))
End

Definition network_step_execution_def:
 network_step_execution net_handling input_handling =
  step_execution (network_step net_handling input_handling)
End

val _ = export_theory ();
