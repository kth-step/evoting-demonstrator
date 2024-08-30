open HolKernel boolLib Parse bossLib listTheory pairTheory combinTheory relationTheory stringTheory finite_mapTheory executionTheory networkTheory VarDPrimaryBackupTheory;

val _ = new_theory "VarDPrimaryBackupProof";

(* ----------------------------- *)
(* semantics-related definitions *)
(* ----------------------------- *)

Definition input_key:
 (input_key (Put k _) = k)
 /\
 (input_key (Get k) = k)
 /\
 (input_key (Del k) = k)
 /\
 (input_key (CAS k _ _) = k)
 /\
 (input_key (CAD k _) = k)
End

Definition operate:
 (operate (Get _) (curr:value option) = (curr, curr))
 /\
 (operate (Put _ v) curr = (SOME v, curr))
 /\
 (operate (Del _) curr = (NONE, curr))
 /\
 (operate (CAS _ v v') curr = if curr = v then (SOME v', curr) else (curr, curr))
 /\
 (operate (CAD _ v) curr = if curr = SOME v then (NONE, curr) else (curr, curr))
End

Definition interpret:
 interpret (k:key) (ops: KV_input list) (init : value option) =
  case ops of
  | [] => (init, init)
  | op::ops => (operate op (FST (interpret k ops init)))
End

Theorem PB_input_handling_handler:
 !h i d ol d' ms.
  PB_input_handling h i d ol d' ms <=>
  PB_input_handler h i d = (ol,d',ms)
Proof
  ntac 2 Cases
  >> rw[PB_input_handling,EQ_IMP_THM]
  >> fs[PB_input_handler,PB_data_component_equality]
  >> BasicProvers.every_case_tac
  >> fs[PB_data_component_equality]
QED

Theorem PB_net_handling_handler:
 !dst src m d ol d' ms.
   PB_net_handling dst src m d ol d' ms <=>
   PB_net_handler dst src m d = (ol,d',ms)
Proof
  ntac 2 Cases
  >> rw[PB_net_handling,EQ_IMP_THM]
  >> gvs[PB_net_handler,PB_data_component_equality,AllCaseEqs(),pairTheory.ELIM_UNCURRY,PB_data_component_equality]
  >> ONCE_REWRITE_TAC[GSYM PAIR]
  >> REWRITE_TAC[CLOSED_PAIR_EQ]
  >> fs[]
QED

(* step executions *)

Definition PB_network_step_execution:
 PB_network_step_execution =
  network_step_execution PB_net_handling PB_input_handling
End

val _ = export_theory ();
