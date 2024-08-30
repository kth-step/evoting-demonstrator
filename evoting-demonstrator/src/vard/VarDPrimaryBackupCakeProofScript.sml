open preamble ml_translatorLib ml_translatorTheory ml_progLib ml_progTheory mllistTheory mlmapTheory mlprettyprinterTheory comparisonTheory totoTheory basisFunctionsLib executionTheory networkTheory VarDPrimaryBackupTheory VarDPrimaryBackupCakeTheory;

val _ = new_theory "VarDPrimaryBackupCakeProof";

Theorem getk_eq_cake:
 !k d. map_ok d ==>
  getk_cake k d = getk k (to_fmap d) 
Proof
 rw [getk_cake,getk,lookup_thm]
QED

Theorem setk_eq_cake:
 !k v d. map_ok d ==>
  to_fmap (setk_cake k v d) = setk k v (to_fmap d)
Proof
 rw [setk_cake,setk,insert_thm]
QED

Theorem delk_eq_cake:
 !k d. map_ok d ==>
  to_fmap (delk_cake k d) = delk k (to_fmap d)
Proof
 rw [delk_cake,delk,delete_thm]
QED

Theorem VarDHandler_eq_cake_FST:
 !i d. map_ok d ==>
  FST (VarDHandler_cake i d) = FST (VarDHandler i (to_fmap d))
Proof
 Cases_on `i` >>
 rw [VarDHandler_cake,VarDHandler,getk_eq_cake]
QED

Theorem VarDHandler_eq_cake_SND:
 !i d. map_ok d ==>
  to_fmap (SND (VarDHandler_cake i d)) = SND (VarDHandler i (to_fmap d))
Proof
 Cases_on `i` >>
 rw [VarDHandler_cake,VarDHandler,getk_eq_cake,setk_eq_cake,delk_eq_cake]
QED

Theorem VarDHandler_eq_cake:
 !i d x y x' y'. map_ok d ==>
  VarDHandler_cake i d = (x,y) /\
  VarDHandler i (to_fmap d) = (x',y') ==>
  x = x' /\ to_fmap y = y'
Proof
 rw [] >-
  (MP_TAC (Q.SPECL [`i`,`d`] VarDHandler_eq_cake_FST) >>
   rw []) >>
 MP_TAC (Q.SPECL [`i`,`d`] VarDHandler_eq_cake_SND) >>
 rw []
QED

Theorem init_state_cake_eq_cake:
 to_fmap init_state_cake = init_state
Proof
 rw [init_state_cake,init_state,empty_thm]
QED

Definition to_PB_data:
 to_PB_data (PB_data_cake l m) =
  <| queue := l ; state := to_fmap m |>
End

Definition PB_data_ok:
 PB_data_ok (PB_data_cake l m) = map_ok m
End

Definition to_PB_output:
 (to_PB_output (RequestResponse_cake inp out) =
  RequestResponse inp out)
 /\
 (to_PB_output (ReadResponse_cake m) =
  ReadResponse (to_fmap m))
End

Definition to_PB_in_out:
 (to_PB_in_out (n:PB_name,INL (inp:PB_input)) = (n,INL inp))
 /\
 (to_PB_in_out (n,INR out) = (n,INR (to_PB_output out)))
End

Theorem PB_input_handler_eq_cake_data:
 !h i d. PB_data_ok d ==>
  to_PB_data (FST (SND (PB_input_handler_cake h i d))) =
  FST (SND (PB_input_handler h i (to_PB_data d)))
Proof
 strip_tac >> strip_tac >> Cases_on `d` >>
 Cases_on `h` >> Cases_on `i` >>
 rw [PB_data_ok,PB_input_handler_cake,PB_input_handler,to_PB_data,append_queue_def]
QED

Theorem PB_input_handler_eq_cake_msgs:
 !h i d. PB_data_ok d ==>
  SND (SND (PB_input_handler_cake h i d)) =
  SND (SND (PB_input_handler h i (to_PB_data d)))
Proof
 strip_tac >> strip_tac >> Cases_on `d` >>
 Cases_on `h` >> Cases_on `i` >>
 rw [PB_data_ok,PB_input_handler_cake,PB_input_handler,to_PB_data,get_queue_def,append_queue_def]
QED

Theorem PB_input_handler_eq_cake_in_out:
 !h i d. PB_data_ok d ==>
  MAP to_PB_in_out (FST (PB_input_handler_cake h i d)) =
  FST (PB_input_handler h i (to_PB_data d))
Proof
 strip_tac >> strip_tac >> Cases_on `d` >>
 Cases_on `h` >> Cases_on `i` >>
 rw [
  PB_data_ok,PB_input_handler_cake,
  PB_input_handler,to_PB_data,to_PB_in_out,
  get_queue_def,append_queue_def,
  to_PB_output,get_state_def
 ]
QED

Theorem PB_net_handler_eq_cake_in_out:
 !dst src m d. PB_data_ok d ==>
  MAP to_PB_in_out (FST (PB_net_handler_cake dst src m d)) =
  FST (PB_net_handler dst src m (to_PB_data d))
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Cases_on `d` >> Cases_on `dst` >> Cases_on `m` >>
 rw [PB_data_ok,PB_net_handler_cake,PB_net_handler,to_PB_data,get_queue_def] >>
 Cases_on `l` >> fs [to_PB_data] >>
 Cases_on `t` >> rw [to_PB_data,get_state_def] >>
 Cases_on `VarDHandler_cake h m'` >>
 Cases_on `VarDHandler h (to_fmap m')` >>
 rw [to_PB_in_out,to_PB_output] >>
 METIS_TAC [VarDHandler_eq_cake]
QED

Theorem PB_net_handler_eq_cake_data:
 !dst src m d. PB_data_ok d ==>
  to_PB_data (FST (SND (PB_net_handler_cake dst src m d))) =
  FST (SND (PB_net_handler dst src m (to_PB_data d)))
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Cases_on `d` >> Cases_on `dst` >> Cases_on `m` >>
 rw [PB_data_ok,PB_net_handler_cake,PB_net_handler,to_PB_data,get_queue_def] >>
 Cases_on `l` >> fs [to_PB_data] >| [
  Cases_on `t` >> rw [to_PB_data,get_state_def] >-
   (Cases_on `VarDHandler_cake h m'` >>
    Cases_on `VarDHandler h (to_fmap m')` >> rw [to_PB_data] >>
    METIS_TAC [VarDHandler_eq_cake]) >>
  Cases_on `VarDHandler_cake h m'` >>
  Cases_on `VarDHandler h (to_fmap m')` >> rw [to_PB_data] >>
  METIS_TAC [VarDHandler_eq_cake],

  rw [set_state_def,to_PB_data,get_state_def,VarDHandler_eq_cake_SND],

  rw [set_state_def,to_PB_data,get_state_def,VarDHandler_eq_cake_SND]
 ]
QED

Theorem PB_net_handler_eq_cake_msgs:
 !dst src m d. PB_data_ok d ==>
  SND (SND (PB_net_handler_cake dst src m d)) =
  SND (SND (PB_net_handler dst src m (to_PB_data d)))
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Cases_on `d` >> Cases_on `dst` >> Cases_on `m` >>
 rw [PB_data_ok,PB_net_handler_cake,PB_net_handler,to_PB_data,get_queue_def] >>
 Cases_on `l` >> rw [to_PB_data] >>
 Cases_on `t` >> rw [get_state_def] >-
  (Cases_on `VarDHandler_cake h m'` >>
   Cases_on `VarDHandler h (to_fmap m')` >> rw [to_PB_data] >>
   METIS_TAC [VarDHandler_eq_cake]) >>
 Cases_on `VarDHandler_cake h m'` >>
 Cases_on `VarDHandler h (to_fmap m')` >> rw [to_PB_data] >>
 METIS_TAC [VarDHandler_eq_cake]
QED

val _ = export_theory ();
