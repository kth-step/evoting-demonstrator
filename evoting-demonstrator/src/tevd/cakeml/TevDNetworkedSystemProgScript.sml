(*
   Extracts the TevDNetworkedSystem to an sexp
*)

open preamble basis ml_progTheory astPP fromSexpTheory astToSexprLib
open mlmapTheory comparisonTheory totoTheory
     serialiseTheory TevDNetworkedSystemTheory
     TevDNetworkedSystemModuleProgTheory TevDLibsProgTheory;

val _ = new_theory "TevDNetworkedSystemProg";

val _ = translation_extends "TevDNetworkedSystemModuleProg"

val res = append_prog o process_topdecs $ `
fun put_get_ffi (input : Word8.word list) =
let
  val max_length = 38960;
  val header_len = 0;
  val buf_data_len = max_length - header_len;
  val buf_len = buf_data_len + header_len;
  val _ = println "[cml put_get_ffi] before Word8Array.array"
  val buf = Word8Array.array buf_len (Word8.fromInt 0)
  (* copy input into buf *)
  (* val _ = Marshalling.n2w2 buf_data_len buf 0; *)
  val _ = println "[cml put_get_ffi] before mapi"
  val _ = List.mapi (fn i => fn x => Word8Array.update buf (i + header_len) x)
    (List.take input (min buf_data_len (List.length input)))
  val _ = #(put_get) "" buf
  (* TODO add header to the buffer data (to avoid copying the full buffer) *)
  (* val length = min (Marshalling.w22n buf 0) max_length; *)
  val _ = print "[cml put_get_ffi] buf_list:"
  val buf_list =
    List.genlist (fn i => Word8Array.sub buf i) buf_len
  val buf_str_list = List.map (Int.toString o Word8.toInt) buf_list;
  val _ = List.map (fn x => print (" " ^ x)) (List.take buf_str_list 30)
  val _ = print "\n"
in
  (* assume no header offset *)
  buf_list
end;

fun get_self () =
let
  val header_length = 0;
  val data_length = 1;
  val buf = Word8Array.array (header_length + data_length) (Word8.fromInt 0);
  val _ = #(get_self) "" buf
  val length = data_length - header_length;
  val w8list = List.genlist (fn i => Word8Array.sub buf (i + header_length)) length
  val (name,_) = Option.valOf (TevDNetworkedSystem.deserialise_netsys_name w8list)
in
  name
end;
`;

(*
  log : (mlstring -> unit)
  fns = (auth_check, format_check)
    : (word8 list -> bool) # (word8 list -> word8 list -> mlstring option)
  self: netsys_name
  ffi : response -> requests
*)
val res = append_prog o process_topdecs $ `
fun main () =
let
  val self = get_self();
  val self_str = TevDNetworkedSystem.name_tostring self;
  val log = logid 5 self_str;
  val logfn = log "main";
  val _ = logfn 1 ("cml node id: " ^ self_str);
  (*
  val pub = if self = TevDNetworkedSystem.Name_vcs
    then (let
      val _ = logfn 3 "vcs: loading public key from file 'signing.pub'"
      in string_to_byte_list (readfile "signing.pub") end)
    else [];
  val _ = logfn 1 ("pub len: " ^ Int.toString (List.length pub));
  *)
  val fns = (auth_check log, (format_check log, TevDNetworkedSystem.transform));
  val _ = TevDNetworkedSystem.tevd_main (logfn 3) fns self put_get_ffi
in () end
`;

val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

val _ = astToSexprLib.write_ast_to_file "tevdProg.sexp" prog;

val _ = export_theory ();
