(*
 Translate the libary code, like networking and crypt
 *)

open preamble basis ml_progTheory astPP fromSexpTheory astToSexprLib
open mlmapTheory comparisonTheory totoTheory
open ByteTreeModuleProgTheory;

val _ = new_theory "TevDLibsProg";

val _ = translation_extends "ByteTreeModuleProg"

fun readfile file =
let
  val fh = TextIO.openIn file;
  val text = TextIO.inputAll fh;
  val _ = TextIO.closeIn fh;
in
  text
end;

(* adds CakeML file to translation *)
fun load_file name =
  let
    val read = readfile name;
    val res = process_topdecs `^read`
  in
    append_prog res
  end;

(*
val files = ["functionslib.cml", "timelib.cml", "cryptffilib.cml", "tevdlib.cml"];
*)
val files = ["functionslib.cml", "cryptffilib.cml", "tevdlib.cml"];
val files = List.map (fn x => "../../../ffi/" ^ x) files;
val loads = List.map load_file files

val _ = export_theory ();
