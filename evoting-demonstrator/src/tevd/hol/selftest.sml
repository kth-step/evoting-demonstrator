open HolKernel Parse boolLib bossLib
open wordsLib TevDNetworkedSystemTheory;

val ERR = mk_HOL_ERR "selftest"

(* selftest setup from $HOLDIR/examples/arm/v7/selftest.sml *)
val _ = wordsLib.guess_lengths();

val _ = set_trace "Unicode" 0;
val _ = set_trace "notify type variable guesses" 0;
val _ = set_trace "notify word length guesses" 0;

fun die() = ()
fun die() = OS.Process.exit OS.Process.failure

fun test str f x = let
  val rt = Timer.startRealTimer ()
  val res = Lib.total f x
  val elapsed = Timer.checkRealTimer rt
in
  TextIO.print ("" ^ str ^ " ... " ^ Time.toString elapsed ^ "s" ^
                (case res of NONE => "FAILED!\n" | _ => "\n"));
  case res of NONE => die() | _ => ()
end

val testfn = List.map (fn (tm,expect) =>
  let
    val evl = EVAL o Term $ `^(tm) = ^(expect)`
    val trhs = evl |> concl
  in
    if (trhs |> rand |> curry Term.compare ``T``) = EQUAL
    then ()
    else raise mk_HOL_ERR "testfn" "error in test" ""
  end
);

val _ = print "Starting tests ... \n";

val tt = Timer.startRealTimer ();

test "serialise netsys_name" testfn [
  (``serialise_netsys_name Name_VCS``, ``SOME [0w:word8]``),
  (``serialise_netsys_name Name_MixNet``, ``SOME [1w:word8]``)
];

test "serialise response" testfn [
  (``serialise_response $ Response 42w [(Name_MixNet, Msg_VotingStart [])]``, ``SOME [0w:word8; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 42w; 1w; 1w; 0w; 0w]``),
  (``serialise_response $ Response 2001w [(Name_MixNet,Msg_BallotRecorded (Request 1w) (Voter «abc»))]``, ``SOME [0w:word8; 0w; 0w; 0w; 0w; 0w; 0w; 7w; 209w; 1w; 1w; 3w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 1w; 0w; 3w; 97w; 98w; 99w]``)
];

test "serialise requests" testfn [
  (``serialise_requests $ Input_network 380w Name_MixNet Msg_Confirm``, ``SOME [1w:word8; 0w; 0w; 0w; 0w; 0w; 0w; 1w; 124w; 1w; 7w]``)
];

val elapsed = Timer.checkRealTimer tt;

val _ = print ("Total time: " ^ Lib.time_to_string elapsed ^ "\n");

val _ = OS.Process.exit OS.Process.success;
