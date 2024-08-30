(*
  Corresponding to `base64Module.cml`, offers `Base64`

  The chosen dependency is `JsonModuleProg`
*)

open preamble ml_translatorLib ml_translatorTheory ml_progTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib astPP comparisonTheory totoTheory fromSexpTheory JsonModuleProgTheory

val _ = new_theory "Base64ModuleProg";

val _ = translation_extends "JsonModuleProg"; (* chosen order of theory extension *)
val _ = ml_prog_update (open_module "Base64");

val _ = ml_prog_update open_local_block;

val res = append_prog o process_topdecs $ `

  fun int_to_bitlist_acc n =
    if n = 0 then []
    else
      (n mod 2) :: int_to_bitlist_acc (n div 2) ;
  fun int_to_bitlist n = List.rev (int_to_bitlist_acc n) ;

  fun n2l2 n =
    if n < 2 then
      [n mod 2]
    else  (n mod 2) :: n2l2 (n div 2);

  fun normalise_bitlist xs =
    List.dropUntil (fn x => x <> 0) xs ;

  fun bitlist_to_int_acc ls e acc =
    case ls of
      [] => acc
    | (x::xs) =>
        if x > 0 then
          bitlist_to_int_acc xs (e*2) (acc + e)
        else
          bitlist_to_int_acc xs (e*2) acc ;
  fun bitlist_to_int xs =
      bitlist_to_int_acc
        (List.rev (normalise_bitlist xs)) 1 0 ;

  fun padlist padding ls = List.pad_left 0 padding ls ;

  fun take_map n f ls =
    case ls of
      [] => []
    | _ => f (List.take ls n) :: take_map n f (List.drop ls n) ;

  fun base64_enc encoding x =
    let
      val len = List.length x ;
      val padlen = (3 - len) mod 3;
      val bitlist =
        List.concat (List.map (fn x => padlist 8 (int_to_bitlist x)) x) ;
      (* ensure multiple of 3 *)
      val bitlist =
        List.pad_right 0 (8 * len + 2 * padlen) bitlist ;
      val enc = take_map 6 bitlist_to_int bitlist ;
      val enc' =
        List.map Option.valOf
          (List.map (Alist.lookup encoding) enc ) ;
      val padding = List.genlist (fn i => #"=") padlen ;
    in
      enc' @ padding
    end ;

  fun swap x = (snd x,fst x) ;

  fun base64_dec encoding x =
    let
      val x = List.takeUntil (fn x => x = #"=") (String.explode x) ;
      val x =
        List.map Option.valOf
          (List.map (Alist.lookup (List.map swap encoding)) x ) ;
      val len = List.length x ;
      val padlen = (4 - len) mod 4;
      val bitlist =
        List.concat (List.map (fn x => padlist 6 (int_to_bitlist x)) x) ;
      val bitlist = List.take bitlist (6 * len - (padlen * 2)) ;
    in
      take_map 8 bitlist_to_int bitlist
    end ;

  fun base64_str u =
    List.mapi (fn i => fn x => (i,x))
    (String.explode
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/") ;

  fun base64url_str u =
    List.mapi (fn i => fn x => (i,x))
    (String.explode
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_") ;

`

val _ = ml_prog_update open_local_in_block;

val res = append_prog o process_topdecs $ `
  fun dec x = base64_dec (base64_str()) x;
  fun enc x = base64_enc (base64_str()) x;
  fun url_dec x = base64_dec (base64url_str()) x;
  fun url_enc x = base64_enc (base64url_str()) x;
`

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

(*
val _ = astToSexprLib.write_ast_to_file "vard.sexp" prog;
*)

val _ = export_theory ();
