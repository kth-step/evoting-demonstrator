(*
  Corresponding to `jsonModule.cml`, offers `Json`

  Depends on `basisProg`
*)

open preamble ml_translatorLib ml_translatorTheory ml_progTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib astPP comparisonTheory totoTheory fromSexpTheory

val _ = new_theory "JsonModuleProg";

val _ = translation_extends "basisProg";
val _ = ml_prog_update (open_module "Json");

val encode_str = append_prog o process_topdecs $ `
  fun encode_str b s = s;
`

val res = append_prog o process_topdecs $ `
  datatype json =
      Object ((string * json ) list)
    | Array (json list)
    | String string | Number int | Bool bool | Null ;
`

val unstr = append_prog o process_topdecs $ `
  fun unstr s = case s of String s => s | _ => "" ;
`

val unarr = append_prog o process_topdecs $ `
  fun unarr a = case a of Array a => a | _ => [] ;
`

val json_get = append_prog o process_topdecs $ `
  fun json_get key obj =
    case obj of
      Object ls => Alist.lookup ls key
    | _ => None ;
`

val json_getl = append_prog o process_topdecs $ `
  fun json_getl keys obj =
    case keys of
      [] => Some obj
    | x::xs => Option.mapPartial (json_getl xs) (json_get x obj);
`

val json_elem = append_prog o process_topdecs $ `
  fun json_elem n obj =
    case obj of
      Array ls =>
        if n < List.length ls
        then Some (List.nth ls n)
        else None
    | _ => None;
`

val get_path1 = append_prog o process_topdecs $ `
  fun get_path1 path obj =
    case path of
      [] => Some obj
    | x::path =>
        case x of
          Number n =>
            Option.mapPartial (get_path1 path) (json_elem n obj)
        | String key =>
            Option.mapPartial (get_path1 path) (json_get key obj)
        | _ => None;
`

val get_path = append_prog o process_topdecs $ `
  fun get_path path obj =
    case path of
      Array path => get_path1 path obj
    | _ => None;
`

val json_keys = append_prog o process_topdecs $ `
  fun json_keys obj =
    case obj of
      Object ls => Some (List.map fst ls)
    | _ => None ;
`

val toString = append_prog o process_topdecs $ `
  fun toString obj =
    case obj of
        Object mems => String.concat ["{",
            String.concatWith "," (List.map memToString mems),
            "}" ]
        | Array obs => String.concat ["[",
            String.concatWith "," (List.map toString obs),
            "]"]
        | String s => String.concat ["\"", encode_str True s, "\""]
        | Number i => Int.toString i
        | Bool b => if b then "true" else "false"
        | Null => "null"
        | _ => "null"
  and memToString n_obj = let
    val key = fst n_obj
    val obj = snd n_obj in
      String.concat ["\"", key, "\":", toString obj]
  end ;
`

val spaces = append_prog o process_topdecs $ `
  fun spaces n = String.concat (List.genlist (fn x => "  ") n) ;
`

val _ = ml_prog_update open_local_block;

val pretty_printing = append_prog o process_topdecs $ `
  fun esc () = String.str (Char.chr 27);
  fun reset () = (esc()) ^ "[0m";
  fun black () = (esc()) ^ "[1;39m"; (* [{,: bold default *)
  fun green () = (esc()) ^ "[0;35m"; (* keys *)
  fun yellow () = (esc()) ^ "[0;33m"; (* strings *)
  fun num_bool () = (esc()) ^ "[0;36m"; (* numbers bool *)
  fun ifc b col = if b then col else "";
`

val toString_fuller = append_prog o process_topdecs $ `
  (* indent level colour object  *)
  fun toString_fuller level c in_arr obj =
    case obj of
        Object mems =>
          String.concat [ifc in_arr (spaces level), ifc c (black())]
          ^ (if List.null mems then "{}"
            else String.concat
              ["{\n", ifc c (reset()),
                String.concatWith ((ifc c (black())) ^ ",\n" ^ (ifc c (reset())))
                  (List.map (mem_to_string_fuller (level+1) c) mems),
                "\n", spaces level, ifc c (black()), "}"])
          ^ ifc c (reset())
        | Array obs =>
          String.concat [ifc in_arr (spaces level), ifc c (black())]
          ^ (if List.null obs then "[]"
            else String.concat
              ["[\n", ifc c (reset()),
                String.concatWith ((ifc c (black())) ^ ",\n" ^ (ifc c (reset())))
                  (List.map (toString_fuller
                  (level + 1)
                    c True) obs),
                "\n", spaces level, ifc c (black()), "]"])
          ^ ifc c (reset())
        | String s =>  (ifc in_arr (spaces level)) ^ String.concat
            [ifc c (yellow()), "\"", encode_str True s, "\"", ifc c (reset())]
        | Number i => (ifc in_arr (spaces level)) ^ (ifc c (num_bool())) ^
        (Int.toString i) ^ (ifc c (reset()))
        | Bool b => (ifc in_arr (spaces level)) ^ (ifc c (num_bool())) ^ (if b then
          "true" else "false") ^ (ifc c (reset()))
        | Null => (ifc in_arr (spaces level)) ^ (ifc c (num_bool())) ^ "null" ^ (ifc
        c (reset()))
  and mem_to_string_fuller level c n_obj = let
    val key = fst n_obj
    val obj = snd n_obj in
      String.concat [spaces level, ifc c (green()), "\"" ^ key ^ "\"", ifc c (reset()),
        ifc c (black()), ": ", ifc c (reset()),
        toString_fuller level c False obj]
  end;
`

val _ = ml_prog_update open_local_in_block;

val toString_pretty = append_prog o process_topdecs $ `
  fun toString_pretty c json = toString_fuller 0 c True json
`

val _ = ml_prog_update close_local_blocks;

val token = append_prog o process_topdecs $ `
  datatype token =
      OBJOPEN | OBJCLOSE | COLON
    | ARROPEN | ARRCLOSE | COMMA
    | Str string | NUM int | BOOL bool | NULL ;
`

val is_whitespace = append_prog o process_topdecs $ `
  fun is_whitespace c = List.member c (List.map (fn x => Char.chr x) [32, 10, 13, 9])
`

val isAlpha = append_prog o process_topdecs $ `
  fun isAlpha c =
    Char.<= #"A" c andalso Char.<= c #"Z" orelse
    Char.<= #"a" c andalso Char.<= c #"z";
`

val isHexLetter = append_prog o process_topdecs $ `
  fun isHexLetter c =
    Char.<= #"A" c andalso Char.<= c #"F" orelse
    Char.<= #"a" c andalso Char.<= c #"f";
`

val isDigit = append_prog o process_topdecs $ `
  fun isDigit c = Char.<= #"0" c andalso Char.<= c #"9";
`

val isHexDigit = append_prog o process_topdecs $ `
  fun isHexDigit c = isDigit c orelse isHexLetter c ;
`

val lex_bool = append_prog o process_topdecs $ `
  fun lex_bool cs =
      case cs of
        #"t"::(#"r"::(#"u"::(#"e"::cs))) => Some (BOOL True, cs)
      | #"f"::(#"a"::(#"l"::(#"s"::(#"e"::cs)))) => Some (BOOL False, cs)
      | _ => None ;
`

val lex_null = append_prog o process_topdecs $ `
  fun lex_null cs =
      case cs of
        #"n"::(#"u"::(#"l"::(#"l"::cs))) => Some (NULL, cs)
      | _ => None ;
`

val lex_escape_innards = append_prog o process_topdecs $ `
  fun lex_escape_innards cs =
    case cs of
      [] => None
    | c::cs =>
      (if List.member c (String.explode "\"/\\bfnrt") then Some (c::(#"\\"::[]),cs)
      else if c <> #"u" then None else
      case cs of
        a::(b::(c::(d::cs))) =>
        if List.all isHexDigit [a,b,c,d]
        then Some ([d,c,b,a,#"u",#"\\"], cs)
        else None
      | _ => None)
`

val is_control_char = append_prog o process_topdecs $ `
  fun is_control_char c = Char.< c #" ";
`

val lex_str = append_prog o process_topdecs $ `
  fun lex_str cs acc =
    case cs of
      [] => None
    | c::cs =>
      if is_control_char c then None
      else if c <> #"\\" then
        if c = #"\"" then
          Some (Str (String.implode (List.rev acc)), cs)
        else lex_str cs (c::acc)
      else
        case lex_escape_innards cs of
          None => None
        | Some (esc, cs) => lex_str cs (esc @ acc) ;
`

val lex_num = append_prog o process_topdecs $ `
  fun lex_num cs acc =
    case cs of
      [] => (acc,[])
    | c::cs =>
      if isDigit c then
        lex_num cs (acc * 10 + (Char.ord c - Char.ord #"0"))
      else (acc, c::cs) ;
`

val lex = append_prog o process_topdecs $ `
  fun lex cs acc =
    case cs of
      ([]:char list) => ((Inl acc) : (token list, string) sum)
    | c::cs =>
      if is_whitespace c then lex cs acc
      else if c = #":" then lex cs (COLON::acc)
      else if c = #"," then lex cs (COMMA::acc)
      else if c = #"{" then lex cs (OBJOPEN::acc)
      else if c = #"}" then lex cs (OBJCLOSE::acc)
      else if c = #"[" then lex cs (ARROPEN::acc)
      else if c = #"]" then lex cs (ARRCLOSE::acc)
      else if c = #"\"" then
        case lex_str cs [] of
          Some (tok, cs) => lex cs (tok::acc)
        | None => Inr ("invalid string: " ^ (String.implode (List.take (c::cs) 10)))
      else if c = #"t" orelse c = #"f" then
        case lex_bool (c::cs) of
          Some (tok, cs) => lex cs (tok::acc)
        | None => Inr ("unexpected characters: " ^ (String.implode (List.take (c::cs) 10)))
      else if c = #"n" then
        case lex_null (c::cs) of
          Some (tok, cs) => lex cs (tok::acc)
        | None => Inr ("unexpected characters: " ^ (String.implode (List.take (c::cs) 10)))
      else let
          val x = lex_num (c::cs) 0
          val num = fst x
          val cs' = snd x
        in
          if cs' = c::cs then
            Inr ("unexpected characters: " ^ (String.implode (List.take (c::cs) 10)))
          else lex cs' ((NUM num)::acc)
        end;
`

val parsestack = append_prog o process_topdecs $ `
  datatype parsestack =
    OBJV json ((string * json) list) | OBJ ((string * json) list) | ARR (json list)
;
`

val parse = append_prog o process_topdecs $ `
  fun parse (ts :token list) (ns : parsestack list) (expect_val : bool) =
    case ts of
      [] => Inl "unexpected EOF"
    | NULL::ts =>
        if not expect_val then
          Inl "unexpected null"
        else
          (case ns of
            (OBJ acc)::ns => parse ts ((OBJV Null acc)::ns) False
          | (ARR acc)::ns => parse ts ((ARR (Null::acc))::ns) False
          | ns => Inr (Null, ts, ns))
    | (BOOL b)::ts =>
        if not expect_val then
          Inl "unexpected boolean"
        else
          (case ns of
            (OBJ acc)::ns => parse ts ((OBJV (Bool b) acc)::ns) False
          | (ARR acc)::ns => parse ts ((ARR ((Bool b)::acc))::ns) False
          | ns => Inr (Bool b, ts, ns))
    | (Str s)::ts =>
      if not expect_val then
        Inl "unexpected string"
      else
        (case ns of
          (OBJ acc)::ns => parse ts ((OBJV (String s) acc)::ns) False
        | (ARR acc)::ns => parse ts ((ARR ((String s)::acc))::ns) False
        | ns => Inr (String s, ts, ns))
    | (NUM n)::ts =>
      if not expect_val then
        Inl "unexpected number"
      else
        (case ns of
          (OBJ acc)::ns => parse ts ((OBJV (Number n) acc)::ns) False
        | (ARR acc)::ns => parse ts ((ARR ((Number n)::acc))::ns) False
        | ns => Inr (Number n, ts, ns))
    | OBJCLOSE::(OBJOPEN::ts) =>
      if not expect_val then
        Inl "unexpected object {}"
      else
        (case ns of
          (OBJ acc)::ns => parse ts ((OBJV (Object []) acc)::ns) False
        | (ARR acc)::ns => parse ts ((ARR ((Object [])::acc))::ns) False
        | ns => Inr (Object [], ts, ns))
    | OBJCLOSE::ts =>
      if not expect_val then
        Inl "unexpected }"
      else parse ts ((OBJ [])::ns) True
    | ARRCLOSE::(ARROPEN::ts) =>
      if not expect_val then
        Inl "unexpected empty array []"
      else
        (case ns of
          (OBJ acc)::ns => parse ts ((OBJV (Array []) acc)::ns) False
        | (ARR acc)::ns => parse ts ((ARR ((Array [])::acc))::ns) False
        | ns => Inr (Array [], ts, ns))
    | ARRCLOSE::ts =>
      if not expect_val then
        Inl "unexpected ]"
      else parse ts ((ARR [])::ns) True
    | ARROPEN::ts =>
        if expect_val then
          Inl "unexpected ["
        else
          (case ns of
            ((ARR aacc)::(OBJ oacc)::ns) => parse ts ((OBJV (Array aacc) oacc)::ns) False
          | ((ARR acc)::(ARR acc')::ns) => parse ts ((ARR ((Array acc)::acc'))::ns) False
          | ((ARR acc)::ns) => Inr (Array acc, ts, ns))
    | COMMA::ts =>
      if expect_val then
        Inl "unexpected comma"
      else
        (case ns of
          (ARR acc)::ns => parse ts ((ARR acc)::ns) True
        | _ => Inl "unexpected comma (outside an array)")
    | COLON::((Str s)::(COMMA::ts)) =>
      if expect_val then
        Inl "unexpected comma"
      else
        (case ns of
          (OBJV v acc)::ns => parse ts ((OBJ ((s,v)::acc))::ns) True
        | _ => Inl "unexpected comma")
    | COLON::((Str s)::(OBJOPEN::ts)) =>
      if expect_val then
        Inl "unexpected colon"
      else
        (case ns of
          (OBJV v oacc)::((ARR aacc)::ns) =>
            parse ts ((ARR ((Object ((s,v)::oacc))::aacc))::ns) False
        | (OBJV v acc)::((OBJ acc')::ns) =>
            parse ts ((OBJV (Object ((s,v)::acc)) acc')::ns) False
        | (OBJV v acc)::ns => Inr (Object ((s,v)::acc), ts, ns)
        | _ => Inl "unexpected colon")
    | _ => Inl "error" ;
`

val parseerror = append_prog o process_topdecs $ `
  exception ParserError string;
`

val lexerror = append_prog o process_topdecs $ `
  exception LexerError string;
`

val parser = append_prog o process_topdecs $ `
  fun parser str =
    case lex (String.explode str) [] of
      Inr msg => raise LexerError msg
    | Inl ts =>
        (case parse ts [] True of
          Inl msg => raise ParserError msg
        | Inr (json_v, [], []) => json_v
        | Inr (_, _, _) => raise ParserError "parser error") ;
`

val _ = ml_prog_update (close_module NONE);

(*
val _ = astToSexprLib.write_ast_to_file "vard.sexp" prog;
*)

val _ = export_theory ();
