(*====================================================================*)
(*  You-il Kim, The LET Project, KAIST                                *)
(*--------------------------------------------------------------------*)
(*  Copyright(c) 2001 Research On Program Analysis System             *)
(*  National Creative Research Initiative Center                      *)
(*  Korea Advanced Institute of Science & Technology                  *)
(*  http://ropas.kaist.ac.kr                                          *)
(*--------------------------------------------------------------------*)
(*  All rights reserved. This file is distributed under the terms of  *)
(*  an Open Source License.                                           *)
(*====================================================================*)

(*--------------------------------------------------------------------*)
(*  Rabbit lexer for nlex                                             *)
(*--------------------------------------------------------------------*)

(*
    TODO: Rabbit code에 삽입되는 nML code의 처리
*)

{

open Parser

type error = Illegal_character
           | Unterminated_comment
           | Unterminated_nml_string
           | Unterminated_nml_comment

exception Error of error * int * int


(* for debugging *)

val verbose_mode = true

fun print_token (ANAID s) = print_string ("(ANAID "^s^") ")
  | print_token (CTLID s) = print_string ("(CTLID "^s^") ")
  | print_token (LID s)   = print_string ("(LID "^s^") ")
  | print_token (UID s)   = print_string ("(UID "^s^") ")
  | print_token (SID s)   = print_string ("(SID "^s^") ")
  | print_token _ = ()

(* to store the position of the beginning of a string and comment *)

val comment_start_pos = ref 0
val embedded_nml_start_pos = ref 0
val nml_string_start_pos = ref 0
val nml_comment_start_pos = ref 0


(* for nested comments *)

val comment_depth = ref 0
val nml_comment_depth = ref 0


(*--------------------------------------------------------------------*)
(* To buffer string literals (by JungTaek Kim)                        *)
(*--------------------------------------------------------------------*)

val initial_string_buffer = String.create 256
val string_buff = ref initial_string_buffer
val string_index = ref 0

fun reset_string_buffer () =
  (string_buff := initial_string_buffer;
   string_index := 0)

fun store_string_char c =
  (if !string_index >= String.length (!string_buff) then
   (
    let val new_buff = String.create (String.length (!string_buff) * 2)
    in
      String.blit (!string_buff) 0 new_buff 0 (String.length (!string_buff));
      string_buff := new_buff
    end
   );
   String.unsafe_set (!string_buff) (!string_index) c;
   incr string_index)


fun store_string s = 
    for i=0; i<(String.length s); i+1 do 
        store_string_char (String.get s i)
    end


fun get_stored_string () =
  let val s = String.sub (!string_buff) 0 (!string_index)
  in
    string_buff := initial_string_buffer; s
  end

(*--------------------------------------------------------------------*)
(* From misc.ml                                                       *)
(*--------------------------------------------------------------------*)

fun create_hashtable size init =
  let val tbl = Hashtbl.create size
  in
      List.iter (fn (key, data) => Hashtbl.add tbl key data) init;
      tbl
  end

(*--------------------------------------------------------------------*)

val keyword_table =
    create_hashtable 149 [
        ("ana", ANA),
        ("analysis", ANALYSIS),
        ("and", AND),
        ("arrow", ARROW),
        ("as", AS),
        ("atomic", ATOMIC),
        ("bottom", BOTTOM),
        ("case", CASE),
        ("ccr", CCR),
        ("cim", CIM),
        ("constraint", CONSTRAINT),
        ("else", ELSE),
        ("end", END),
        ("eqn", EQN),
        ("false", FALSE),
        ("flat", FLAT),
        ("fn", FN),
        ("from", FROM),
        ("fun", FUN),
        ("if", IF),
        ("in", IN),
        ("index", INDEX),
        ("int", INT),
        ("lattice", LATTICE),
        ("let", LET),
        ("map", MAP),
        ("mp", MP),
        ("not", NOT),
        ("of", OF),
        ("or", OR),
        ("order", ORDER),
        ("post", POST),
        ("power", POWER),
        ("pre", PRE),
        ("product", PRODUCT),
        ("rec", REC),
        ("rhs", RHS),
        ("query", QUERY),
        ("set", SET),
        ("sig", SIG),
        ("signature", SIGNATURE),
        ("sum", SUM),
        ("syntree", SYNTREE),
        ("then", THEN),
        ("top", TOP),
        ("true", TRUE),
        ("val", VAL),
        ("var", VAR),
        ("widen", WIDEN),
        ("with", WITH),
        ("AF", AF),
        ("AG", AG),
        ("AU", AU),
        ("AX", AX),
        ("EF", EF),
        ("EG", EG), 
        ("EU", EU),
        ("EX", EX)
    ]

(*--------------------------------------------------------------------*)
(*  Error Report                                                      *)
(*--------------------------------------------------------------------*)

val report_error = fn
    Illegal_character =>
        print_string "Illegal character"
  | Unterminated_comment =>
        print_string "Comment not terminated"
  | Unterminated_nml_string =>
        print_string "Embbed nML expression not terminated"
  | Unterminated_nml_comment =>
        print_string "nML comment not terminated"
}


(*--------------------------------------------------------------------*)
(*  Tokens                                                            *)
(*--------------------------------------------------------------------*)

val dec = ['0'-'9']+
val hex = '0' ['X' 'x'] ['0'-'9' 'A'-'F' 'a'-'f']+
val oct = '0' ['O' 'o'] ['0'-'7']+
val bin = '0' ['B' 'b'] ['0'-'1']+

val positive_integer = dec | hex | oct | bin
val negative_integer = '-' dec
val integer = positive_integer | negative_integer

(*
ignore ::= \(newline|formfeed|newline formfeed)(space|tab)+

    \009 : horizontal tab '\t'
    \010 : newline '\n'
    \012 : formfeed
    \013 : carrage return 'r'
*)
val ignore   = [' ' '\009' '\013' '\012'] +
val eol      = ['\010' ]

(*
hangul ::= Syllables of KSX1001 (a.k.a. KSC5601 or euc-kr)
         | Syllables of KSX1005-1 (a.k.a. KSC5700, unicode, or ISO/IEC10640-1)
*)
val hangul   = ['\176'-'\200']['\161'-'\254']
		     | ['\172'-'\214']['\000'-'\255']|'\215'['\000'-'\163']

val alphanum = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\''] 
             | hangul

val sym1     = ['%' '&' '$' '#' '\\' '~' '`']

val sym2     = ['!' '%' '&' '$' '#' '+' '-' '/' ':' '<' '=' '>' '?' '@' '\\' 
                '~' '`' '^' '|' '*']

val upper    = ['A'-'Z']
val lower    = ['a'-'z'] | hangul

val lid      = lower alphanum *
val uid      = upper alphanum *
val sid      = sym1 sym2 +


(*--------------------------------------------------------------------*)
(*  Rules                                                             *)
(*--------------------------------------------------------------------*)

rule start = parse

     (* ignore blanks *)
     ignore 
     {	
        start lexbuf
     }

     (* end of line *)
   | eol
     {
        FileInfo.store_line_info (Lexing.lexeme_end lexbuf);
        start lexbuf
     }
     (* keyword or lid *)
   | lid
     {
        let
            val s = Lexing.lexeme lexbuf
            fun token s =
                if (!Parser.check_ctlid) andalso (Parser.is_ctlid s) then
                    (CTLID s)
                else
                    if (!Parser.check_anaid) andalso (Parser.is_anaid s) then
                        (ANAID s)
                    else
                        (LID s)
            val _ = Parser.check_ctlid := false
        in
            FileInfo.set_token_start (Lexing.lexeme_start lexbuf);
            (Hashtbl.find keyword_table s) handle Not_found => token s
        end
     }

     (* keyword or uid *)
   | uid
     {
        let
            val s = Lexing.lexeme lexbuf
            fun token s = 
                if (!Parser.check_ctlid) andalso (Parser.is_ctlid s) then
                    (CTLID s)
                else
                    if (!Parser.check_anaid) andalso (Parser.is_anaid s) then
                        (ANAID s)
                    else
                        (UID s)
            val _ = Parser.check_ctlid := false
        in
            FileInfo.set_token_start (Lexing.lexeme_start lexbuf);
            (Hashtbl.find keyword_table s) handle Not_found => token s
        end
     }

     (* seperator in CCR declaration *)
   | '-' '-' +
     {
        FileInfo.set_token_start (Lexing.lexeme_start lexbuf);
        LINE
     }

     (* integer *)
   | integer
     {
        let
            val s = Lexing.lexeme lexbuf
        in
            FileInfo.set_token_start (Lexing.lexeme_start lexbuf);
            INTNUM (int_of_string s)
        end
     }

     (* nML tylongid/strlongid/pattern/expr *)
   | "/"
     {
        reset_string_buffer ();
        let
            val nml_start = Lexing.lexeme_start lexbuf
        in
            FileInfo.set_token_start (Lexing.lexeme_start lexbuf);
            embedded_nml_start_pos := nml_start;
            embedded_nml lexbuf;
            NMLEXP (get_stored_string())
        end
     }

     (* one line comment *)
   | "//" [^'\n'] *
     {
        start lexbuf
     }

     (* multi line comment *)
   | "(*"
     {
	comment_depth := 1;
        comment_start_pos := Lexing.lexeme_start lexbuf;
        comment lexbuf;
        start lexbuf
     }

     (* reserved symbols *)
   | "_"    { UNDER }
   | "__"   { UNDERUNDER }
   | "("    { LPAREN }
   | ")"    { RPAREN }
   | "{"    { LBRACE }
   | "}"    { RBRACE }
   | "["    { LBRACKET }
   | "]"    { RBRACKET }
   | ":"    { COLON }
   | ","    { COMMA }
   | "*"    { STAR }
   | "+"    { PLUS }
   | "-"    { MINUS }
   | "<-"   { LEFTARROW }
   | "->"   { RIGHTARROW }
   | "<->"  { BOTHARROW }
   | "=>"   { DOUBLEARROW }
   | "@"    { AT }
   | "^"    { HAT }
   | "|"    { BAR }
   | "."    { DOT }
   | "..."  { DOTDOTDOT }
   | "!"    { BANG }
   | "?"    { QUESTION }
   | "<"    { LT }
   | ">"    { GT }
   | "="    { EQ }
   | "<="   { LE }
   | ">="   { GE }

     (* sid *)
   | sid
     {
        let
            val s = Lexing.lexeme lexbuf
            fun token s = 
                if (!Parser.check_ctlid) andalso (Parser.is_ctlid s) then
                    (CTLID s)
                else
                    if (!Parser.check_anaid) andalso (Parser.is_anaid s) then
                        (ANAID s)
                    else
                        (SID s)
            val _ = Parser.check_ctlid := false
        in
            FileInfo.set_token_start (Lexing.lexeme_start lexbuf);
            token s
        end
     }

     (* end of file *)
   | eof    { EOF }

     (* error *)
   | _
     {
        let
            val s = Lexing.lexeme_start lexbuf
            val e = Lexing.lexeme_end lexbuf
        in
            raise (Error (Illegal_character, s, e))
        end
     }

(*--------------------------------------------------------------------*)

and comment = parse

    (* start of nested comment *)
    "(*"
    {
        comment_depth := succ !comment_depth;
        comment lexbuf 
    }

    (* end of comment *)
  | "*)"
    {
        comment_depth := pred !comment_depth;
        if !comment_depth > 0 then comment lexbuf
    }

    (* end of line *)
  | eol
    {
        FileInfo.store_line_info (Lexing.lexeme_end lexbuf);
        comment lexbuf
    }

    (* ignore other char *)
  | _
    {
        comment lexbuf
    }

    (* end of file *)
  | eof
    {
        let
            val s = !comment_start_pos
            val e = s + 2
        in
            raise (Error (Unterminated_comment, s, e))
        end
    }

(*--------------------------------------------------------------------*)

and embedded_nml = parse

    (* end of nML string *)
    '/'
    {
        ()
    }
    (* nML comment *)
   | "(*"
     {
        store_string (Lexing.lexeme lexbuf);
	nml_comment_depth := 1;
        nml_comment lexbuf;
        embedded_nml lexbuf
     }
    (* end of line *)
  | eol
    {
        FileInfo.store_line_info (Lexing.lexeme_end lexbuf);
        store_string_char (Lexing.lexeme_char lexbuf 0);
        embedded_nml lexbuf
    }

    (* store other char *)
  | _
    {
        store_string_char (Lexing.lexeme_char lexbuf 0);
        embedded_nml lexbuf
    }
  
    (* end of file *)	
  | eof
    {
        let
            val s = !embedded_nml_start_pos
            val e = s + 1
        in
            raise (Error (Unterminated_nml_string, s, e))
        end
    }

(*--------------------------------------------------------------------*)

and nml_comment = parse

    (* start of nested comment *)
    "(*"
    {
        store_string (Lexing.lexeme lexbuf);
        nml_comment_depth := succ !nml_comment_depth;
        nml_comment lexbuf 
    }

    (* end of comment *)
  | "*)"
    {
        store_string (Lexing.lexeme lexbuf);
        nml_comment_depth := pred !nml_comment_depth;
        if !nml_comment_depth > 0 then nml_comment lexbuf
    }

    (* end of line *)
  | eol
    {
        FileInfo.store_line_info (Lexing.lexeme_end lexbuf);
        store_string_char (Lexing.lexeme_char lexbuf 0);
        nml_comment lexbuf
    }

    (* ignore other char *)
  | _
    {
        store_string_char (Lexing.lexeme_char lexbuf 0);
        nml_comment lexbuf
    }

    (* end of file *)
  | eof
    {
        let
            val s = !comment_start_pos
            val e = s + 2
        in
            raise (Error (Unterminated_nml_comment, s, e))
        end
    }

(*--------------------------------------------------------------------*)
(*  the end of this file                                              *)
(*--------------------------------------------------------------------*)
