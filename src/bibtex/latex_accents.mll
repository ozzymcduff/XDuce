(* Modified: 2000/07/28 Haruo Hosoya *)

(*
 * bibtex2html - A BibTeX to HTML translator
 * Copyright (C) 1997-2000 Jean-Christophe Filli�tre and Claude March�
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(* $Id: latex_accents.mll,v 1.1.1.1 2001/07/23 02:37:48 hahosoya Exp $ *)

{

  let string_buf = Buffer.create 79
                     
  let add_string s = Buffer.add_string string_buf s

  let add lexbuf = Buffer.add_string string_buf (Lexing.lexeme lexbuf)

}

let space = [ '\t']

rule next_char = parse
  '\\'                          { control lexbuf }
| '{' 
| '}'                           { next_char lexbuf }
| _                             { add lexbuf ; next_char lexbuf }
| eof                           { () }


(* called when we have seen  "\\"  *)

and control = parse
  '"'                { quote_char lexbuf }
| '\''               { right_accent lexbuf }
| '`'                { left_accent lexbuf }
| '^'                { hat lexbuf }
| "c{c}"             { add_string "�" ; next_char lexbuf }
| ("~n"|"~{n}")      { add_string "�"; next_char lexbuf  }
|  _                 { add_string "\\" ; add lexbuf ; next_char lexbuf  }
| eof                { add_string "\\" }

(* called when we have seen  "\\\""  *)
and quote_char = parse
  ('a'|"{a}")                   { add_string "�" ; next_char lexbuf }
| ('o'|"{o}")                   { add_string "�" ; next_char lexbuf }
| ('u'|"{u}")                   { add_string "�" ; next_char lexbuf }
| ('e'|"{e}")                   { add_string "�" ; next_char lexbuf }
| ('A'|"{A}")                   { add_string "�" ; next_char lexbuf }
| ('O'|"{O}")                   { add_string "�" ; next_char lexbuf }
| ('U'|"{U}")                   { add_string "�" ; next_char lexbuf }
| ('E'|"{E}")                   { add_string "�" ; next_char lexbuf }
| ("\\i" space+|"{\\i}")        { add_string "�" ; next_char lexbuf }
| ('I'|"\\I" space+|"{\\I}")    { add_string "�" ; next_char lexbuf }
| _                             { add_string "\\\"" ; add lexbuf }
| eof                           { add_string "\\\"" }

(* called when we have seen  "\\'"  *)
and right_accent = parse
| ('a'|"{a}")   { add_string "�" ; next_char lexbuf }
| ('o'|"{o}")   { add_string "�" ; next_char lexbuf }
| ('u'|"{u}")   { add_string "�" ; next_char lexbuf }
| ('e'|"{e}")   { add_string "�" ; next_char lexbuf }
| ('A'|"{A}")   { add_string "�" ; next_char lexbuf }
| ('O'|"{O}")   { add_string "�" ; next_char lexbuf }
| ('U'|"{U}")   { add_string "�" ; next_char lexbuf }
| ('E'|"{E}")   { add_string "�" ; next_char lexbuf }
| ('i'|"\\i" space+|"{\\i}") { add_string "�" ; next_char lexbuf }
| ('I'|"\\I" space+|"{\\I}") { add_string "�" ; next_char lexbuf }
| _             { add_string "\\'" ; add lexbuf ; next_char lexbuf }
| eof           { add_string "\\'" }

(* called when we have seen "\\`"  *)
and left_accent = parse
  ('a'|"{a}")   { add_string "�" ; next_char lexbuf }
| ('o'|"{o}")   { add_string "�" ; next_char lexbuf }
| ('u'|"{u}")   { add_string "�" ; next_char lexbuf }
| ('e'|"{e}")   { add_string "�" ; next_char lexbuf }
| ('A'|"{A}")   { add_string "�" ; next_char lexbuf }
| ('O'|"{O}")   { add_string "�" ; next_char lexbuf }
| ('U'|"{U}")   { add_string "�" ; next_char lexbuf }
| ('E'|"{E}")   { add_string "�" ; next_char lexbuf }
| ('i'|"\\i" space+ |"{\\i}") { add_string "�" ; next_char lexbuf }
| ('I'|"\\I" space+ |"{\\I}") { add_string "�" ; next_char lexbuf }
| _             { add_string "\\`" ; add lexbuf ; next_char lexbuf }
| eof           { add_string "\\`" }

and hat = parse
  ('a'|"{a}")   { add_string "�" ; next_char lexbuf }
| ('o'|"{o}")   { add_string "�" ; next_char lexbuf }
| ('u'|"{u}")   { add_string "�" ; next_char lexbuf }
| ('e'|"{e}")   { add_string "�" ; next_char lexbuf }
| ('A'|"{A}")   { add_string "�" ; next_char lexbuf }
| ('O'|"{O}")   { add_string "�" ; next_char lexbuf }
| ('U'|"{U}")   { add_string "�" ; next_char lexbuf }
| ('E'|"{E}")   { add_string "�" ; next_char lexbuf }
| ('i'|"\\i" space+ |"{\\i}") { add_string "�" ; next_char lexbuf }
| ('I'|"\\I" space+ |"{\\I}") { add_string "�" ; next_char lexbuf }
| _             { add_string "\\^" ; add lexbuf ; next_char lexbuf }
|  eof          { add_string "\\^" }

{

let normalize s = 
  Buffer.clear string_buf;
  next_char (Lexing.from_string s);
  Buffer.contents string_buf
;;

}
