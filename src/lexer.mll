(* 
 *  The lexical analyzer
 *)

{

exception Lexing of Finfo.finfo * string

let info lexbuf =
  Finfo.make_finfo (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf)

let depth    = ref 0

let stringBuffer = ref (String.create 2048)
let stringEnd = ref 0

let resetStr () = stringEnd := 0

let addStr ch =
  let x = !stringEnd in
  let buffer = !stringBuffer
in
  if x = String.length buffer then
    begin
      let newBuffer = String.create (x*2) in
      String.blit buffer 0 newBuffer 0 x;
      String.set newBuffer x ch;
      stringBuffer := newBuffer;
      stringEnd := x+1
    end
  else
    begin
      String.set buffer x ch;
      stringEnd := x+1
    end

let getStr () = String.sub (!stringBuffer) 0 (!stringEnd)

}

let float_literal =
  ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?

rule token = parse
  [' ' '\009' '\012' '\n']+     
| "#!" [^ '\012' '\n']* ['\012' '\n']
    { token lexbuf }
| "*)" 
    { raise (Lexing(info lexbuf, "Unmatched end of comment")) }
| "(*" 
    { depth := 1; comment lexbuf; token lexbuf }
| ['0'-'9']+
| '-'?['0'-'9']+
    { Parser.INTV(int_of_string (Lexing.lexeme lexbuf)) }
| float_literal
| '-'float_literal
    { Parser.FLOATV (float_of_string(Lexing.lexeme lexbuf)) }
| "type" 
    { Parser.TYPE }
| "and" 
    { Parser.AND }
| "fun" 
    { Parser.FUN }
| "match" 
    { Parser.MATCH }
| "with" 
    { Parser.WITH }
| "val" 
    { Parser.VAL }
| "ty" 
    { Parser.TVAL }
| "import" 
    { Parser.IMPORT }
| "import_dtd" 
    { Parser.IMPORT_DTD }
| "let" 
    { Parser.LET }
| "in" 
    { Parser.IN }
| "if" 
    { Parser.IF }
| "then" 
    { Parser.THEN }
| "else" 
    { Parser.ELSE }
| "end" 
    { Parser.END }
| "as" 
    { Parser.AS }
| "extern" 
    { Parser.EXTERN }
| "coerce" 
    { Parser.COERCE }
| "validate" 
    { Parser.VALIDATE }
| "try" 
    { Parser.TRY }
| "raise" 
    { Parser.RAISE }
| "relabel"
    { Parser.RELABEL }
| "copy_label"
    { Parser.COPY_LABEL }
| "caltype"
    { Parser.CALTYPE }
| "case"
    { Parser.CASE }
| "filter"
    { Parser.FILTER }
| "rule"
    { Parser.RULE }
| "namespace"
    { Parser.NAMESPACE }
| "=" 
    { Parser.EQ }
| "(" 
    { Parser.LPAREN }
| ")" 
    { Parser.RPAREN }
| "(:" 
    { Parser.LPARENCOLON }
| ":)" 
    { Parser.COLONRPAREN }
| "[" 
    { Parser.LSQUARE }
| "]" 
    { Parser.RSQUARE }
| "{{" 
    { Parser.LBRACKETBRACKET }
| "}}" 
    { Parser.RBRACKETBRACKET }
| "{"
    { Parser.LBRACKET }
| "}"
    { Parser.RBRACKET }
| "#" 
    { Parser.HASH }
| "||"
    { Parser.BARBAR }
| "|"
    { Parser.BAR }
| "*" 
    { Parser.STAR }
| "+" 
    { Parser.PLUS }
| "-" 
    { Parser.MINUS }
| "/" 
    { Parser.SLASH }
| "\\" 
    { Parser.BACKSLASH }
| "mod" 
    { Parser.MOD }
| "*." 
    { Parser.STARDOT }
| "+." 
    { Parser.PLUSDOT }
| "-." 
    { Parser.MINUSDOT }
| "/." 
    { Parser.SLASHDOT }
| "::>" 
    { Parser.COLONCOLONGT }
| "::" 
    { Parser.COLONCOLON }
| ":" 
    { Parser.COLON }
| ";" 
    { Parser.SEMICOLON }
| "?" 
    { Parser.QUESTION }
| "<:" 
    { Parser.LTCOLON }
| ":>" 
    { Parser.COLONGT }
| "," 
    { Parser.COMMA }
| "->" 
    { Parser.ARROW }
| "<-" 
    { Parser.LARROW }
| "^"
    { Parser.HAT }
| "~"
    { Parser.TILDE }
| "@.."
    { Parser.ATDOTDOT }
| ".."
    { Parser.ATDOTDOT }
| "@"
    { Parser.AT }
| "<"
    { Parser.LT }
| ">"
    { Parser.GT }
| "<="
    { Parser.LTEQ }
| ">="
    { Parser.GTEQ }
| "and"
    { Parser.AND }
| "or"
    { Parser.OR }
| "&"
    { Parser.AMPER }
| "."
    { Parser.DOT }

| ['A'-'Z' 'a'-'z' '_']
  ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*
    { Parser.ID (Lexing.lexeme lexbuf) }

| "\"" { resetStr(); string lexbuf }

| "'" { resetStr(); singlequoted lexbuf }

| eof { Parser.EOF }

| _  { raise (Lexing(info lexbuf, "Illegal character")) }

and comment = parse
  "(*"
    { depth := succ !depth; comment lexbuf }
| "*)"
    { depth := pred !depth; if !depth > 0 then comment lexbuf }
| eof
    { raise (Lexing(info lexbuf, "Comment not terminated")) }
| [^ '\n']
    { comment lexbuf }
| "\n"
    { comment lexbuf }

and string = parse
  '"'  { Parser.STRINGV (getStr()) }
| '\\' { addStr(escaped lexbuf); string lexbuf }
| '\n' { addStr '\n'; string lexbuf }
| eof  { raise (Lexing(info lexbuf, "String not terminated")) }
| _    { addStr (Lexing.lexeme_char lexbuf 0); string lexbuf }

and singlequoted = parse
  '\''  { Parser.SINGLEQUOTED (getStr()) }
| '\\' { addStr(escaped lexbuf); singlequoted lexbuf }
| eof  { raise (Lexing(info lexbuf, "String not terminated")) }
| _    { addStr (Lexing.lexeme_char lexbuf 0); singlequoted lexbuf }

and escaped = parse
  'n'    { '\n' }
| 't'    { '\t' }
| '\\'   { '\\' }
| '"'    { '\034'  }
| '\''   { '\'' }
| ['0'-'9']['0'-'9']['0'-'9']
    {
      let x = int_of_string(Lexing.lexeme lexbuf) in
      if x > 255 then
        raise (Lexing(info lexbuf, "Illegal character constant"))  
      else
        Char.chr x
    }
| [^ '"' '\\' 't' 'n' '\'']
    { raise (Lexing(info lexbuf, "Illegal character constant")) }
