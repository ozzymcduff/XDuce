/*  
 *  Yacc grammar for the parser.  The files parser.mli and parser.ml
 *  are generated automatically from parser.mly.
 */

%{

open Syn
open Parsing
open Finfo
open Base

let parseFile : (string -> string -> unit) ref = 
  ref (fun x y -> ())

let info() = make_finfo (symbol_start()) (symbol_end())
let info_rhs s e = make_finfo (rhs_start s) (rhs_end e)

let (prefix_stack : string Stack.t) = Stack.create ()
let cur_prefix = ref ""

let import_file alist fname =
  let prefix = try List.assoc "prefix" alist with Not_found -> "" in
  Stack.push !cur_prefix prefix_stack;
  cur_prefix := prefix ^ !cur_prefix;
  !parseFile !cur_prefix fname;
  cur_prefix := Stack.pop prefix_stack

let intern_prefix x = Synutil.intern (!cur_prefix ^ x)

let intern_bltin x =
  try let _ = Bltin.lookup_builtin x in Synutil.intern x
  with Bltin.Bltin_not_found _ -> intern_prefix x

let any_type x = (x = "Any" or x = "AnyAttrs")

let handle_tyvar x =
  if any_type x then TVar (info(), Synutil.intern x)
  else
    match basety_of_string x with
      | Some basety -> TBase (info(), basety)
      | None -> TVar (info(), intern_prefix x)

let handle_pvar x =
  if any_type x then TVar (info(), Synutil.intern x)
  else
    match basety_of_string x with
      | Some basety -> TBase (info(), basety)
      | None -> TVar (info(), intern_prefix x)

let rec erase_prefix nset =
  match nset with
  | NQName("", ln) -> NQName("emptyprefix", ln)
  | NNSName "" -> NNSName "emptyprefix"
  | NQName _ | NNSName _ | NAnyName -> nset
  | NOr(nset1, nset2) -> NOr(erase_prefix nset1, erase_prefix nset2)
  | NDiff(nset1, nset2) -> NDiff(erase_prefix nset1, erase_prefix nset2)

%}

%token <string> STRINGV
%token <int> INTV
%token <float> FLOATV
%token <string> ID
%token <string> SINGLEQUOTED

/* key words */

%token TYPE AND FUN MATCH WITH VAL TVAL EXTERN TRY RAISE CALTYPE CASE 
%token FILTER RULE NAMESPACE
%token IMPORT LET IN IF THEN ELSE END AS AND OR
%token IMPORT_DTD 
%token COERCE VALIDATE RELABEL COPY_LABEL

/* symbols */

%token EQ BAR HASH STAR COLON COLONCOLON LTCOLON COLONCOLONGT COLONGT BARBAR
%token QUESTION COMMA SEMICOLON
%token HAT DOT SLASH BACKSLASH MOD PLUS MINUS STARDOT SLASHDOT PLUSDOT MINUSDOT
%token TILDE AT GT LT GTEQ LTEQ ATDOTDOT DOTDOT
%token LPAREN RPAREN LSQUARE RSQUARE LBRACKETBRACKET RBRACKETBRACKET
%token ARROW LARROW
%token AMPER LBRACKET RBRACKET DOT
%token LPARENCOLON COLONRPAREN

/* special tokens */

%token EOF

/* priorities */

%right prec_let
%right prec_match
%left SEMICOLON
%right prec_if
%left BARBAR
%left BAR
%left AMPER BACKSLASH
%left COMMA
%left LT GT LTEQ GTEQ EQ AND OR
%left PLUS MINUS PLUSDOT MINUSDOT HAT
%left STAR SLASH MOD STARDOT SLASHDOT

%start parse

%type <(string -> string -> unit) -> unit> parse

%%

/* toplevel */

parse :
    toplevel
      { fun f -> parseFile := f; $1 }

toplevel :
     /* empty */
       { () } 
   | tydef toplevel
       { Top.top.top_tydefs <- $1 :: Top.top.top_tydefs }
   | fundef toplevel
       { Top.top.top_fundefs <- $1 :: Top.top.top_fundefs }
   | bltin toplevel
       { Top.top.top_bltins <- $1 :: Top.top.top_bltins }
   | valdef toplevel
       { Top.top.top_valdefs <- $1 :: Top.top.top_valdefs }
   | IMPORT import_dtd_param_form STRINGV toplevel
       { import_file $2 $3 }
   | IMPORT_DTD import_dtd_param_form STRINGV toplevel
       { Parsedtd.parse_dtd (info()) !cur_prefix $2 $3 }
   | NAMESPACE var EQ STRINGV toplevel
       { Top.top.top_nsdefs <- (info(), $2, $4) :: Top.top.top_nsdefs }
   | NAMESPACE EQ STRINGV toplevel
       { Top.top.top_nsdefs <- (info(), "", $3) :: Top.top.top_nsdefs }
   | CALTYPE atom_ty AMPER atom_ty toplevel
       { Top.top.top_caltype <- ("isect", [$2; $4]) :: Top.top.top_caltype }
   | CALTYPE atom_ty BACKSLASH atom_ty toplevel
       { Top.top.top_caltype <- ("diff", [$2; $4]) :: Top.top.top_caltype }
   | CALTYPE atom_ty LTCOLON atom_ty toplevel
       { Top.top.top_caltype <- ("sub", [$2; $4]) :: Top.top.top_caltype }
   | CALTYPE atom_ty AMPER AMPER atom_ty toplevel
       { Top.top.top_caltype <- ("inf", [$2; $5]) :: Top.top.top_caltype }
   | CALTYPE atom_ty toplevel
       { Top.top.top_caltype <- ("disp", [$2]) :: Top.top.top_caltype }

import_dtd_param_form :
   | /* empty */
       { [] } 
   | LPAREN import_dtd_params RPAREN
       { $2 }

import_dtd_params :
   | /* empty */
     { [] } 
   | var EQ STRINGV import_dtd_params
       { ($1, $3) :: $4 }
   | NAMESPACE EQ STRINGV import_dtd_params
       { ("namespace", $3) :: $4 }

/* type definitions */

tydef :
  | TYPE var EQ ty
      { (info(), intern_prefix $2, $4) }
      
/* function definitions */

fundef :
  | FUN var atom_pat_list COLON ty EQ expr
       { (info(), intern_prefix $2, [], $3, $5, $7) }
  | FUN var LBRACKETBRACKET var_list RBRACKETBRACKET atom_pat_list COLON ty EQ expr
       { (info(), intern_prefix $2, $4, $6, $8, $10) }

var_list :
  | var 
      { [$1] }
  | var COMMA var_list
      { $1 :: $3 }

atom_pat_list :
  | atom_pat
      { [($1, ref (-1))] }
  | atom_pat atom_pat_list
      { ($1, ref (-1)) :: $2 }

/* external function definitions */

bltin :
  | EXTERN var COLON atom_ty_list ARROW ty
      { let f = Bltin.lookup_builtin $2 in
        (info(), $2, [], $4, $6, f) }
  | EXTERN var COLON LBRACKETBRACKET var_list RBRACKETBRACKET atom_ty_list ARROW ty
      { let f = Bltin.lookup_builtin $2 in
        (info(), $2, $5, $7, $9, f) }
      
atom_ty_list :
  | atom_ty
      { [$1] }
  | atom_ty atom_ty_list
      { $1 :: $2 }

/* queries */

valdef :
  | LET pat EQ expr
      { (info(), $2, ref (-1), $4) }

/* variables */

var :
  | ID
      { $1 }

/* labels */

label :
  | ID
      { $1 }
  | SINGLEQUOTED
      { $1 }

full_labset:
   | atom_labset
       { $1 }
   | full_labset BAR full_labset
       { NOr($1, $3) }
   | full_labset BACKSLASH full_labset
       { NDiff($1, $3) }

atom_labset:
   | label
       { NQName("", Sym.label $1) }
   | label COLON label
       { NQName($1, Sym.label $3) }
   | label COLON TILDE
       { NNSName $1 }
   | TILDE 
       { NAnyName }
   | HAT atom_labset
       { NDiff(NAnyName, $2) }
   | LPAREN full_labset RPAREN
       { $2 }

labset:
   | label 
       { NQName("", Sym.label $1) }
   | label COLON label
       { NQName($1, Sym.label $3) }
   | label COLON TILDE
       { NNSName $1 }
   | TILDE 
       { NAnyName }
   | TILDE atom_labset
       { $2 }
   | HAT atom_labset
       { NDiff(NAnyName, $2) }

/* types */

ty :
   | as_ty
       { $1 }
   | ty BAR ty
       { TUnion(info(), $1, $3) }
   | ty AMPER ty
       { assert false }
   | ty COMMA ty
       { TCat(info(), $1, $3) }

as_ty :
   | TVAL var AS lab_ty
       { TTyAs (info(), intern_prefix $2, $4) }
   | TVAL var
       { TTyAs (info(), intern_prefix $2, TVar(bogus(), "AnyElm")) }
   | lab_ty
       { $1 }

lab_ty :
   | labset LSQUARE emp_ty RSQUARE
       { TLab (info(), $1, $3) }
   | AT atom_labset LSQUARE emp_ty RSQUARE
       { TAtt (info(), erase_prefix $2, $4) }
   | lab_ty STAR
       { TClos (info(), $1) }
   | lab_ty QUESTION
       { TUnion (info(), $1, TEmpty(info())) }
   | lab_ty PLUS
       { TClos1 (info(), $1) }
   | lab_ty LBRACKETBRACKET var ARROW ty RBRACKETBRACKET
       { TSubst (info(), $1, $3, $5) }
   | atom_ty
       { $1 }

atom_ty :
   | var 
       { handle_tyvar $1 }
   | ATDOTDOT 
       { TAttRem(info()) }
   | DOTDOT 
       { handle_tyvar "AnyElms" }
   | STRINGV
       { TSingle(info(), BVString $1) }
   | INTV
       { TSingle(info(), BVInt $1) }
   | FLOATV
       { TSingle(info(), BVFloat $1) }
   | LPAREN emp_ty RPAREN
       { $2 }

emp_ty :
   | /* empty */
       { TEmpty (info()) }
   | ty
       { $1 }

/* patterns */

pat :
   | as_pat
       { $1 }
   | pat BAR pat
       { TUnion(info(), $1, $3) }
   | pat AMPER pat
       { assert false }
   | pat COMMA pat
       { TCat(info(), $1, $3) }

as_pat :
   | TVAL var AS lab_pat
       { TTyAs (info(), intern_prefix $2, $4) }
   | TVAL var
       { TTyAs (info(), intern_prefix $2, TVar(bogus(), "AnyElm")) }
   | VAL var AS lab_pat
       { TAs (info(), intern_prefix $2, $4) }
   | VAL var
       { TAs (info(), intern_prefix $2, TVar(bogus(), "Any")) }
   | lab_pat AS var
       { TAs (info(), intern_prefix $3, $1) }
   | lab_pat
       { $1 }

lab_pat :
   | labset LSQUARE emp_pat RSQUARE
       { TLab( (info()), $1, $3) }
   | AT atom_labset LSQUARE emp_pat RSQUARE
       { TAtt (info(), erase_prefix $2, $4) }
   | lab_pat STAR
       { TClos (info(), $1) }
   | lab_pat QUESTION
       { TUnion (info(), $1, TEmpty(info())) }
   | lab_pat PLUS
       { TClos1 (info(), $1) }
   | lab_pat LBRACKETBRACKET var ARROW pat RBRACKETBRACKET
       { TSubst (info(), $1, $3, $5) }
   | atom_pat
       { $1 }

atom_pat :
   | var 
       { handle_pvar $1 }
   | ATDOTDOT 
       { TAttRem(info()) }
   | DOTDOT 
       { handle_pvar "AnyElms" }
   | STRINGV
       { TSingle(info(), BVString $1) }
   | INTV
       { TSingle(info(), BVInt $1) }
   | FLOATV
       { TSingle(info(), BVFloat $1) }
   | LPAREN emp_pat RPAREN
       { $2 }

emp_pat :
   | /* empty */
       { TEmpty (info()) }
   | pat
       { $1 }

/* regular expression clauses */

filter :
   | bar_filter
       { $1 }

bar_filter :
   | bar_filter BAR bar_filter
       { TUnion(info(), $1, $3) }
   | bar_filter BARBAR bar_filter
       { TUnionF(info(), $1, $3) }
   | comma_filter LBRACKET expr RBRACKET
       { TRule(info(), $1, $3, Syn.next_filter_id()) }
   | comma_filter
       { $1 }

comma_filter :
   | comma_filter COMMA comma_filter
       { TCat(info(), $1, $3) } 
   | VAL var AS lab_filter
       { TAs (info(), intern_prefix $2, $4) }
   | VAL var
       { TAs (info(), intern_prefix $2, TVar(bogus(), "Any")) }
   | lab_filter AS var
       { TAs (info(), intern_prefix $3, $1) }
   | lab_filter
       { $1 }

lab_filter :
   | labset LSQUARE emp_filter RSQUARE
       { TLab(info(), $1, $3) }
   | AT atom_labset LSQUARE emp_filter RSQUARE
       { TAtt(info(), erase_prefix $2, $4) }
   | lab_filter STAR
       { TClos (info(), $1) }
   | lab_filter QUESTION
       { TUnion (info(), $1, TEmpty(info())) }
   | lab_filter PLUS
       { TClos1 (info(), $1) }
   | lab_filter LBRACKETBRACKET var ARROW pat RBRACKETBRACKET
       { TSubst (info(), $1, $3, $5) }
   | atom_filter
       { $1 }

atom_filter :
   | var 
       { handle_pvar $1 }
   | var arg_list
       { TApp(info(), $1, 
	      List.map
		(function
		  | (EVar (_, "_")) -> None 
		  | arg -> Some arg)
		$2) }
   | ATDOTDOT 
       { TAttRem(info()) }
   | DOTDOT 
       { handle_pvar "AnyElms" }
   | STRINGV
       { TSingle(info(), BVString $1) }
   | INTV
       { TSingle(info(), BVInt $1) }
   | FLOATV
       { TSingle(info(), BVFloat $1) }
   | LPAREN emp_filter RPAREN
       { $2 }

emp_filter :
   | /* empty */
       { TEmpty (info()) }
   | filter
       { $1 }

/* expressions */

expr :
   | MATCH expr WITH clauses 
       { EFilter(info(), $2, $4, ref (-1)) }
   | FILTER expr LBRACKET filter RBRACKET
       { EFilter(info(), $2, $4, ref (-1)) }
   | TRY expr WITH clauses
       { let x = new_name() in
         ETry(info(), $2, x, 
              EFilter(info_rhs 4 4, 
                      EVar(bogus(), x),                     
                      TUnionF(bogus(), 
			      TRule(bogus(), 
				    TVar(bogus(), "Any"), 
				    ERaise(bogus(), EVar(bogus(), x)), 
				    Syn.next_filter_id()), 
			      $4), 
		      ref (-1))) }
   | LET pat EQ expr IN expr %prec prec_let
       { EFilter(info(), $4, 
		 TRule(info_rhs 1 6, 
		       $2, $6, 
		       Syn.next_filter_id()),
		 ref (-1)) }
   | IF expr THEN expr ELSE expr %prec prec_if
       { EFilter(info(), $2,
		 TUnion(info_rhs 3 6,
			TRule(info_rhs 3 4,
			      Synutil.true_ty, $4, Syn.next_filter_id()),
			TRule(info_rhs 5 6,
			      Synutil.false_ty, $6, Syn.next_filter_id())),
		 ref (-1)) }		 
   | expr SEMICOLON expr
       { ESeq(info(), $1, $3) }
   | COERCE expr WITH atom_ty ELSE expr %prec prec_if
       { ECast(info(), $4, $2, true, ref (-1), Some $6 ) }
   | expr COMMA expr
       { ECat(info(), $1, $3) }
   | expr LT expr
       { EApp(info(), "lt", [$1; $3]) }
   | expr GT expr
       { EApp(info(), "gt", [$1; $3]) }
   | expr LTEQ expr
       { EApp(info(), "lteq", [$1; $3]) }
   | expr GTEQ expr
       { EApp(info(), "gteq", [$1; $3]) }
   | expr AND expr
       { EApp(info(), "band", [$1; $3]) }
   | expr OR expr
       { EApp(info(), "bor", [$1; $3]) }
   | expr EQ expr
       { EApp(info(), "eq", [$1; $3]) }
   | expr PLUS expr
       { EApp(info(), "iplus", [$1; $3]) }
   | expr MINUS expr
       { EApp(info(), "iminus", [$1; $3]) }
   | expr PLUSDOT expr
       { EApp(info(), "rplus", [$1; $3]) }
   | expr MINUSDOT expr
       { EApp(info(), "rminus", [$1; $3]) }
   | expr HAT expr
       { EApp(info(), "string_cat", [$1; $3]) }
   | expr STAR expr
       { EApp(info(), "imul", [$1; $3]) }
   | expr SLASH expr
       { EApp(info(), "idiv", [$1; $3]) }
   | expr MOD expr
       { EApp(info(), "imod", [$1; $3]) }
   | expr STARDOT expr
       { EApp(info(), "rmul", [$1; $3]) }
   | expr SLASHDOT expr
       { EApp(info(), "rdiv", [$1; $3]) }
   | VALIDATE expr WITH atom_ty
       { ECast(info(), $4, $2, true, ref (-1), None) }
   | label LSQUARE emp_expr RSQUARE
       { ELab (info(), "", Sym.label $1, $3) }
   | label COLON label LSQUARE emp_expr RSQUARE
       { ELab (info(), $1, Sym.label $3, $5) }
   | AT label LSQUARE emp_expr RSQUARE
       { EAtt (info(), "emptyprefix", Sym.label $2, $4) }
   | AT label COLON label LSQUARE emp_expr RSQUARE
       { EAtt (info(), $2, Sym.label $4, $6) }
   | RELABEL atom_expr LSQUARE emp_expr RSQUARE
       { EAnyLab (info(), EBase (info(), BVString ""), $2, $4) }
   | RELABEL atom_expr COLON atom_expr LSQUARE emp_expr RSQUARE
       { EAnyLab (info(), $2, $4, $6) }
   | COPY_LABEL atom_expr LSQUARE emp_expr RSQUARE
       { ECopyLab (info(), $2, $4) }
   | var arg_list 
       { EApp(info(), intern_bltin $1, $2) }
   | RAISE LPAREN emp_expr RPAREN
       { ERaise(info(), $3) }
   | atom_expr
       { $1 }

atom_expr :
   | var
       { EVar (info(), intern_prefix $1) }
   | STRINGV
       { EBase (info(), BVString $1) }
   | INTV
       { EBase (info(), BVInt $1) }
   | FLOATV
       { EBase (info(), BVFloat $1) }
   | LPAREN emp_expr RPAREN
       { $2 }

emp_expr :
   | /* empty */
       { EEmpty (info()) }
   | expr
       { $1 }

clauses :
   | pat ARROW expr %prec prec_match
       { TRule(info_rhs 1 3, $1, $3, Syn.next_filter_id()) }
   | pat ARROW expr BAR clauses
       { TUnionF(info_rhs 1 5, 
		 TRule(info_rhs 1 3, $1, $3, Syn.next_filter_id()),
		 $5) }

arg_list :
   | LPAREN emp_expr RPAREN
       { [$2] }
   | LPAREN emp_expr RPAREN arg_list
       { $2 :: $4 }
