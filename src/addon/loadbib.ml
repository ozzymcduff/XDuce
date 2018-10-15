open Bltin
open Format
open Syn
open Base

exception BibtexParsing of Finfo.finfo * string

let elem_of_atom a = match a with
  Bibtex.Id x -> MBase(BVString x)
| Bibtex.String x -> MBase(BVString (Latex_accents.normalize x))

let elem_of_entry etype key args =
  Synutil.label_va
    (Sym.label (String.lowercase etype))
    ~attr:(Synutil.label_va (Sym.label "key") [MBase(BVString key)])
    (Listutil.mapcat (fun (n,a) ->
      (Synutil.label_va
	 (Sym.label (String.lowercase n))
	 (List.map elem_of_atom a)))
       (List.sort (fun (n,_) (n',_) -> compare n n')
	  args))

let load_bib fname =
  let fname = Filing.search_file !Pref.searchpaths fname in
  let inch = open_in fname in
  let lexbuf = Lexing.from_channel inch in
  let biblio = 
    try
      Bibtex_parser.command_list Bibtex_lexer.token lexbuf
    with Parsing.Parse_error -> 
      raise(BibtexParsing (Finfo.make_finfo (Lexing.lexeme_start lexbuf)
		       (Lexing.lexeme_end lexbuf), "Parse error")) in
  close_in inch;
  let biblio = Bibtex.expand_abbrevs biblio in
  Bibtex.fold (fun com va -> 
    match com with
      Bibtex.Entry (etype, key, args) -> va @ (elem_of_entry etype key args)
    | _ -> va)
    biblio []
      
    
;;    
    
add_bltin "load_bib0" (function
    [[MBase(BVString fname)]] ->
      load_bib fname
  | _ -> raise Wrong_base_app);;

