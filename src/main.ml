open List
open Sym
open Syn

let usage_msg = 
  Format.sprintf "Usage: %s filename [arg ...]" Sys.argv.(0)

let process_args() =
  let args = ref [] in
  Arg.parse
    [ 
      "-version", Arg.Unit (fun () -> Format.printf "XDuce version %s@." Pref.version; exit 0), "show version";
      "-path", Arg.String (fun s -> Pref.searchpaths := s::!Pref.searchpaths), "add a string to the search paths";
      "-timer", Arg.Unit (fun () -> Pref.timer := true), "print timer and counter outputs";
      "-verbose_error", Arg.Unit (fun () -> Pref.verbose_error := true), "print verbose error nmessages";
      "-trace", Arg.Unit (fun () -> Pref.trace := true), "trace function call/return";
      "-tracemore", Arg.Unit (fun () -> Pref.tracemore := true), "trace function call/return with arguments/return values";
      "-show_ns_table", Arg.Unit (fun () -> Pref.show_ns_table := true), "show the name space table in the end";
      "-patopt", Arg.Unit (fun () -> Pref.patopt := true), "enable pattern optimization";
      "-rejectambig", Arg.Unit (fun () -> Pref.reject_ambiguous := true), "reject ambiguous patterns";
      "-noredun", Arg.Unit (fun () -> Pref.check_redundant := false), "disable pattern redundancy check";
      "-noeval", Arg.Unit (fun () -> Pref.noeval := true), "no evaluation";
      "-nopervasive", Arg.Unit (fun () -> Pref.nopervasive := true), "don't load pervasive.q";
      "-showphase", Arg.Unit (fun() -> Pref.showphase := true), "show phases";
      "-typinglog", Arg.Unit (fun() -> Pref.typinglog := true), "show typing log";
      "-showam", Arg.Unit (fun() -> Pref.showam := true), "show automata in typing error messages";
      "-showtypedef", Arg.Unit (fun() -> Pref.showtypedef := true), "show type definitions";
      "-tracepat", Arg.Unit (fun() -> Pref.tracepat := true), "trace pattern matching evaluation";
      (*"-peekpat", Arg.String (fun s -> Pref.peek_pat := s::!Pref.peek_pat), "peek internal structure of pattern";*)
      "-profpat", Arg.Unit (fun () -> Pref.prof_pat := true), "profile pattern matching";
      "-experim", Arg.Int (fun i -> Pref.experim := i), "(undocumented)";
      "--", Arg.Rest (fun arg -> args := !args @ [arg]), "pass the rest arguments to XDuce program";
    ] 
    (fun arg -> args := !args @ [arg])
    usage_msg;
  match !args with
    [] -> failwith "Input file not specified"
  | fname :: args -> 
      Pref.args := args;
      fname

exception Parsing of Finfo.finfo * string

let (_read_files_ : (string*string, unit) Hashtbl.t) = Hashtbl.create 97

let rec parseFile prefix fname =
  if not (!Pref.nopervasive) && fname <> "pervasive.q" then
    parseFile prefix "pervasive.q";
  let original_fname = !Finfo.input_file_name in
  let fname = Filing.search_file !Pref.searchpaths fname in
  try Hashtbl.find _read_files_ (prefix, fname);    
  with Not_found ->
    Hashtbl.add _read_files_ (prefix, fname) ();
    Finfo.input_file_name := fname;
    let inch = open_in fname in
    try
      let lexbuf = Lexing.from_channel inch in
      try
        let res = Parser.parse Lexer.token lexbuf parseFile in
        close_in inch;
        res
      with Parsing.Parse_error -> 
        raise(Parsing (Finfo.make_finfo (Lexing.lexeme_start lexbuf)
                         (Lexing.lexeme_end lexbuf), "Parse error"))
    with e ->
      close_in inch; 
      Finfo.input_file_name := original_fname;
      raise e

let main() =
  Format.set_max_boxes 10000;
  Format.pp_set_max_boxes Format.err_formatter 10000;
  let input_file  = process_args() in
  parseFile "" input_file;
  let _ = Top.process_top Top.top in
  ()

(* errors *)

open Format

exception Unmatch of Finfo.finfo * string * va

let rec print_exn = function
    Lexer.Lexing(finfo, mes) ->
      Finfo.print finfo;
      eprintf "@[%s@]@."  mes
  | Parsing(finfo, mes) ->
      Finfo.print finfo;
      eprintf "@[%s@]@." mes
  | Ctx.Unbound(finfo, kind, name) ->
      Finfo.print finfo;
      eprintf "@[Unbound %s: %s@]@." kind name
  | Ctx.Multidef(finfo, kind, name) ->
      Finfo.print finfo;
      eprintf "@[Multiply defined %s: %s@]@." kind name
  | Check.Subtyping(finfo, ty1, ty2, w) ->
      Finfo.print finfo;
      if !Pref.verbose_error then begin
	eprintf "@[This expression's type@;<1 2>@[%a@]@ is not a subtype of the expected type:@;<1 2>@[%a@]@ @]@." 
	Htype.print ty1 Htype.print ty2;
      end else begin
	eprintf "@[This expression's type is not a subtype of the expected type.@."
      end;
      eprintf "@[<2>The following tag is not expected:@ @[%a@]@]@."
	Typath.print w
  | Eval.CastFailed(finfo, ty, w) ->
      Finfo.print finfo;
      eprintf "@[Conformance test failed against type@;<1 2>@[%a@]@."
	Synutil.print_ty ty;
      eprintf "@[<2>The following tag is not matched:@ @[%a@]@]@."
	Typath.print w
  | Check.Non_exhaustive(finfo, ty1, pats, w) ->
      Finfo.print finfo;
      eprintf "This pattern is not exhaustive.@.";
      eprintf "@[<2>The following tag is not captured:@ @[%a@]@]@."
	Typath.print w
  | Check.Redundant_pattern(finfo) ->
      Finfo.print finfo;
      eprintf "This pattern matches no values.@."
  | Check.Ambiguous_pattern(finfo) ->
      Finfo.print finfo;
      eprintf "This pattern is ambiguous.@."
  | Desugtype.Ill_formed_pattern(finfo, s) ->
      Finfo.print finfo;
      eprintf "@[Ill-formed pattern: %s@]@." s
  | Desugtype.Ill_formed_type(finfo, s) ->
      Finfo.print finfo;
      eprintf "@[Ill-formed type: %s@]@." s
  | Eval.Evaluation(finfo, expr, mes) ->
      Finfo.print finfo;
      eprintf "%s@." mes
  | Eval.EvaluationFunc(finfo, mes) ->
      Finfo.print finfo;
      eprintf "%s@." mes
  | Unmatch(finfo, fun_name, va) ->
      Finfo.print finfo;
      eprintf "@[This application fails with unmatching.@]@." 
  | Eval.UserExc(v) ->
      eprintf "User exception: @[%a@]@." Synutil.print_va v;
  | Parsedtd.DTD_error(s) ->
      eprintf "Misc exception: @[%s@]@." s;
  | Loadbib.BibtexParsing(finfo, mes) ->
      Finfo.print finfo;
      eprintf "%s@." mes
  | Bltin.Bltin_not_found name ->
      eprintf "Built-in function %s not implemented@." name
  | Check.Wrong_num_arguments(finfo, actual, formal) ->
      Finfo.print finfo;
      if actual > formal then 
	eprintf "This function application supplies too many arguments@."
      else
	eprintf "This function application supplies too few arguments@."
  | Eval.Bltin_error (finfo, f, mes) ->
      Finfo.print finfo;
      eprintf "Built-in function %s raised error: %s@." f mes
  | e -> raise e
	
let dump_stat () =
  if !Pref.showtypedef then printf "%a@." Htype.print_binding ();
  if !Pref.timer then Timer.dump();
  if !Pref.timer then Counter.dump();
  if !Pref.show_ns_table then Ns.print_table()
    

let exec func arg =
  try
    func arg
  with
    e -> 
      print_exn e;
      dump_stat();
      exit 1

let _ = exec main ()

let _ = dump_stat ()

