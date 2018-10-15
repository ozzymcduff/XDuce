(*
   4.1 Annotations 
   4.2 Whitespace [ignored]
   4.3 datatypeLibrary [ignored]
   4.4 type/value [ignored]
   4.5 href [ignored]
   4.6 externalRef [include-stage]
   4.7 include [include-stage]
   4.8 name attribute [dump-stage]
   4.9 ns
   4.10 QNames
   4.11 div [hoisting-stage]
   4.12 number of child elements [dump-stage]
   4.13 mixed [dump-stage]
   4.14 optional [dump-stage]
   4.15 zeroOrMore [dump-stage]
   4.16 Constraints [irrelevant]
   4.17 combine [hoisting-stage]
   4.18 grammar [hoisting-stage]
   4.19 define/ref [dump-stage]
   4.20 notAllowed [dump-stage]
   4.21 empty [dump-stage]
*)

(* to do:
   + @ns stuff 
   + foreign elements (comment etc.) --- need a namespace & interleave support
   + list
   + name mangling
   + renaming stage to treat ref/parentRef
*)

import "xml.q"

namespace = "http://relaxng.org/ns/structure/1.0"

type pattern =
    element[@name[String], pattern+]
  | element[nameClass, pattern+]
  | attribute[@name[String], pattern?]
  | attribute[nameClass, pattern?]
  | group[pattern+]
  | interleave[pattern+]
  | choice[pattern+]
  | optional[pattern+]
  | zeroOrMore[pattern+]
  | oneOrMore[pattern+]
  | list[pattern+]
  | mixed[pattern+]
  | ref[@name[String]]
  | parentRef[@name[String]]
  | empty[]
  | text[]
  | value[@'type'[String]?, String]
  | data[@'type'[String], param*, exceptPattern?]
  | notAllowed[]
  | externalRef[@href[String]]
  | grammar[@.., grammarContent*]

type param =
    param[@name[String], String]
  | except[pattern+]

type exceptPattern =
    except[pattern+]

type grammarContent =
    start
  | define
  | div[grammarContent*]
  | include[@href[String], includeContent*]

type includeContent =
    start
  | define
  | div[includeContent*]

type start =
    start[@combine[method]?, pattern]

type define =
    define[@name[String], @combine[method]?, pattern+]

type method =
    "choice" | "interleave"

type nameClass =
    name[String]
  | anyName[exceptNameClass?]
  | nsName[@.., exceptNameClass?]
  | choice[nameClass+]

type exceptNameClass =
    except[nameClass+]

(* Utility *)

fun strcat (String* as arg) : String =
  filter arg {
    String as x, Any as rest { x ^ strcat(rest) }
  | () { "" }
  }

fun remove_dup (String* as ns) : String* =
  filter ns {
    String as n1, String* as ns 
    { n1, 
      remove_dup(filter ns { (String as n2 { if n1 = n2 then () else n2 })* }) }
  | ()
    { () }
  }  

(* Inclusion *)

fun override_defines ((start|define)* as ics)(grammarContent* as gcs) : grammarContent* =
  filter ics {
    define[@name[String as s1], @.., AnyElms], AnyElms as rest
    { let Any as gcs =
        filter gcs {
        ( define[@name[String as s2], @.., AnyElms] as d
	    (* INF *)
	  { if s1 = s2 then () else d }
        | ^define[Any] as e
	  { e })*
        } in
      override_defines(rest)(gcs) }
  | ^define[Any], AnyElms as rest
    { override_defines(rest)(gcs) }
  | ()
    { gcs }
  } 

fun override_starts ((start|define)* as ics)(grammarContent* as gcs) : grammarContent* =
  filter ics {
    AnyElms, start[Any], AnyElms  
    { filter gcs {
      ( start
      | ^start[Any] as gc  { gc })* } }
  | ^start[Any]*
    { gcs }
  } 

fun override ((start|define)* as ics)(grammarContent* as gcs) : grammarContent* =
  let Any as gcs = override_starts (ics)(gcs) in
  override_defines(ics)(gcs)
    
fun include_files_includeContents (includeContent* as ics) : (start|define)* =
  filter ics {
    ( start[(@.. as a), AnyElms as p] 
      { start[a, include_files(p)] }
    | define[(@.. as a), AnyElms as ps]
      { define[a, filter ps { include_files(_)+ } ] }
    | div[AnyElms as ics]
      { include_files_includeContents(ics) })*
  }   

fun include_file (String as s)(includeContent* as ics) : grammarContent* =
  let Any as file = load_xml(s) in
  let grammar[(@.. as a), grammarContent* as gcs] = validate file with grammar in
  let Any as ics = include_files_includeContents(ics) in
  div[(* a,*) override(ics)(gcs)], ics
  
fun include_files_grammarContents (grammarContent* as gcs) : grammarContent* =
  filter gcs {
    ( start[(@.. as a), AnyElms as p] 
      { start[a, include_files(p)] }
    | define[(@.. as a), AnyElms as ps]
      { define[a, filter ps { include_files(_)+ }] }
    | div[AnyElms as gcs]
      { include_files_grammarContents(gcs) }
    | include[@href[String as s], (@.. as a), AnyElms as ics]
      { div[a, include_file(s)(ics)] })*
  }   

fun include_extern (String as s)(@ns[String]? as ns) : pattern =
  let Any as file = load_xml(s) in
  let Any as p =
    filter file {
        ~[@ns[Any], @.., AnyElms] as p { p }
      | ~[(@^ns[Any]* as a), AnyElms as es] as p { copy_label p [ns, a, es] }
(*      |	(() | AnyElm,AnyElm+) { error("shouldn't happen") }  *)
	  (* Redundancy check found this clause's unnecessity! *)
    } in
  validate p with pattern 
  
fun include_files (pattern as p) : pattern =
  filter p {
    element[(@name[Any] | nameClass) as n, AnyElms as ps]
    { element[n, filter ps { include_files(_)* } ] }
  | attribute[(@name[Any] | nameClass) as n, AnyElms as ps] 
    { attribute[n, filter ps { include_files(_)? } ] }
  | ~(group|interleave|choice|optional|zeroOrMore|oneOrMore|list|mixed)[Any as ps] as p2
    { copy_label p2 [filter ps { include_files(_)+ } ] }
  | data[@'type'[Any as s], param* as params]
    { data[@'type'[s], params] }
  | data[@'type'[Any as s], param* as params, except[Any as ps]]
    { data[@'type'[s], params, except[filter ps { include_files(_)* }]] }
  | grammar[(@.. as a), AnyElms as gcs] 
    { grammar[a, include_files_grammarContents(gcs)] } 
      (* extracting the whole attributes and put them back. *)
  | ~(ref|parentRef|empty|text|value|notAllowed|externalRef)[Any] as p
    { p }
  | externalRef[@href[Any as s], (@ns[Any]? as ns)] 
    { include_extern(s)(ns) }
  } 

(* Renaming *)
(* Hoisting nested grammars *)

fun combine_starts (grammarContent* as gcs) : pattern =
  let Any as starts = 
    filter gcs { (start[@.., AnyElm] as s { s } | ^start[Any] { () })* } in
  let Any as ps = 
    filter starts { (start[@.., AnyElm as p] { p })* } in
  filter ps {
    AnyElm+ as ps
    { 
      filter starts { 
        start[AnyElms]*, start[@combine[Any as c], AnyElms], Any
        { filter c { "choice" { choice[ps] } 
                 | "interleave" { interleave[ps] } } }
      | start[AnyElm as p] 
        { p }
      | start[AnyElms]*
        { error("shouldn't happen") }
      }
    }   
  | ()  { error("shouldn't happen") }
  } 

fun combine_defines (define* as ds) : define* =
  let Any as ns =
    filter ds {
      (define[@name[String as n], @.., AnyElms] { n })*
    } in
  let Any as ns = remove_dup(ns) in
  filter ns {
    (String as n1 {
      let Any as ds = 
	filter ds { 
	  (define[@name[String as n2], @.., AnyElms] as d
	   { if n1 = n2 then d else () })*
	} in
      let Any as ps =
	filter ds {
	  (define[@.., AnyElms as ps] { group[ps] })*
	} in 
      filter ps {
        AnyElm+ as ps  {  
          filter ds { 
            define[@.., AnyElms]*, define[@name[String as n], @combine[Any as c], AnyElms], Any
            {           
	      define[@name[n],
		     filter c { "choice" { choice[ps] } 
                            | "interleave" { interleave[ps] } }] 
	    }
          | define[@name[Any], AnyElms as ps]
            { define[@name[n1], group[ps]] } 
          | define[@name[Any], AnyElms]*
            { error("shouldn't happen") }
          } 
	}
      | ()  { error("shouldn't happen") }
      }  
    })*
  }  
	
fun remove_grammars (pattern as p) : pattern =
  filter p {
    element[(@name[Any] | nameClass) as n, AnyElms as ps]
      (* effectively use att-elm mixture *)
    { element[n, filter ps { remove_grammars(_)* }] }
      (* the inner filter is ugly.  better to be able to use functions as rules *)
  | attribute[(@name[Any] | nameClass) as n, AnyElms as ps] 
    { attribute[n, filter ps { remove_grammars(_)? }] }
      (* this code is almost the same as element.  but cannot be merged because
	 the type of ps is differenct. *)
  | ~(group|interleave|choice|optional|zeroOrMore|oneOrMore|list|mixed)[Any as ps] as p2
      (* use a union label set *) 
    { copy_label p2 [filter ps { remove_grammars(_)* }] }
  | data[@'type'[Any as s], param* as params]
    { data[@'type'[s], params] }
  | data[@'type'[Any as s], param* as params, except[Any as ps]]
    { data[@'type'[s], params, except[filter ps { remove_grammars(_)* }]] }
  | grammar[@.., AnyElms as gcs]
    { combine_starts(gcs) }
  | ~(ref|parentRef|empty|text|value|notAllowed|externalRef)[Any] as p
    (* Pattern inference could be helpful since the content is different 
       for each label.  Though in this specific case, p can be just
	"pattern".
       If we were to cut off some labels where the result type must be a 
       cut off one, then the inference would be useful. *)
    { p }
  } 

type grammar = grammar[@.., grammarContent*]

fun extract_grammars (pattern as p) : grammar* =
  filter p {
    ~(element|attribute)[(@name[Any] | nameClass) as n, AnyElms as ps]
    { filter ps { extract_grammars(_)* } }
  | ~(group|interleave|choice|optional|zeroOrMore|oneOrMore|list|mixed)[Any as ps] 
    { filter ps { extract_grammars(_)* } }
  | data[@'type'[Any as s], param*, (except[Any as ps] | () as ps)]
    { filter ps { extract_grammars(_)* } }
  | grammar[Any] as p  
    { p }
  | ~(ref|parentRef|empty|text|value|notAllowed|externalRef)[Any] 
    { () }
  } 
  
fun hoist_grammarContent (grammarContent* as gcs) : define* =
  filter gcs {
  ( start 
    { () }
  | define[(@name[String], @combine[method]?) as h, AnyElms as ps]
    { define[h, filter ps { remove_grammars(_)* }],
      filter ps { hoist(_)* } }
  | div[grammarContent* as gcs]
    { hoist_grammarContent(gcs) }
  | include[Any] 
    { error("shouldn't happen") } )*
  }
   
fun hoist (pattern as p) : define* =
  let Any as gs = extract_grammars(p) in  
  filter gs {
    (grammar[@.., AnyElms as gcs]
      { combine_defines(hoist_grammarContent(gcs)) })*
  } 


(* Patterns -> String *)

fun proc_group (pattern+ as ps) : String* =
  filter ps {
    (AnyElm as p  {  proc_pattern(p)  }),
    (AnyElm as p  {  ", ", proc_pattern(p) })*
  }

fun proc_interleave (pattern+ as ps) : String* =
  filter ps {
    (AnyElm as p  {  proc_pattern(p)  }),
    (AnyElm as p  {  " & ", proc_pattern(p) })*
  }

fun proc_choice (pattern+ as ps) : String* =
  filter ps {
    (AnyElm as p  {  proc_pattern(p)  }),
    (AnyElm as p  {  " | ", proc_pattern(p) })*
  }

fun proc_pattern (pattern as p) : String* =
  filter p {
    element[@name[Any as s], AnyElms as ps]
    { s, "[", proc_group(ps), "]" }
  | element[nameClass as nc, AnyElms as ps]
    { "elm ", proc_nameClass(nc) , "[", proc_group(ps), "]" }
  | attribute[@name[Any as s], AnyElms as p]
    { "@", s, "[", filter p { proc_pattern(_)? }, "]" }
  | attribute[nameClass as nc, AnyElms as p]
    { "@", proc_nameClass(nc) , "[", filter p { proc_pattern(_)? }, "]" }
  | group[Any as ps]
    { "(", proc_group(ps), ")" }
  | interleave[Any as ps]
    { "(", proc_interleave(ps), ")" }
  | choice[Any as ps]
    { "(", proc_choice(ps), ")" }
  | optional[Any as ps]
    { "(", proc_choice(ps), ")?" }
  | zeroOrMore[Any as ps]
    { "(", proc_group(ps), ")*" }
  | oneOrMore[Any as ps]
    { "(", proc_group(ps), ")+" }
  | list[Any as ps]
    { "list(", proc_group(ps), ")" }
  | mixed[Any as ps]
    { "(", proc_group(ps), ") & String*" }
  | ref[@name[Any as s]]
    { s }
  | parentRef[@name[Any as s]]
    { "parentRef(", s, ")" }
  | empty[]
    { "()" }
  | text[]
    { "String*" }
  | value[@'type'[String]?, AnyElms as s]
    { "\"", s, "\"" }
  | data[@'type'[Any as s], param*]
    { s }
  | data[@'type'[Any as s], param*, except[Any as ps]]
    { "(", s, " \\ (", proc_choice(p), ")" }
  | notAllowed[]
    { "None" }
  | externalRef[@href[Any as s]]
    { "externalRef(", s, ")" }
  | grammar[Any]
    { error("shouldn't happen") }
  } 

fun proc_choiceNameClass (nameClass+ as ncs) : String* =
  filter ncs {
    (nameClass as nc  { proc_nameClass(nc) }), 
    (nameClass as nc  { " | ", proc_nameClass(nc) })*
  } 
    
fun proc_nameClass(nameClass as nc) : String* =
  filter nc {
    name[Any as n]
    { n }
  | anyName[]
    { "~" }
  | anyName[except[Any as ncs]]
    { "~\\(", proc_choiceNameClass(ncs), ")" }
  | nsName[@..]
    { "ns" }
  | nsName[@.., except[Any as ncs]]
    { "ns\\(", proc_choiceNameClass(ncs), ")" }
  | choice[Any as ncs]
    { "(", proc_choiceNameClass(ncs), ")" }
  } 

fun proc_define (define[@name[String as n], @.., pattern+ as ps]) : String* =
  "type ", n, " = ",
  proc_group(ps),
  "\n"

(* Entry point *)

fun main () : () =
  filter argv() {
    String as infile, String as outfile
    { display("incorporating...\n");
      let Any as file = load_xml(infile) in
      let Any as pat = validate file with pattern in
      let Any as pat = include_files(pat) in
      display("processing...\n");
      let Any as toppat = remove_grammars(pat) in
      let Any as defines = hoist(pat) in
      let Any as out = 
	"type start = ",
	proc_pattern(toppat), 
	"\n",
	filter defines { (define as d  { proc_define(d) })* }
        in
      fileout_string(outfile)(strcat(out)) }
  || Any 
    { print("Usage: <xduce-program> rng2xduce.q -- <input-file> <output-file>") }
  } 

let Any = main()
