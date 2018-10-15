#! ../../xduce.opt
(*
Missing features / problems:
- Namespaces
- Comments / stars: (x as (a|b)* )
- Coerce error message
- argv does not contain the program name
*)


import "xml.q"
import_dtd "xhtml1-transitional.dtd"

(*-------------------- Bookmark Types ------------------*)

type NS_bookmarks = 
    html [NS_head,
          NS_body]

type NS_head =
    head [meta [],
          title [String*]]
      
type NS_body =
    body [h1 [String*],
          NS_folder_contents]
                    
type NS_folder_contents =
    dl [(NS_bookmark | NS_folder)*]?

type NS_bookmark =
    dt [NS_address]

type NS_folder =
    dd [NS_folder_title,
        NS_folder_contents]

type NS_folder_title = h3 [String*]

type NS_a_attribs =
     add_date [String],
     href [String],
     last_modified [String],
     last_visit [String]

type NS_address = 
    a@NS_a_attribs
       [String*]

(**************************************************)

import_dtd "xbel-1.0.dtd"
type nodes = (bookmark | folder | alias | separator)*

(***********************)

fun real_contents (val c as NS_folder_contents) : NS_folder_cts =
  match c with
    ()         -> ()
  | dl[val c'] -> c'

type terse = verbose[] | terse[]

fun to_xbel (val h as NS_bookmarks)(val terse as terse): xbel =
  match h with
    html [NS_head, body [h1 [val title], val contents]] ->
      xbel[xtitle[title], folder_contents (real_contents (contents))(terse)]

type NS_folder_cts = (NS_bookmark | NS_folder)*

fun folder_contents (val l as NS_folder_cts)(val terse as terse) : nodes =
  match l with
    () -> ()
  | dd [h3[val title], val contents], val rem ->
      folder[xtitle[title], folder_contents (real_contents (contents))(terse)],
      folder_contents (rem)(terse)
  | dt [a@(val attrs)[val title]], val rem ->
      (match terse with
         terse[] ->
           let Any,href[val url],Any = attrs in
           bookmark@(href[url])[xtitle[title]]
       | verbose[] ->
           let Any,href[val url],Any = attrs in
           let Any,add_date[val added],Any = attrs in
           let Any,last_visit[val visited],Any = attrs in
           let Any,last_modified[val modified],Any = attrs in
           bookmark@(added[added],href[url],
                     modified[modified],visited[visited])
                   [xtitle[title]]),
      folder_contents (rem)(terse)

(*************)

fun test_url (val url as String) : Bool =
  print_string_oneline ("Testing " ^ url ^ "...");
  let val res = system("./test.pl", url) = 0 in
  print_string_oneline ("done.\n");
  res

fun test_urls (val bm as xbel) : xbel =
  match bm with
(*    xbel[val head as (xtitle?, info?, desc?), val cts] -> *)
      xbel[val head as (xtitle?, info?, desc?), 
	   val cts as ^(xtitle|info|desc)[Any]* ] -> 
      xbel[head, cts_test_urls (cts)]

fun cts_test_urls (val c as nodes) : nodes =
  match c with
    ()  -> ()
  | bookmark@(val attrs as (Any, href[val url], Any))
            [val head as (xtitle?, info?), val d as desc?],
    val rem ->
      let val new_desc =
        if test_url (url) then d else
        match d with
          ()           -> desc["Broken"]
        | desc [val d] -> desc["Broken -", d]
      in
      bookmark@attrs[head, new_desc], cts_test_urls (rem)
  | folder[val head as (xtitle?, info?, desc?), val cts as nodes], val rem ->
      folder[head, cts_test_urls (cts)], cts_test_urls (rem)
  | val other as (alias | separator), val rem ->
      other, cts_test_urls (rem)

(*************)

let val file = load_xml("bookmarks.html")
let val bmfile = coerce (file) with NS_bookmarks else raise("help")

let val output = "bookmarks.xbel"
let Any = save_xml(output)(test_urls(to_xbel(bmfile)(terse[])))
let Any = system ("tidy -i -xml -m", output)
