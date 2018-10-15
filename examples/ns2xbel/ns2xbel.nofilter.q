import "xml.q"

namespace = "http://www.w3.org/1999/xhtml"
namespace xbel = "http://www.python.org/topics/xml/xbel"

(* Netscape bookmark types *)

type NS_bookmarks = html[AnyAttrs, NS_head, NS_body]

type NS_head = head[AnyAttrs, meta[AnyAttrs], title[String*]]
      
type NS_body = body[AnyAttrs, h1[String*], NS_folder_list]
                    
type NS_folder_list = dl[AnyAttrs, NS_folder_contents]?

type NS_folder_contents = (NS_bookmark | NS_folder)*

type NS_bookmark = dt[AnyAttrs, NS_link]

type NS_link = a[NS_a_attribs, String*]

type NS_a_attribs =
     @add_date[String*],
     @href[String*],
     @last_modified[String*],
     @last_visit[String*]

type NS_folder = dd[AnyAttrs, NS_folder_title, NS_folder_list]

type NS_folder_title = h3[AnyAttrs, String*]

(* XBEL types *)

import_dtd (prefix="XBEL_" namespace="http://www.python.org/topics/xml/xbel") 
      "xbel-1.0.dtd"
type nodes = (XBEL_bookmark | XBEL_folder | XBEL_alias | XBEL_separator)*

(* NS->XBEL *)

fun ns_to_xbel (val h as NS_bookmarks): XBEL_xbel =
  match h with
    html[AnyAttrs, NS_head, body[AnyAttrs, h1[val t], val l as AnyElms]] ->
      xbel:xbel[
        xbel:title[t], ns_to_xbel_contents (folder_contents (l))]

fun folder_contents (val l as NS_folder_list) : NS_folder_contents =
  match l with
    () -> ()
  | dl[AnyAttrs, val c as AnyElms] -> c

fun ns_to_xbel_contents (val l as NS_folder_contents) : nodes =
  match l with
    () -> ()
  | dd[AnyAttrs, h3[AnyAttrs, val t as AnyElms], val l as AnyElms], val rest ->
      xbel:folder[xbel:title[t], ns_to_xbel_contents (folder_contents (l))],
      ns_to_xbel_contents (rest)
  | dt[AnyAttrs, 
       a[@add_date[val add],
	 @href[val url],
	 @last_modified[val modi],
	 @last_visit[val vis],
         val t as AnyElms]], 
    val rest ->
      xbel:bookmark[
               @added[add], 
	       @href[url], 
               @modified[modi], 
	       @visited[vis],
               xbel:title[t]],
      ns_to_xbel_contents (rest)

(* Entry point *)

let val in_doc = load_xml("ns.xml")
let val valid_doc = validate in_doc with NS_bookmarks
let val out_doc = ns_to_xbel(valid_doc)
let Any = save_xml("xbel.xml")(out_doc)
