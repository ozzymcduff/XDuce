import "xml.q"

namespace = "http://www.w3.org/1999/xhtml"
namespace xbel = "http://www.python.org/topics/xml/xbel"

(* Netscape bookmark types *)

type NS_bookmarks = html[@.., NS_head, NS_body]

type NS_head = head[@.., meta[@..], title[String*]]
      
type NS_body = body[@.., h1[String*], NS_folder_list]
                    
type NS_folder_list = dl[@.., NS_folder_contents]?

type NS_folder_contents = (NS_bookmark | NS_folder)*

type NS_bookmark = dt[@.., NS_link]

type NS_link = a[NS_a_attribs, String*]

type NS_a_attribs =
     @add_date[String*],
     @href[String*],
     @last_modified[String*],
     @last_visit[String*]

type NS_folder = dd[@.., NS_folder_title, NS_folder_list]

type NS_folder_title = h3[@.., String*]

(* XBEL types *)

import_dtd
      (prefix="XBEL_" namespace="http://www.python.org/topics/xml/xbel") 
      "xbel-1.0.dtd"

type nodes = (XBEL_bookmark | XBEL_folder | XBEL_alias | XBEL_separator)*

(* NS->XBEL *)

fun ns_to_xbel (NS_bookmarks as h): XBEL_xbel =
  filter h {
    html[@.., NS_head, 
      body[@.., h1[Any as t], 
           (() as l | dl[@.., AnyElms as l])]] 
      { 
	xbel:xbel[xbel:title[t], ns_to_xbel_contents (l)] 
      }
  } 

fun proc_dd (NS_folder as f) : XBEL_folder =
  filter f {
    dd[@.., h3[@.., AnyElms as t], 
       (() as l | dl[@.., AnyElms as l])] 
      { xbel:folder[xbel:title[t], ns_to_xbel_contents (l)] }
  } 

fun proc_dt (NS_bookmark as b) : XBEL_bookmark =
  filter b {
  dt[@.., 
     a[@add_date[Any as add],
       @href[Any as url],
       @last_modified[Any as modi],
       @last_visit[Any as vis],
       AnyElms as t]] 
   { xbel:bookmark[@added[add], 
		   @href[url], 
		   @modified[modi], 
		   @visited[vis],
		   xbel:title[t]] }
  } 

fun ns_to_xbel_contents (NS_folder_contents as l) : nodes =
  filter l {
   (proc_dd(_) | proc_dt(_))*
  } 

(* Entry point *)

let Any as in_doc = load_xml("ns.xml")
let Any as valid_doc = validate in_doc with NS_bookmarks
let Any as out_doc = ns_to_xbel(valid_doc)
let Any = save_xml("xbel.xml")(out_doc)

(*

filter proc_dd =
 dd[@.., h3[@.., AnyElms as t], 
    dl[@.., (proc_dd | proc_dt)+ as l]
    { xbel:folder[xbel:title[t], l] }
 ]

filter proc_dt =
  dt[@.., 
     a[@add_date[Any as add],
       @href[Any as url],
       @last_modified[Any as modi],
       @last_visit[Any as vis],
       AnyElms as t]] 
   { xbel:bookmark[@added[add], 
		   @href[url], 
		   @modified[modi], 
		   @visited[vis],
		   xbel:title[t]] }

*)
