(*-------------------- Publishing Netscape Personal Bookmark ------------------*)

(* The aim of this application is, given a NS bookmark file, to
   extract a folder named "Public", construct a table of contents for
   the top two levels, and make links from the TOC to the bullets in
   the folder (i.e., insert an anchors in each bullet). *)

import "xml.q"
import_dtd
  (prefix = "Html_" namespace = "http://www.w3.org/1999/xhtml") 
  "xhtml1-transitional.dtd"

namespace = "http://www.w3.org/1999/xhtml"

(*-------------------- Bookmark Types ------------------*)

type NS_bookmarks = 
    html [@..,
	  NS_head,
	  NS_body]

type NS_head =
    head [@..,
	  meta [@..],
	  title [@..,
		 String*]]
      
type NS_body =
    body [@..,
	  h1 [@..,
	      String*],
	  NS_folder]
		    
type NS_folder =
    NS_dl*

type NS_dl = 
    dl [@..,
	(NS_dt | NS_dd)*]

type NS_dt =
    dt [@..,
	NS_a]
	    
type NS_dd =
    dd [@..,
	NS_h3,
	NS_folder]

type NS_h3 = h3 [@..,
		 String*]

type NS_a_attribs =
    @href [String*]?,
    @add_date [String*]?,
    @last_visit [String*]?,
    @last_modified [String*]?

type NS_a = 
    a[NS_a_attribs,
      String*]

fun main () : () =
  filter argv() {
    val infile as String, val outfile as String {
      let val file = load_xml(infile) in
      let val bmfile = validate file with NS_bookmarks in
      let val title = getTitle(bmfile) in
      let val folder = getFolder(bmfile) in
      let val publics = findPublic(folder) in
      let val public = firstPublic(publics) in
      let val toc = ul [tocTop(public)] in
      let val public2 = putAnchors(public) in
      let val out = 
	html 
	  [head[title[title]],
	   body
	     [h1[title],
	      h2["Table of Contents"],
	      toc,
	      hr[],
	      public2]] in
      save_xml(outfile)(out)
    }
  || Any 
    {
      print("Usage: <xduce-program> bookmarks.q -- <input-file> <output-file>")
    }
  }

(*-------------------- String Concat ------------------*)

fun strcat (val l as String* ) : String =
  filter l {
    () 
       { "" }
  | val x as String, val y 
       { x ^ strcat(y) }
  } 

(*-------------------- Get title and folder ------------------*)

type AnyEls = (~[Any] | String)*

fun getTitle (val b as NS_bookmarks) : String =
  filter b {
    html [@..,
	  head [Any],
	  body [@..,
		h1 [@..,
		    val title as String*],
		AnyEls]]
    { strcat(title) }
  } 

fun getFolder (val b as NS_bookmarks) : NS_folder =
  filter b {
    html [@..,
	  AnyEls,
	  body [@..,
		h1 [Any],
		val folder as AnyEls],
	  AnyEls]
    { folder }
  } 

(*-------------------- Find Public Folder ------------------*)

fun findPublic (val f as NS_folder) :  res[NS_folder]* =
  filter f {
   (dl [@.., val dt as AnyEls] 
     { filter dt {
        (dd [@.., h3 [@.., "Public"], val folder as AnyEls]
         { res[folder] }
       | dd [@.., NS_h3, val folder as AnyEls]
         { findPublic(folder) }
       | NS_dt 
         { () })*
      } 
    })*
  } 

fun firstPublic (val rs as res[NS_folder]* ) : NS_folder =
  filter rs {
    res [@.., val folder as AnyEls], Any
      { folder }
  | ()
      { error ("Can't find a \"" ^ "Public" ^ "\" folder") }
  } 

(*-------------------- Table of Contents ------------------*)

fun tocTop (val f as NS_folder) : Html_li* =
  filter f {
    (dl [@.., val dt as AnyEls]
       { tocFirst(dt) })*
  } 

fun tocFirst (val ds as (NS_dt|NS_dd)* ) : Html_li* =
  filter ds {
  ( dd [@.., h3 [@.., val names as AnyEls], val folder as AnyEls]
    {  let val name = strcat(names) in
       li [a[@href ["#" ^ name],
	     b[name]], ": ",
           tocSecondTop(folder)]  }
  | NS_dt
    { () }
  )*
  } 

fun tocSecondTop (val f as NS_folder) : (Html_a | String)* =
  filter f {
  ( dl [@.., val dt as AnyEls]
      { tocSecond(dt) }
  )*
  } 

fun tocSecond (val ds as (NS_dt|NS_dd)* ) : (Html_a | String)* =
  filter ds {
  ( dd [@.., h3 [@.., val name as AnyEls], val folder as AnyEls]
    {  let val name = strcat(name) in
       a[@href ["#" ^ name],
	 name], "/"  }
  | NS_dt
    { () }
  )*
  } 

(*-------------------- Anchors ------------------*)

fun putAnchors (val f as NS_folder) : (Html_dl | String)* =
  filter f {
   (dl[@.., val dt as AnyEls]  { dl [putAnchorsDt(dt)] })*
  }

fun putAnchorsDt2 (val f as (NS_dt)* ) : (Html_dt)+ =
  filter f {
    ((NS_dt)
       { 
         dt[]
       })+
    | () 
       { dt[] }
  }


fun putAnchorsDt (val f as (NS_dt|NS_dd)* ) : (Html_dd|Html_dt)+ =
  filter f {
    (dd[@..,
        h3[@.., val name as AnyEls],
        val folder as AnyEls]
       { 
         let val name = strcat(name) in
         dd[h3[a[@name[name],
	         name]],
	    putAnchors(folder)]  
       }
     | dt[@.., a[val attr as @.., val s as AnyEls]]
       { 
         dt[a[strip_bm_specific(attr), strcat(s)]] 
       })+
    | () 
       { dt[] }
  }


fun strip_bm_specific (val attrs as NS_a_attribs) : @href[String*]? =
  filter attrs {
    @^href[Any]*, @href[val x] { @href[x] }
  || Any { () }
  }

let val Any = main()

