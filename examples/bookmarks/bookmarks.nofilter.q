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
    html [AnyAttrs,
	  NS_head,
	  NS_body]

type NS_head =
    head [AnyAttrs,
	  meta [AnyAttrs],
	  title [AnyAttrs,
		 String*]]
      
type NS_body =
    body [AnyAttrs,
	  h1 [AnyAttrs,
	      String*],
	  NS_folder]
		    
type NS_folder =
    NS_dl*

type NS_dl = 
    dl [AnyAttrs,
	(NS_dt | NS_dd)*]

type NS_dt =
    dt [AnyAttrs,
	NS_a]
	    
type NS_dd =
    dd [AnyAttrs,
	NS_h3,
	NS_folder]

type NS_h3 = h3 [AnyAttrs,
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
  match argv() with
    val infile as String, val outfile as String ->
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
  | Any ->
      print("Usage: <xduce-program> bookmarks.q -- <input-file> <output-file>")

(*-------------------- String Concat ------------------*)

fun strcat (val l as String* ) : String =
  match l with
    () -> ""
  | val x as String, val y -> x ^ strcat(y)

(*-------------------- Get title and folder ------------------*)

type AnyEls = (~[Any] | String)*

fun getTitle (val b as NS_bookmarks) : String =
  match b with
    html [AnyAttrs,
	  head [Any],
	  body [AnyAttrs,
		h1 [AnyAttrs,
		    val title as String*],
		AnyEls]]
    -> strcat(title)

fun getFolder (val b as NS_bookmarks) : NS_folder =
  match b with
    html [AnyAttrs,
	  AnyEls,
	  body [AnyAttrs,
		h1 [Any],
		val folder as AnyEls],
	  AnyEls]
    -> folder

(*-------------------- Find Public Folder ------------------*)

fun findPublic (val f as NS_folder) :  res[NS_folder]* =
  match f with
    dl [AnyAttrs, val dt as AnyEls], val rest
       -> findPublicDt(dt), findPublic(rest)
  | () -> ()

fun findPublicDt (val ds as (NS_dt|NS_dd)* ) : res[NS_folder]* =
  match ds with
    dd [AnyAttrs, h3 [AnyAttrs, "Public"], val folder as AnyEls], val rest
       -> res[folder]
  | dd [AnyAttrs, NS_h3, val folder as AnyEls], val rest 
       -> findPublic(folder), findPublicDt(rest)
  | NS_dt, val rest 
       -> findPublicDt(rest)
  | () -> ()

fun firstPublic (val rs as res[NS_folder]* ) : NS_folder =
  match rs with
    res [AnyAttrs, val folder as AnyEls], Any
      -> folder
  | ()
      -> error ("Can't find a \"" ^ "Public" ^ "\" folder")

(*-------------------- Table of Contents ------------------*)

fun tocTop (val f as NS_folder) : Html_li* =
  match f with
    dl [AnyAttrs, val dt as AnyEls], val rest
       -> tocFirst(dt), tocTop(rest)
  | () -> ()

fun tocFirst (val ds as (NS_dt|NS_dd)* ) : Html_li* =
  match ds with
    dd [AnyAttrs, h3 [AnyAttrs, val names as AnyEls], val folder as AnyEls], val rest 
    -> let val name = strcat(names) in
       li [a[@href ["#" ^ name],
	     b[name]], ": ",
           tocSecondTop(folder)],
       tocFirst(rest)
  | NS_dt, val rest
    -> tocFirst(rest) 
  | ()
    -> ()

fun tocSecondTop (val f as NS_folder) : (Html_a | String)* =
  match f with
    dl [AnyAttrs, val dt as AnyEls], val rest 
      -> tocSecond(dt), tocSecondTop(rest)
  | ()
      -> ()

fun tocSecond (val ds as (NS_dt|NS_dd)* ) : (Html_a | String)* =
  match ds with
    dd [AnyAttrs, h3 [AnyAttrs, val name as AnyEls], val folder as AnyEls], 
    val rest
    -> let val name = strcat(name) in
       a[@href ["#" ^ name],
	 name], "/",
       tocSecond(rest)
  | NS_dt, val rest
    -> tocSecond(rest)
  | ()
    -> ()

(*-------------------- Anchors ------------------*)

fun putAnchors (val f as NS_folder) : (Html_dl | String)* =
  match f with
    dl[val attr as AnyAttrs, val dt as AnyEls], val rest
    -> dl [putAnchorsDt(dt)], putAnchors(rest)
  | ()
    -> ()

fun putAnchorsDt (val f as (NS_dt|NS_dd)* ) : (Html_dd|Html_dt)+ =
  match f with
    dd[AnyAttrs,
       h3[AnyAttrs, val name as AnyEls],
       val folder as AnyEls],
    val rest
    -> let val name = strcat(name) in
       dd[h3[a[@name[name],
	       name]],
	  putAnchors(folder)],
       putAnchorsDt(rest)
  | dt [AnyAttrs, a[val attr as AnyAttrs, val s as AnyEls]], val rest
    -> dt[a[strip_bm_specific(attr), strcat(s)]], 
       putAnchorsDt(rest)
  | ()
    -> dt[]

fun strip_bm_specific (val attrs as NS_a_attribs) : @href[String*]? =
  match attrs with
    @^href[Any]*, @href[val x] -> @href[x] 
(*    Any, href[val x], Any -> href[x]  *)
  | Any -> ()

let val Any = main()

