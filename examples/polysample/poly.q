(* definition of generic types and functions *)

type AList = entry[key[String], data[ty X]]*
type Res = found[ty X] | notfound[]

fun search {{X}} (val key1 as String)(val data as AList) : Res =
  match data with
    entry[key[val key2], data[val d]], val r ->
      if key1 = key2 then found[d] else search (key1)(r)
  | () ->
      notfound[]

fun search2 {{X}} (val key1 as String)(val data as AList) : Res =
  filter data {
    entry[key[val key2], data[val d]], val r
      { if key1 = key2 then found[d] else search2 (key1)(r) }
  | () 
      { notfound[] }
}

(* Bib instance *)

type Bib = bib[Author+, Title]
type Author = author[String]
type Title = title[String]

let val mybib as (AList{{X -> Bib}}) = 
  entry[key["HFC05"],
	data[bib[author["Hosoya"],
		 author["Frisch"],
		 author["Castagna"],
		 title["PolyX"]]]],
  entry[key["HVP00"],
	data[bib[author["Hosoya"],
		 author["Vouillon"],
		 author["Pierce"],
		 title["SubX"]]]]

let val res as (Res{{X -> Bib}}) = search("HFC05")(mybib)

let Any = print(res)

let val res2 as (Res{{X -> Bib}}) = search2("HFC05")(mybib)

let Any = print(res2)

(* Piece instance *)

type Piece = piece[title[String], key[String]]

let val music as (AList{{X -> Piece}}) =
  entry[key["Chopin Op.23"],
	data[piece[title["Balade"],
		   key["G minor"]]]],
  entry[key["Chopin Op.10-1"],
	data[piece[title["Etude"],
		   key["C major"]]]],
  entry[key["Beethoven Op.110"],
	data[piece[title["Piano Sonata"],
		   key["A flat major"]]]]

let val res as (Res{{X -> Piece}}) = search("Chopin Op.10")(music)

let Any = print(res)

let val res2 as (Res{{X -> Piece}}) = search2("Beethoven Op.110")(music)

let Any = print(res2)

(*

fun wrong1 {{X}} (val x as (a[ty X],c[] | a[b[]],ty X)) : Any = x

fun wrong2 {{X}} (val x as a[ty X]) : Any =
  filter x {
    (val y as a[Res]) { y }
  }

fun wrong3 {{X}} (val x as a[ty X as (a[],b[] )]) : Any = x

type Wrong = AList{{X -> Wrong}}

*)
