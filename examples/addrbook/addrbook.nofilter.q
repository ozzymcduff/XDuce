import "xml.q"

type Addrbook = addrbook[Person*]
type Person = person[(Name,Tel?,Email* )]
type Name = name[String]
type Tel = tel[String]
type Email = email[String]

(* validate EXPR with TYPE tests conformance of the value of EXPR
   against TYPE.  If it fails, it displays a hint for the cause of the
   error.  *)

let val mybook = validate load_xml("mybook.xml") with Addrbook

(* Alternatively, we can write a tree equivalent to "mybook.xml"
   by XDuce notation:

let val mybook =
  addrbook[
    person[
      name["Haruo Hosoya"],
      email["hahosoya"],
      email["haruo"]],
    person[
      name["Jerome Vouillon"],
      tel["123-456-789"],
      email["vouillon"]],
    person[
      name["Benjamin Pierce"],
      email["bcpierce"]]]
*)

let val _ = print(mybook)

(* Just extract the content of addrbook for later manipulation *)

let val persons = 
  match mybook with
    addrbook[val ps] -> ps

(* The following two functions collect all persons with a tel field.
   In the first one, the pattern matching tests if the sequences
   begins with a person with tel, and if so, then extracts it;
   otherwise we skip it.  In the second function, the pattern matching
   skips all the persons with NO tel from the beginning, and extracts
   the first person with a tel.  *)

fun mkTelbook (val ps as Person* ) : entry[(Name,Tel)]* =
  match ps with
    person[name[val n], tel[val t],val e],val rest
        -> entry[name[n], tel[t]], mkTelbook(rest)
  | person[name[val n],val e],val rest
        -> mkTelbook(rest)
  | () 
        -> ()

let val _ = print(mkTelbook(persons))

fun mkTelbook2 (val ps as Person* ) : entry[(Name,Tel)]* =
  match ps with
    person[Name,Email*]*, 
        person[name[val n], tel[val t],val e],val rest
    -> entry[name[n], tel[t]], mkTelbook2(rest)
  | person[Name,Email*]* 
    -> ()

let val _ = print(mkTelbook2(persons))

