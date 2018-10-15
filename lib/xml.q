(*-------------------- Generic types for XML ------------------*)

type Xml_content = (Xml_elem | Xml_att | String)*
type Xml_elem = ~[Xml_content]
type Xml_att = @~[String*]

(*-------------------- XML type check ------------------*)

fun check_xml (val x as Any) : Xml_elem =
  match x with
    val x as Xml_elem -> x
  | Any -> error("Cast error", x)

(*-------------------- external XML writer ------------------*)

extern save_xml : (String)(Xml_elem) -> ()
extern load_xml : String -> Xml_elem

