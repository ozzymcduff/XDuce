open Bltin
open Syn
open Str
open List

let elem2str = function
  | MBase _ -> ""
  | MWs _ -> ""
  | MLab (ns, l, _) -> Sym.name ns ^ ":" ^ Sym.name l
  | MAtt _ -> ""

let compare elem1 elem2 = compare (elem2str elem1) (elem2str elem2)

let sort_xml_nodes = function
    [nodes] -> sort compare nodes
  | _ -> raise Wrong_base_app
      
let _ =
  add_bltin "sort_xml_nodes" sort_xml_nodes
