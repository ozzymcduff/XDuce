open Format
open Syn
open List
open Bltin
open Base

let rec print_error e =
  match e with
    Pxp_types.At(where,what) ->
      print_endline where;
      print_error what
  |  _ ->
      raise e

let va_of_attrs names attrs nsmgr =
  Listutil.mapcat
    (fun name ->
      let prefix, localname = Pxp_aux.namespace_split name in
      let ns = 
	if prefix = "" then Ns.empty else
	try Ns.of_uri(nsmgr # get_primary_uri prefix)
	with Not_found -> Ns.empty in
      match attrs name with
      | Pxp_types.Value s -> 
	  [MAtt(ns, Sym.label localname, [MBase(BVString s)])]
      | Pxp_types.Valuelist sl -> 
	  [MAtt(ns, Sym.label localname, List.map (fun s -> MBase(BVString s)) sl)]
      | Pxp_types.Implied_value ->
	  [])
    names
      
let empty_string = MBase(BVString "")

let rec insert_empty_strings prev va =
  match prev, va with
  | _, ((MAtt _) as v) :: va' ->
      v :: insert_empty_strings prev va'
  | (None | Some (MLab _)), [] -> 
      [empty_string]
  | (None | Some (MLab _)), ((MLab _) as v) :: va' -> 
      empty_string :: v :: insert_empty_strings (Some v) va'
  | (None | Some (MLab _)), ((MBase _) as v) :: va' ->
      v :: insert_empty_strings (Some v) va'
  | Some (MBase _), [] ->
      []
  | Some (MBase _), v :: va' ->
      v :: insert_empty_strings (Some v) va'
  | Some (MAtt _), _ ->
      assert false

let is_white_space s =
  let b = ref true in
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    if not(c = ' ' || c = '\t' || c = '\n' || c = '\r') then b := false
  done;
  !b

let rec va_of_node n =
  let ntype = n # node_type in
  match ntype with
    Pxp_document.T_element name ->
      let nsmgr = n # namespace_manager in
      let prefix, localname = Pxp_aux.namespace_split name in
      let ns = 
	if prefix = "" then Ns.empty else
	try Ns.of_uri(nsmgr # get_primary_uri prefix)
	with Not_found -> Ns.empty in
      [MLab (ns, Sym.label localname,
	     va_of_attrs (n # attribute_names) (n # attribute) nsmgr @
(*	     (insert_empty_strings *)
		 (Listutil.mapcat va_of_node (n # sub_nodes)))]
  | Pxp_document.T_data ->
      let s = n # data in
      if is_white_space s then [MWs s] else [MBase(BVString s)]
  | _ ->
      []

class warner =
  object 
    method warn w =
      print_endline ("WARNING: " ^ w)
  end

let id_opener id =
  let loc = 
    match id with 
      Pxp_types.System n -> n 
    | Pxp_types.Public (_,n) -> n 
    | Pxp_types.Anonymous -> raise Pxp_reader.Not_competent in
  let file_name =
    try
      let scheme = Neturl.extract_url_scheme loc in
      let syntax = Hashtbl.find Neturl.common_url_syntax scheme in
      let url = Neturl.url_of_string syntax loc in
      let path = Neturl.url_path url in 
      List.nth path (List.length path - 1)
    with 
      Neturl.Malformed_URL -> loc
    | Not_found -> raise Pxp_reader.Not_competent in
  try
    let abs_path = Filing.search_file !Pref.searchpaths file_name in
    open_in abs_path, None
  with
    Failure _ -> raise Pxp_reader.Not_competent

let load_xml file_name =
  try
    let config = 
      	  { Pxp_yacc.default_namespace_config with 
	      Pxp_yacc.debugging_mode = false;
	      Pxp_yacc.encoding = `Enc_utf8;
	      Pxp_yacc.idref_pass = true;
	      Pxp_yacc.warner = new warner
          } in
    let res = new Pxp_reader.resolve_read_any_channel ~channel_of_id:id_opener () in
    let src = Pxp_yacc.ExtID(Pxp_types.System(file_name),res) in
    let d = Pxp_yacc.parse_wfdocument_entity config 
	src Pxp_yacc.default_namespace_spec in
    va_of_node (d # root)
  with
    e ->
      print_error e

(* XML writer *)

let empty_dtd = 
  (new Pxp_dtd.dtd (new Pxp_types.drop_warnings) `Enc_iso88591)

let _ = empty_dtd # allow_arbitrary

let rec collect_nss va =
  Sortedlist.merge_many
    compare
    (Listutil.mapcat
       (function
	 | MLab(ns, _, va1) 
	 | MAtt(ns, _, va1) ->
	     [[ns]; collect_nss va1]
	 | MBase _ -> 
	     [])
       va)

let qname_string ns ln =
  if Ns.uri ns = "" then Sym.name ln else
  Sym.name ns ^ ":" ^ Sym.name ln

let attr_of_va va =
  Listutil.mapcat
    (fun el ->
      match el with
	MAtt(ns, c, [MBase(BVString s)]) ->
	  [(qname_string ns c, Pxp_types.Value s)]
      | MAtt(ns, c, l) ->
	  [(qname_string ns c, Pxp_types.Valuelist
	      (List.map
		 (fun el -> 
		   match el with
		     MBase(BVString s) -> s
		   | _ -> "")
		 l))]
      | _ ->
	  [])
    va

let separate_attrs va =
  List.partition (function MAtt _ -> true | _ -> false) va

let rec xml_of_elem el =
  match el with
    MBase(BVString s) ->
      Pxp_document.create_data_node Pxp_yacc.default_spec empty_dtd s
  | MLab(ns, c, va) ->
      let attr_va, rest_va = separate_attrs va in
      let attrs = attr_of_va attr_va in
      let n = Pxp_document.create_element_node Pxp_yacc.default_spec empty_dtd 
	  (qname_string ns c) [] in
      n # set_nodes (List.map xml_of_elem rest_va);
      n # quick_set_attributes attrs;
      n
  | MWs s ->
      Pxp_document.create_data_node Pxp_yacc.default_spec empty_dtd s
  | _ -> 
      failwith "Internal error in loadxml.xml_of_elem"

let ns_decls nss =
  Listutil.mapcat
    (fun ns -> 
      if Ns.uri ns = "" then [] else
	[("xmlns:" ^ Sym.name ns, Pxp_types.Value (Ns.uri ns))])
    nss

let save_xml fname va =
  let outch = open_out fname in
  let nss = collect_nss [va] in
  let n = xml_of_elem va in
  n # quick_set_attributes (ns_decls nss);
  let MLab(ns, c, _) = va in
  let d = new Pxp_document.document (new Pxp_types.drop_warnings) `Enc_iso88591 in
  d # init_root n (Sym.name ns ^ ":" ^ Sym.name c);
  let encoding = d # encoding in
  let os = `Out_channel outch in
  let encoding = d # encoding in
  let enc = `Enc_iso88591 in
  let wms = Pxp_aux.write_markup_string ~from_enc:encoding ~to_enc:enc os in
  let r = d # root in
  wms ("<?xml version='1.0' encoding='" ^
       Netconversion.string_of_encoding enc ^
       "'?>\n");
(*  d # write_pinstr os enc;*)
  r # write os enc;
  wms "\n";
  close_out outch

;;

add_bltin "load_xml" (function
    [[MBase(BVString fname)]] ->
      load_xml fname
  | _ -> raise Wrong_base_app);;

add_bltin "save_xml" (function
    [[MBase(BVString fname)]; [elem]] ->
      save_xml fname elem;
      []
  | _ -> raise Wrong_base_app);;

