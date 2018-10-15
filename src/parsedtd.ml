open Syn
open Finfo
open Base
open Format
open List
open Pxp_yacc
open Pxp_types
open Pxp_dtd

exception DTD_error of string

let cats_of_seq tys =
  match tys with
    [] -> TEmpty(bogus())
  | [ty] -> ty
  | ty::tys -> fold_left (fun ty1 ty2 -> TCat(bogus(),ty1,ty2)) ty tys
	
let unions_of_alt tys =
  match tys with
    [] -> TNone(bogus())
  | [ty] -> ty
  | ty :: tys -> fold_left (fun ty1 ty2 -> TUnion(bogus(),ty1,ty2)) ty tys
	
let option_of_ty ty =
  TUnion(bogus(), ty, TEmpty(bogus()))

let clos_of_ty ty =
  TClos(bogus(), ty)

let type_name prefix elem_name = prefix ^ elem_name

let type_of_mixed prefix specl =
  clos_of_ty
    (unions_of_alt 
       (map
	  (function
	    | MPCDATA -> TBase(bogus(),BTString)
	    | MChild name -> TVar(bogus(), type_name prefix name))
	  specl))

let rec type_of_regexp prefix spec =
  match spec with
    Optional spec1 -> 
      option_of_ty(type_of_regexp prefix spec1)
  | Repeated spec1 ->
      TClos(bogus(), type_of_regexp prefix spec1)
  | Repeated1 spec1 ->
      TClos1(bogus(), type_of_regexp prefix spec1)
  | Alt specl ->
      unions_of_alt (map (type_of_regexp prefix) specl)
  | Seq specl ->
      cats_of_seq (map (type_of_regexp prefix) specl)
  | Child name ->
      TVar(bogus(),(type_name prefix name))

let type_of_contmod prefix contmod = 
  match contmod with
    Unspecified -> 
      raise (DTD_error "content model: Unspecified?")
  | Empty -> 
      TEmpty(bogus())
  | Any -> 
      TVar(bogus(),"Any")
  | Mixed specl -> 
      type_of_mixed prefix specl
  | Regexp spec ->
      type_of_regexp prefix spec

let type_of_att_type att_type =
      TClos(bogus(),TBase(bogus(),BTString))
(*
  match att_type with			
    A_cdata 
  | A_id
  | A_idref 
  | A_entity
  | A_nmtoken -> 
      TBase(bogus(),BTString)
  | A_idrefs
  | A_entities
  | A_nmtokens ->
      TClos(bogus(),TBase(bogus(),BTString))
  | A_enum sl -> 
      TBase(bogus(),BTString)
(*      unions_of_alt (map (fun s -> TSingle(bogus(), BVString s)) sl)*)
  | A_notation sl -> 
      TBase(bogus(),BTString)
(*      unions_of_alt (map (fun s -> TSingle(bogus(), BVString s)) sl)*)
*)

let type_of_attrs names attrs =
  let names = Sort.list (<) names in
  let tys =
    map 
      (fun name ->
	let att_ty = 
	  TAtt (bogus(), NQName("emptyprefix", Sym.label name),
		type_of_att_type(fst(attrs name))) in
	match snd(attrs name) with
	  D_required -> att_ty
	| D_implied | D_default _ | D_fixed _ -> option_of_ty(att_ty))
      names in
  cats_of_seq tys

let incorp_types_of_dtd prefix ns d =
  let elem_names = d # element_names in
  List.iter
    (fun elem_name ->
      let elem = d # element elem_name in
      let contmod = elem # content_model in
      let elem_type = 
	TLab(bogus(), NQName(ns, Sym.label elem_name),
	     TCat(bogus(),
		  type_of_attrs (elem # attribute_names) (elem # attribute),
		  type_of_contmod prefix contmod)) in
      Top.top.top_tydefs <- 
	(bogus(), type_name prefix elem_name, elem_type) :: Top.top.top_tydefs)
    elem_names

let rec print_error e =
  match e with
    At(where,what) ->
      print_endline where;
      print_error what
  |  _ ->
      raise e

let parse_dtd fi prefix params file_name =
  let prefix = 
    try prefix ^ (List.assoc "prefix" params)
    with Not_found -> prefix in
  let ns = Syn.new_name() in
  Ctx.add_nsdef ns 
    (Finfo.bogus(),
     Ns.of_uri
       (try List.assoc "namespace" params
       with Not_found -> ""));
  try
    let file_name = Filing.search_file !Pref.searchpaths file_name in
    let d = parse_dtd_entity default_config (from_file file_name) in
    incorp_types_of_dtd prefix ns d
  with
    e -> print_error e
  
