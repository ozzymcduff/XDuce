open List
open Finfo
open Base

let name_c = Counter.make()
let new_name() = "%X" ^ (string_of_int (Counter.next name_c))
  
(* types *)

type ty =
  | TVar of finfo * string 
  | TBase of finfo * basety
  | TSingle of finfo * baseval
  | TEmpty of finfo
  | TLab of finfo * nset * ty
  | TAtt of finfo * nset * ty
  | TCat of finfo * ty * ty
  | TUnion of finfo * ty * ty
  | TUnionF of finfo * ty * ty
  | TClos of finfo * ty
  | TClos1 of finfo * ty
  | TNone of finfo
  | TAs of finfo * string * ty
  | TTyAs of finfo * string * ty
  | TRule of finfo * ty * expr * int
  | TAttRem of finfo
  | TApp of finfo * string * expr option list
  | TSubst of finfo * ty * string * ty

and nset =
  | NQName of string * Sym.symbol
  | NNSName of string
  | NAnyName
  | NOr of nset * nset
  | NDiff of nset * nset

(* expressions *)

and expr =
  | EVar of finfo * string
  | EBase of finfo * baseval
  | EEmpty of finfo
  | ELab of finfo * string * Sym.symbol * expr
  | EAtt of finfo * string * Sym.symbol * expr
  | EAnyLab of finfo * expr * expr * expr
  | ECopyLab of finfo * expr * expr 
  | ECat of finfo * expr * expr
  | EApp of finfo * string * expr list
  | ESeq of finfo * expr * expr
  | EFilter of finfo * expr * ty * int ref
  | ECast of finfo * ty * expr * bool * int ref * expr option
  | ETry of finfo * expr * string * expr
  | ERaise of finfo * expr
	
and clause = ty * expr * int ref 

(* values *)

type elem =
  | MBase of baseval
  | MLab of Sym.symbol * Sym.symbol * va
  | MAtt of Sym.symbol * Sym.symbol * va
  | MWs of string

and va = elem list

(* environments *)

module Env =
  Map.Make
    (struct 
      type t = string
      let compare = compare
    end)

type venv = va Env.t

(* toplevels *)

type valdef = finfo * ty * int ref * expr
      (* val pat = expr *)
(*type valty = string * ty*)
type fundef = finfo * string * string list * (ty * int ref) list * ty * expr
      (* fun f{ X ... } (pat,...) : ty = expr *)
type bltin = finfo * string * string list * ty list * ty * (va list -> va)
      (* bltin f { X ...} (ty,...) : ty = caml_func *)
type tydef = finfo * string * ty 
      (* type X = ty *)
type caltype = string * ty list
      (* calty op ty ... *)
type nsdef = finfo * string * string
      (* namespace prefix = url *)

type top =
    { mutable top_tydefs : tydef list;
      mutable top_fundefs : fundef list;
      mutable top_bltins : bltin list;
      mutable top_valdefs : valdef list;
      mutable top_caltype : caltype list;
      mutable top_nsdefs : nsdef list;
    }

(* counters *)

let filter_ctr = Counter.make()
let next_filter_id() = Counter.next filter_ctr
