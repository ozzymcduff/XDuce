open Base
open List

type symbol = int

(* symbol *)

type symbol_val = 
    Const 
  | Unary of string
  | Binary of string
  | Single of baseval

let tbl : (symbol_val, symbol) Hashtbl.t = Hashtbl.create 121
let sym_c = Counter.make()
let inv_tbl = ref (Array.create 100 Const)

let n_syms() = Counter.get sym_c

let get_inv_tbl sym = 
  (!inv_tbl).(sym)
let put_inv_tbl v =
  let sym = Counter.next sym_c in
  if sym >= Array.length !inv_tbl then
    inv_tbl := Array.append !inv_tbl (Array.create 100 Const);
  (!inv_tbl).(sym) <- v;
  sym

let make_symbol v =
  try 
    Hashtbl.find tbl v
  with Not_found ->
    let sym = put_inv_tbl v in
    Hashtbl.add tbl v sym;
    sym

let rank sym =
  match get_inv_tbl sym with
    Const -> 0
  | Unary _ | Single _ -> 1
  | Binary _ -> 2

let name sym =
  match get_inv_tbl sym with
    Const -> "[]"
  | Unary s -> s
  | Binary s -> s
  | Single v -> (match v with
      BVString s -> "\"" ^ s ^ "\""
    | BVInt i -> string_of_int i
    | BVFloat f -> string_of_float f)

let baseval sym =
  match get_inv_tbl sym with
    Single v -> Some v
  | _ -> None

(* symbols *)

let base nm = make_symbol (Unary nm)
let empty = make_symbol Const
let label nm = make_symbol (Binary nm)
let single v = make_symbol (Single v)

let top = label "(top)"
let any_label = label "~"
let string = base "String"
let int = base "Int"
let float = base "Float"
let truel = label "True"
let falsel = label "False"

let predefined s =
  rank s = 1 || s = any_label || s = top
  
let symbol_of_basety = function
    BTString -> string
  | BTInt -> int
  | BTFloat -> float

let symbol_of_baseval = function
    BVString _ -> string
  | BVInt _ -> int
  | BVFloat _ -> float

open Format

let print ff sym = fprintf ff "%s" (name sym)

