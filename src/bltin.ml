open List
open Syn
open Finfo
open Sym
open Base

(* built-in functions *)

let bltins : (string, va list -> va) Hashtbl.t = Hashtbl.create 121
let add_bltin name f = Hashtbl.add bltins name f

exception Bltin_not_found of string

let lookup_builtin name =
  try Hashtbl.find bltins name with
    Not_found -> raise (Bltin_not_found name)

exception Wrong_base_app
exception Bltin_error_intern of string

let boolval = function
    true -> Synutil.true_va
  | false -> Synutil.false_va

let intval i = [MBase(BVInt i)]
let floatval i = [MBase(BVFloat i)]

let bin_int_op f = function
    [[MBase(BVInt i1)]; [MBase(BVInt i2)]] -> intval (f i1 i2)
  | _ -> raise Wrong_base_app

let bin_int_pred f = function
    [[MBase(BVInt i1)]; [MBase(BVInt i2)]] -> boolval (f i1 i2)
  | _ -> raise Wrong_base_app

let bin_float_op f = function
    [[MBase(BVFloat r1)]; [MBase(BVFloat r2)]] -> floatval (f r1 r2)
  | _ -> raise Wrong_base_app


