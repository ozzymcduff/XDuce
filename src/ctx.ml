open Syn
open Finfo

(* contexts *)

let valdefs : venv ref = ref Env.empty

let tydefs : (string, finfo * ty) Hashtbl.t = Hashtbl.create 121

let fundefs : (string, finfo * string list * (ty * int ref) list * ty * expr) Hashtbl.t =
  Hashtbl.create 121

let bltins : (string, finfo * string list * ty list * ty * (va list -> va)) Hashtbl.t =
  Hashtbl.create 121

let nsdefs : (string, Sym.symbol) Hashtbl.t =
  Hashtbl.create 121

(* context operations *)

exception Unbound of Finfo.finfo * string * string
exception Multidef of Finfo.finfo * string * string

let add_valdef x va =
  valdefs := Env.add x va !valdefs

let lookup_valdef fi x = 
  try
    Env.find x !valdefs
  with Not_found ->
    raise (Unbound (fi,"variable",x))

let add_fundef x (fi, type_params, pat_cell_pairs, resty, body) =
  if Hashtbl.mem fundefs x then
    raise (Multidef (fi, "function name", x))
  else
    Hashtbl.add fundefs x (fi, type_params, pat_cell_pairs, resty, body)

let lookup_fundef fi f =
  try
    let (_, type_params, pat_cell_pairs, resty, body) = 
      Hashtbl.find fundefs f in
    type_params, pat_cell_pairs, resty, body
  with Not_found ->
    raise (Unbound (fi, "function name", f))

let add_tydef x (fi, ty) =
  if Hashtbl.mem tydefs x then
    raise (Multidef (fi, "type name", x))
  else
    Hashtbl.add tydefs x (fi, ty)

let iter_tydef f = Hashtbl.iter f tydefs

let lookup_tydef fi x =
  try
    let _, ty = Hashtbl.find tydefs x in
    ty
  with Not_found -> 
    raise (Unbound (fi, "type name", x))

let lookup_bltin fi x =
  try
    let (_, typarams, paramtys, resty, f) = Hashtbl.find bltins x in
    typarams, paramtys, resty, f
  with Not_found -> 
    raise (Unbound (fi, "builtin function name", x))

let is_bltin x =
  Hashtbl.mem bltins x

let add_bltin x (fi, typarams, argty, resty, f) =
  if Hashtbl.mem bltins x then
    raise (Multidef (fi, "built-in function name", x))
  else
    Hashtbl.add bltins x (fi, typarams, argty, resty, f)

let add_nsdef x (fi, url) =
  Hashtbl.add nsdefs x url

let lookup_nsdef fi x =
  try
    let url = Hashtbl.find nsdefs x in
    url
  with Not_found ->
    raise (Unbound (fi, "namespace", x))



