exception Unbound of Finfo.finfo * string * string
exception Multidef of Finfo.finfo * string * string

val add_valdef : string -> Syn.va -> unit
val lookup_valdef : Finfo.finfo -> string -> Syn.va

val add_tydef : string -> Finfo.finfo * Syn.ty -> unit
val lookup_tydef : Finfo.finfo -> string -> Syn.ty
val iter_tydef : (string -> Finfo.finfo * Syn.ty -> unit) -> unit

val add_fundef :
  string ->
  Finfo.finfo * string list * (Syn.ty * int ref) list * Syn.ty * Syn.expr ->
  unit

val lookup_fundef :
  Finfo.finfo ->
  string -> string list * (Syn.ty * int ref) list * Syn.ty * Syn.expr

val add_bltin :
  string -> Finfo.finfo * string list * Syn.ty list * Syn.ty * (Syn.va list -> Syn.va) -> unit
val lookup_bltin :
  Finfo.finfo -> string -> string list * Syn.ty list * Syn.ty * (Syn.va list -> Syn.va)
val is_bltin : string -> bool

val add_nsdef : string -> Finfo.finfo * Sym.symbol -> unit
val lookup_nsdef : Finfo.finfo -> string -> Sym.symbol

