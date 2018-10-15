type hash

type t =
  | Elm of Label.t * string * string list * string list
  | Attrep of Label.t * string * string list 
  | Alt of ht list
  | Seq of ht list
  | Rep of ht
  | Exe of int * ht

and ht = 
    { hash : hash; 
      def : t; 
      mutable adom : Label.t; 
      mutable ldom : Label.t;
      mutable rvars1 : string list option;
      mutable rvars2 : string list option }

val comp : ht -> ht -> int

module Tbl : Hashtbl.S with type key = ht

module Ht :
  sig
    type t = ht
    val compare : t -> t -> int
  end

module HtSet : Set.S with type elt = ht

val lookup_name : string -> ht
val define_name : string -> ht -> unit
val give_unique_name : ht -> string

val cons : t -> ht

val empty : ht
val epsilon : ht
val elm : Label.t -> string -> string list -> string list -> ht
val attrep : Label.t -> string -> string list -> ht
val alt : ht list -> ht
val seq : ht list -> ht
val rep : ht -> ht
val exe : int -> ht -> ht

val any : ht
val any_elm : ht
val string : ht
val int : ht
val float : ht
val single : Base.baseval -> string list -> string list -> ht
val base : Base.basety -> string list -> string list -> ht

val empty_name : string
val epsilon_name : string
val any_name : string

val nullable : ht -> bool
val is_empty : ht -> bool
val is_obviously_empty : ht -> bool
val is_att_free : ht -> bool

val elim_empty : ht -> ht
val reachable_vars1 : ht -> string list
val reachable_vars2 : ht -> string list
val reachable_exe_ids : ht -> int list

val sample : ht -> Syn.va

val size : ht -> int

val print : Format.formatter -> ht -> unit
val print_binding : Format.formatter -> unit -> unit
