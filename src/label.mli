type t

val any_label : t
val ns_label : Sym.symbol -> t
val label : Sym.symbol -> Sym.symbol -> t
val base : Base.basety -> t
val single : Base.baseval -> t

val empty : t
val is_empty : t -> bool
val any : t
val is_obviously_any : t -> bool
val is_any : t -> bool

val disjoint : t -> t -> bool
val subset : t -> t -> bool
val overlapping : t -> t -> bool

val union : t -> t -> t
val inter : t -> t -> t
val diff : t -> t -> t
val compl : t -> t

val union_many : t list -> t

val equal : t -> t -> bool
val compare : t -> t -> int

val hash : t -> int

val is_finite : t -> bool
exception Infinite_label
val elt : t -> (Sym.symbol * Sym.symbol) list

val sample : t -> Sym.symbol * Sym.symbol

val print : Format.formatter -> t -> unit

