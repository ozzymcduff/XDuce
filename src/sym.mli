type symbol = int

val n_syms : unit -> int
val name : symbol -> string
val rank : symbol -> int
val baseval : symbol -> Base.baseval option

val base : string -> symbol
val label : string -> symbol
val top : symbol
val any_label : symbol
val int : symbol
val string : symbol
val float : symbol
val single : Base.baseval -> symbol
val truel : symbol
val falsel : symbol

val predefined : symbol -> bool

val symbol_of_basety : Base.basety -> symbol
val symbol_of_baseval : Base.baseval -> symbol

val print : Format.formatter -> symbol -> unit
