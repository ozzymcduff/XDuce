val print_list : (unit -> 'a) -> ('b -> unit) -> 'b list -> unit
val print_set :
  Format.formatter -> (Format.formatter -> 'a -> unit) -> 'a list -> unit
val print_tuple :
  Format.formatter -> (Format.formatter -> 'a -> unit) -> 'a list -> unit
