type timer
val make : unit -> timer
val create : string -> timer
val start : timer -> unit
val stop : timer -> unit
val get : timer -> float
val dump : unit -> unit
val wrap : timer -> (unit -> 'a) -> 'a
val reset : timer -> unit
