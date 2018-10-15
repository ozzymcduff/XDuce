val mem : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
val add : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
val merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
val diff : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
val equal : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
