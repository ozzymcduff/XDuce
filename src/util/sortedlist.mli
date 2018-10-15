val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
val merge_many : ('a -> 'a -> int) -> 'a list list -> 'a list
val isect : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
val diff : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list
val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int
val mem : ('a -> 'a -> int) -> 'a -> 'a list -> bool
