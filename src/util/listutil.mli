val mapcat : ('a -> 'b list) -> 'a list -> 'b list
val split_list : ('a -> bool) -> 'a list -> 'a list * 'a list
val union_many : ('a list -> 'a list -> 'a list) -> 'a list list -> 'a list
val compare_list : ('a -> 'a -> int) -> 'a list -> 'a list -> int
val same_list : 'a list -> 'a list -> bool
val peak : ('a -> int) -> 'a list -> 'a
val index : ('a -> bool) -> 'a list -> int
