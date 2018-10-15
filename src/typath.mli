type t =
  [ `Lab of Label.t * t * t
  | `Att of Label.t * t * t
  | `Empty
  | `BaseVal of Base.baseval * t
  | `Any ]

val cat : t -> t -> t

val print : Format.formatter -> t -> unit
