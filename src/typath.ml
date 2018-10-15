open Format

type t =
  [ `Lab of Label.t * t * t
  | `Att of Label.t * t * t
  | `Empty
  | `BaseVal of Base.baseval * t
  | `Any ]

let rec cat v w =
  match v with
  | `Lab (c, v1, v2) -> `Lab (c, v1, cat v2 w)
  | `Att (c, v1, v2) -> `Att (c, v1, cat v2 w)
  | `BaseVal (b, v1) -> `BaseVal (b, cat v1 w)
  | `Empty -> w
  | `Any -> w

let rec print ch w =
  match w with
  | `Lab (c, `Any, `Any) ->
      fprintf ch "@[<2>*%a*@ @[<1>[%a]@]@],@ %a" 
	Label.print c print `Any print `Any
  | `Lab (c, w1, w2) ->
      fprintf ch "@[<2>%a@ @[<1>[%a]@]@],@ %a" 
	Label.print c print w1 print w2
  | `Att (c, `Any, `Any) ->
      fprintf ch "@[<2>*@@%a*@ @[<1>[%a]@]+@],@ %a" 
	Label.print c print `Any print `Any
  | `Att (c, w1, w2) ->
      fprintf ch "@[<2>@@%a@ @[<1>[%a]+@]@],@ %a" 
	Label.print c print w1 print w2
  | `Empty ->
      fprintf ch "*()*"
  | `BaseVal (v, `Any) ->
      fprintf ch "@[<2>*%s*@],@ %a" (Base.string_of_baseval v) print `Any
  | `BaseVal (v, w1) ->
      fprintf ch "@[<2>%s@],@ %a" (Base.string_of_baseval v) print w1
  | `Any ->
      fprintf ch ".."


