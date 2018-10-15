let rec merge comp r s =
  match r, s with
    [], _ -> s
  | _, [] -> r
  | x :: r', y :: s' ->
      let c = comp x y in
      if c = 0 then x :: merge comp r' s'
      else if c < 0 then x :: merge comp r' s
      else y :: merge comp r s'

let rec compare comp l1 l2 =
  match l1, l2 with
    [], [] -> 0
  | _, [] -> -1
  | [], _ -> 1
  | s1::r1, s2::r2 -> 
      let c = comp s1 s2 in
      if c <> 0 then c
      else compare comp r1 r2

let rec diff comp l l' =
  match l, l' with
    [], _ -> []
  | _, [] -> l
  | x :: r, x' :: r' ->
      let c = comp x x' in
      if c < 0 then
        x :: diff comp r l'
      else if c = 0 then
        diff comp r r'
      else
        diff comp l r'

let rec isect comp r s =
  match r, s with
    [], _ -> []
  | _, [] -> []
  | x :: r', y :: s' ->
      let c = comp x y in
      if c = 0 then x :: isect comp r' s'
      else if c < 0 then isect comp r' s
      else isect comp r s'

let rec mem comp x l =
  match l with
    [] -> false
  | y :: l ->
      let c = comp x y in
      if c = 0 then true
      else if c < 0 then mem comp x l
      else false

let merge_many comp ls = Listutil.union_many (merge comp) ls
