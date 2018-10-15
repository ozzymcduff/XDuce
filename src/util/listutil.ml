open List

let rec mapcat f = function
    [] -> []
  | x :: xl -> (f x) @ (mapcat f xl)

let split_list (f:'a -> bool) : 'a list -> 'a list * 'a list =
  let rec loop = function
    | [] -> [],[]
    | el :: rest ->
        let ls1, ls2 = loop rest in
        if f el then el :: ls1, ls2
        else ls1, el :: ls2 in
  loop

let union_many f l =
  let rec union2 = function
      s1 :: s2 :: rest -> f s1 s2 :: union2 rest
    | l -> l in
  let rec union_all = function
      [] -> []
    | [s] -> s
    | l -> union_all (union2 l) in
  union_all l

let rec compare_list f l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x1 :: l1, x2 :: l2 -> 
      let c = f x1 x2 in
      if c <> 0 then c else compare_list f l1 l2

let rec same_list l l' = 
  l == l' ||
  match l, l' with
    [], [] -> true
  | x :: r, x' :: r' -> x == x' && same_list r r'
  | _ -> false

let peak f l =
  let rec iter max peak l =
    match l with
    | [] -> peak
    | x :: l -> 
	let v = f x in
	if v > max then iter v x l else iter max peak l in
  match l with
  | [] -> raise Not_found
  | x :: l -> iter (f x) x l

let index f l =
  let rec iter l i =
    match l with
      [] -> raise Not_found
    | x :: l -> if f x then i else iter l (i + 1) in
  iter l 0
