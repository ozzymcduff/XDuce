let rec mem eq x l =
  match l with
    [] -> false
  | x' :: _ when eq x x' -> true
  | _ :: r -> mem eq x r

let add eq x l =
  if mem eq x l then l else x :: l

let merge eq l1 l2 =
  l1 @ (List.filter (fun x -> not(mem eq x l1)) l2)

let diff eq l1 l2 =
  List.filter (fun x -> not(mem eq x l2)) l1

let rec equal eq l1 l2 =
  List.for_all (fun x -> mem eq x l2) l1 &&
  List.for_all (fun x -> mem eq x l1) l2

