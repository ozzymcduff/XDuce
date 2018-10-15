open Format

type repr = (Sym.symbol * repr') list
and repr' = Pos of repr | Neg of repr

type t = { hash : int; repr : repr }
type t' = t

module InternTbl =
  Hashtbl.Make
    (struct 
      type t = t'
      let equal r1 r2 = r1.hash = r2.hash && r1.repr = r2.repr
      let hash r = r.hash
    end)

let hash_combine h h' = h + 31 * h'
let rec hash_repr c =
  (List.fold_right
    (fun d h ->
      match d with
      |	(s, Pos c) -> 
	  hash_combine (3 * s) (hash_combine (hash_repr c) h)
      |	(s, Neg c) ->
	  hash_combine (7 * s) (hash_combine (hash_repr c) h))
    c 0)
    land 0x3FFFFFFF

let intern_tbl = InternTbl.create 121
let id_count = Counter.create "label id"
let intern c =
  let r = { hash = hash_repr c; repr = c } in
  try 
    InternTbl.find intern_tbl r
  with Not_found ->
    InternTbl.add intern_tbl r r;
    Counter.incr id_count;
    r

let equal = (==)

let empty = intern []
let is_empty c = equal c empty

let rec union_rec c1 c2 =
  if c1 == c2 then c1 else
  match c1, c2 with
  | [], _ -> c2
  | _, [] -> c1
  | ((s1, d1) as p1) :: c1', ((s2, d2) as p2) :: c2' ->
      if s1 < s2 then p1 :: union_rec c1' c2 else
      if s2 < s1 then p2 :: union_rec c1 c2' else
      match d1, d2 with
      |	Pos c1'', Pos c2'' -> 
	  let c3 = union_rec c1'' c2'' in
	  if c3 = [] then union_rec c1' c2' else
	  (s1, Pos c3) :: union_rec c1' c2'
      |	Pos c1'', Neg c2'' ->
	  (s1, Neg (diff_rec c2'' c1'')) :: union_rec c1' c2'
      |	Neg c1'', Pos c2'' ->
	  (s1, Neg (diff_rec c1'' c2'')) :: union_rec c1' c2'
      |	Neg c1'', Neg c2'' ->
	  (s1, Neg (inter_rec c1'' c2'')) :: union_rec c1' c2'

and inter_rec c1 c2 =
  if c1 == c2 then c1 else
  match c1, c2 with
  | [], _ -> []
  | _, [] -> []
  | (s1, d1) :: c1', (s2, d2) :: c2' ->
      if s1 < s2 then inter_rec c1' c2 else
      if s2 < s1 then inter_rec c1 c2' else
      match d1, d2 with
      |	Pos c1'', Pos c2'' -> 
	  let c3 = inter_rec c1'' c2'' in
	  if c3 = [] then inter_rec c1' c2' else
	  (s1, Pos c3) :: inter_rec c1' c2'
      |	Pos c1'', Neg c2'' ->
	  let c3 = diff_rec c1'' c2'' in
	  if c3 = [] then inter_rec c1' c2' else
	  (s1, Pos c3) :: inter_rec c1' c2'
      |	Neg c1'', Pos c2'' ->
	  let c3 = diff_rec c2'' c1'' in
	  if c3 = [] then inter_rec c1' c2' else
	  (s1, Pos c3) :: inter_rec c1' c2'
      |	Neg c1'', Neg c2'' ->
	  (s1, Neg (union_rec c1'' c2'')) :: inter_rec c1' c2'

and diff_rec c1 c2 =
  if c1 == c2 then [] else
  match c1, c2 with
  | [], _ -> []
  | _, [] -> c1
  | (s1, d1) :: c1', (s2, d2) :: c2' ->
      if s1 < s2 then (s1, d1) :: diff_rec c1' c2 else
      if s2 < s1 then diff_rec c1 c2' else
      match d1, d2 with
      |	Pos c1'', Pos c2'' -> 
	  let c3 = diff_rec c1'' c2'' in
	  if c3 = [] then diff_rec c1' c2' else
	  (s1, Pos c3) :: diff_rec c1' c2'
      |	Pos c1'', Neg c2'' ->
	  let c3 = inter_rec c1'' c2'' in
	  if c3 = [] then diff_rec c1' c2' else
	  (s1, Pos c3) :: diff_rec c1' c2'
      |	Neg c1'', Pos c2'' ->
	  (s1, Neg (union_rec c1'' c2'')) :: diff_rec c1' c2'
      |	Neg c1'', Neg c2'' ->
	  let c3 = diff_rec c2'' c1'' in
	  if c3 = [] then diff_rec c1' c2' else
	  (s1, Pos c3) :: diff_rec c1' c2'

let rec disjoint_rec c1 c2 =
  if c1 == c2 then c1 = [] else
  match c1, c2 with
  | [], _ -> true
  | _, [] -> true
  | (s1, d1) :: c1', (s2, d2) :: c2' ->
      if s1 < s2 then disjoint_rec c1' c2 else
      if s2 < s1 then disjoint_rec c1 c2' else
      match d1, d2 with
      |	Pos c1'', Pos c2'' -> 
	  disjoint_rec c1'' c2'' && disjoint_rec c1' c2' 
      |	Pos c1'', Neg c2'' ->
	  subset_rec c1'' c2'' && disjoint_rec c1' c2' 
      |	Neg c1'', Pos c2'' ->
	  subset_rec c2'' c1'' && disjoint_rec c1' c2' 
      |	Neg c1'', Neg c2'' ->
	  false

and subset_rec c1 c2 =
  if c1 == c2 then true else
  match c1, c2 with
  | [], _ -> true
  | _, [] -> false
  | (s1, d1) :: c1', (s2, d2) :: c2' ->
      if s1 < s2 then false else
      if s2 < s1 then subset_rec c1 c2' else
      match d1, d2 with
      |	Pos c1'', Pos c2'' -> 
	  subset_rec c1'' c2'' && subset_rec c1' c2' 
      |	Pos c1'', Neg c2'' ->
	  disjoint_rec c1'' c2'' && subset_rec c1' c2' 
      |	Neg c1'', Pos c2'' ->
	  false
      |	Neg c1'', Neg c2'' ->
	  subset_rec c2'' c1'' && subset_rec c1' c2' 

let rec elim_empty c =
  match c with
  | [] ->
      []
  | (s, Pos c') :: rest ->
      let c'' = elim_empty c' in
      if c'' = [] then elim_empty rest else 
      (s, Pos c'') :: elim_empty rest
  | (s, Neg c') :: rest ->
      (s, Neg (elim_empty c')) :: elim_empty rest

let union r1 r2 =
  if r1 == r2 then r1 else
  intern (union_rec r1.repr r2.repr)

let rec union_many cl = 
  match cl with
  | [] -> empty
  | c :: cl -> union c (union_many cl)

let inter r1 r2 = intern (inter_rec r1.repr r2.repr)
let diff r1 r2 = intern (diff_rec r1.repr r2.repr)

let hash r = r.hash
let compare r1 r2 = 
  let c = compare r1.hash r2.hash in
  if c <> 0 then c else
  compare r1 r2

let any_label = intern [(Sym.any_label, Neg [])]
let ns_label ns = intern [(Sym.any_label, Pos [(ns, Neg [])])]
let label ns s = intern [(Sym.any_label, Pos [(ns, Pos [(s, Neg [])])])]
let base bty = intern [(Sym.symbol_of_basety bty, Neg [])]
let single bv = intern [(Sym.symbol_of_baseval bv, Pos [(Sym.single bv, Neg [])])]
let any = 
  union_many [any_label; 
	      base Base.BTString; 
	      base Base.BTInt; 
	      base Base.BTFloat]
let is_obviously_any c = equal c any

let compl r = diff any r
let subset r1 r2 = subset_rec r1.repr r2.repr
let is_any r = subset any r
let disjoint r1 r2 = disjoint_rec r1.repr r2.repr
let overlapping r1 r2 = not (disjoint r1 r2)

let is_finite c = (* applied only to non-base-type labels *)
  List.for_all
    (fun (s, d) -> 
      s = Sym.any_label &&
      match d with
      | Neg _ -> false
      | Pos l ->
	  List.exists
	    (fun (ns, d) ->
	      match d with
	      | Neg _ -> false
	      | Pos _ -> true)
	    l)
    c.repr

exception Infinite_label

let elt c = (* applied only to non-base-type labels *)
  if c.repr = [] then [] else
  Listutil.mapcat
    (fun (s, d) ->
      if s != Sym.any_label then assert false else
      match d with
      | Pos c' -> 
	  Listutil.mapcat
	    (fun (s', d') ->
	      match d' with
	      | Pos c'' -> List.map (fun (s'', _) -> (s', s'')) c''
	      | Neg _ -> raise Infinite_label)
	    c'
      | Neg _ -> raise Infinite_label)
    c.repr

let dummy_sym = Sym.label "???"

let rec sample c =			(* XXX: super-adhoc *)
  match c with
  | (_, Pos ((s, Pos ((s', _) :: _)) :: _)) :: _ ->
      s, s'
  | (s, Pos ((s', Neg _) :: _)) :: _ ->
      if s == Sym.string || s == Sym.int || s == Sym.float then
	s, s' 
      else
	s', dummy_sym
  | (s, Neg c) :: _ when s == Sym.any_label ->
      dummy_sym, dummy_sym
  | (s, Neg c) :: _ when s == Sym.string ->
      s, Sym.single (Base.BVString "???")
  | (s, Neg c) :: _ when s == Sym.int ->
      s, Sym.single (Base.BVInt 0)
  | (s, Neg c) :: _ when s == Sym.float ->
      s, Sym.single (Base.BVFloat 0.0)
  | _ ->
      assert false

let sample c = 
  let c = elim_empty c.repr in
  if c = [] then raise Not_found else
  sample c

let rec print_qname ch ns (s, d) =
  match d with
  | Neg [] ->
      fprintf ch "%a:%a" Sym.print ns Sym.print s
  | _ ->
      assert false

and print_ns ch (s, d) =
  match d with
  | Neg [] ->
      fprintf ch "%a:~" Sym.print s
  | Neg c ->
      fprintf ch "%a:~ \\ @[<1>(" Sym.print s;
      Printing.print_list
        (fun () -> fprintf ch "@ |@ ") 
	(print_qname ch s) c;
      fprintf ch ")@]"
  | Pos c ->
      fprintf ch "@[<1>(";
      Printing.print_list
        (fun () -> fprintf ch "@ |@ ") 
	(print_qname ch s) c;
      fprintf ch ")@]"
      
and print ch c = (* applied only to non-base-type labels *)
  match c with
  | [] ->
      fprintf ch "0"
  | [(s, d)] when s == Sym.any_label ->
      begin
	match d with
	| Neg [] ->
	    Sym.print ch s
	| Neg c ->
	    Format.fprintf ch "@[<1>^(";
	    Printing.print_list
              (fun () -> Format.fprintf ch "@ |@ ") (print_ns ch) c;
	    Format.fprintf ch ")@]"
	| Pos c ->
	    Format.fprintf ch "@[<1>(";
	    Printing.print_list
              (fun () -> Format.fprintf ch "@ |@ ") (print_ns ch) c;
	    Format.fprintf ch ")@]"
      end
  | _ -> 
      Format.fprintf ch "***"
      (*assert false*)

let print ch c = print ch c.repr

