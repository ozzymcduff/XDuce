open Format

let tm_nullable = Timer.create "htype:nullable"
let tm_is_empty = Timer.create "htype:is_empty"
let tm_elim_empty = Timer.create "htype:elim_empty"
let tm_reachable_vars = Timer.create "htype:reachable_vars"
let ctr_define_name = Counter.create "htype:define_name"

type hash = int
type t =
  | Elm of Label.t * string * string list * string list
  | Attrep of Label.t * string * string list 
  | Alt of ht list
  | Seq of ht list
  | Rep of ht
  | Exe of int * ht

and ht = 
    { hash : hash; 
      def : t; 
      mutable adom : Label.t; 
      mutable ldom : Label.t;
      mutable rvars1 : string list option;
      mutable rvars2 : string list option }

(* Hash consing *)

let equal ht1 ht2 =
  ht1.hash = ht2.hash &&
  match ht1.def, ht2.def with
  | Elm (s1, n1, xs1, ys1), Elm (s2, n2, xs2, ys2) ->
      n1 == n2 && Label.equal s1 s2 && Listutil.same_list xs1 xs2 && Listutil.same_list ys1 ys2
  | Attrep (s1, n1, xs1), Attrep (s2, n2, xs2) -> 
      n1 == n2 && Label.equal s1 s2 && Listutil.same_list xs1 xs2
  | Alt l1, Alt l2 | Seq l1, Seq l2 -> 
      Listutil.same_list l1 l2 
  | Rep ht1', Rep ht2' -> ht1' == ht2'
  | Exe (i1, ht1'), Exe (i2, ht2') -> i1 == i2 && ht1' == ht2'
  | _ -> false

let hash_combine h h' = h + 17 * h'
let hash_list l = List.fold_left (fun h x -> hash_combine x.hash h) 0 l

let hash ht =
  let h =
    match ht with
    | Elm (s, n, xs, ys) -> hash_combine (Label.hash s) (Hashtbl.hash n)
    | Attrep (s, n, xs) -> hash_combine (Label.hash s) (Hashtbl.hash n)
    | Alt l -> hash_combine 1 (hash_list l)
    | Seq l -> hash_combine 2 (hash_list l)
    | Rep ht' -> ht'.hash 
    | Exe (i, ht') -> hash_combine i ht'.hash in
  h land 0x3FFFFFFF

let comp ht1 ht2 =
  if ht1 == ht2 then 0 else
  if ht1.hash < ht2.hash then -1 else
  if ht1.hash > ht2.hash then 1 else
  compare ht1 ht2

module Tbl =
  Hashtbl.Make (struct type t = ht let equal = equal let hash ht = ht.hash end)

let hashcons_cache : ht Tbl.t = Tbl.create 121

let cons x = 
  let ht = 
    { hash = hash x; def = x; 
      adom = Label.empty; ldom = Label.empty;
      rvars1 = None; rvars2 = None } in
  try
    Tbl.find hashcons_cache ht
  with Not_found ->
    ht.adom <-
      (match x with
      | Elm _ | Rep _ -> Label.empty
      |	Exe (i, ht') -> ht'.adom 
      | Attrep (c, _, _) -> c
      | Alt htl 
      | Seq htl -> Label.union_many (List.map (fun ht -> ht.adom) htl));
    ht.ldom <-
      (match x with
      | Elm (c, _, _, _) -> c
      | Rep ht' -> ht'.ldom
      | Attrep _ -> Label.empty
      |	Exe (i, ht') -> ht'.ldom 
      | Alt htl 
      | Seq htl -> Label.union_many (List.map (fun ht -> ht.ldom) htl));
    Tbl.add hashcons_cache ht ht;
    ht

(* Binding of pattern names to patterns *)

let binding : (string, ht) Hashtbl.t = Hashtbl.create 101
let rev_table : (ht, string) Hashtbl.t = Hashtbl.create 101

let lookup_name n = Hashtbl.find binding n

let define_name n ht = 
  Counter.incr ctr_define_name;
  Hashtbl.add rev_table ht n;
  Hashtbl.add binding n ht

let give_unique_name ht =
  try Hashtbl.find rev_table ht 
  with Not_found ->
    let n = Syn.new_name() in
    Hashtbl.add rev_table ht n;
    Hashtbl.add binding n ht;
    n

let redefine_name n ht =
  Hashtbl.remove binding n;
  define_name n ht

(* constructors *)

let epsilon = cons (Seq [])
let empty = cons (Alt [])

let alt_merge = Sortedlist.merge comp
let rec alt2 ht1 ht2 =
  let c = comp ht1 ht2 in
  if c = 0 then ht1 else
  match ht1.def, ht2.def with
    Alt [], _ -> ht2
  | _, Alt [] -> ht1
  | Alt r, Alt s -> cons (Alt (alt_merge r s))
  | Alt [r], _ when r == ht2 -> ht2
  | _, Alt [s] when ht1 == s -> ht1
  | Alt r, _ -> cons (Alt (alt_merge r [ht2]))
  | _, Alt s -> cons (Alt (alt_merge [ht1] s))
  | _ -> cons (if c < 0 then Alt [ht1; ht2] else Alt [ht2; ht1])

let alt l = List.fold_right alt2 l empty

let seq2 ht1 ht2 =
  match ht1.def, ht2.def with
    Alt [], _ | _, Alt [] -> empty
  | Seq [], _ -> ht2
  | _, Seq [] -> ht1
  | Seq r, Seq s -> cons (Seq (r @ s))
  | Seq r, _ -> cons (Seq (r @ [ht2]))
  | _, Seq s -> cons (Seq (ht1 :: s))
  | _ -> cons (Seq [ht1; ht2])

let seq l = List.fold_right (fun ht1 ht2 -> seq2 ht1 ht2) l epsilon

let attrep s n xs = cons (Attrep (s, n, xs))
let elm s n xs ys = 
  if Label.is_empty s then empty else cons (Elm (s, n, xs, ys))

let rep ht = 
  if ht == empty || ht == epsilon then epsilon else cons (Rep ht)
	
let empty_name = give_unique_name empty
let epsilon_name = give_unique_name epsilon

let string = elm (Label.base Base.BTString) epsilon_name [] []
let int = elm (Label.base Base.BTInt) epsilon_name [] []
let float = elm (Label.base Base.BTFloat) epsilon_name [] []
let single b xs ys = elm (Label.single b) epsilon_name xs ys
let base b xs ys = elm (Label.base b) epsilon_name xs ys

let exe i ht = cons (Exe (i, ht))

let string_rep_name = give_unique_name (rep string)

let any_name = Syn.new_name ()
let any_elm =
  alt [elm Label.any_label any_name [] []; string; int; float]
let any = 
  seq [alt [attrep Label.any_label string_rep_name []; epsilon]; 
       rep any_elm]
let _ = define_name any_name any

(* testers *)

let rec nullable ht =
  match ht.def with
  | Elm _ -> false
  | Rep _ -> true
  | Attrep _ -> false
  | Alt htl -> List.exists nullable htl
  | Seq htl -> List.for_all nullable htl
  | Exe (_, ht') -> nullable ht'

let nullable ht = Timer.wrap  tm_nullable (fun () -> nullable ht)

module Ht = 
  struct
    type t = ht 
    let compare = comp 
  end

module HtSet = Set.Make(Ht)

let empty_tbl = ref HtSet.empty
let non_empty_tbl = ref HtSet.empty

let rec is_empty' ht =
  match ht.def with
  | Elm (c, n, _, _) -> Label.is_empty c || is_empty (lookup_name n)
  | Rep ht -> false
  | Attrep (c, n, _) -> Label.is_empty c || is_empty (lookup_name n)
  | Alt htl -> List.for_all is_empty htl
  | Seq htl -> List.exists is_empty htl
  | Exe (_, ht') -> is_empty ht'

and is_empty ht =
  if HtSet.mem ht !empty_tbl then true 
  else if HtSet.mem ht !non_empty_tbl then false else begin
    let tbl' = !empty_tbl in
    empty_tbl := HtSet.add ht !empty_tbl;
    if is_empty' ht then true else
    begin
      empty_tbl := tbl';
      non_empty_tbl := HtSet.add ht !non_empty_tbl;
      false 
    end 
  end

let is_empty ht = Timer.wrap  tm_is_empty (fun () -> is_empty ht)

let is_obviously_empty ht = ht == empty

let is_att_free ht = Label.is_empty ht.adom

let rec rvars1 asm ht =
  match ht.rvars1 with
  | Some xs -> xs
  | None ->
      match ht.def with
      | Elm (c, n, xs, _) | Attrep (c, n, xs) -> 
	  Sortedlist.merge compare xs
	    (if List.memq n !asm then [] else 
	    begin
	      asm := n :: !asm;
	      rvars1 asm (lookup_name n)
	    end)
      | Rep ht' | Exe (_, ht') -> rvars1 asm ht' 
      | Alt htl | Seq htl -> 
	  Sortedlist.merge_many compare (List.map (rvars1 asm) htl)
      
let reachable_vars1 ht =
  match ht.rvars1 with
  | Some xs -> xs
  | None ->
      let xs = rvars1 (ref []) ht in
      ht.rvars1 <- Some xs;
      xs

let reachable_vars1 ht = 
  Timer.wrap tm_reachable_vars (fun () -> reachable_vars1 ht)

let rec rvars2 asm ht =
  match ht.rvars2 with
  | Some xs -> xs
  | None ->
      match ht.def with
      | Elm (c, n, _, ys) ->
	  Sortedlist.merge compare ys
	    (if List.memq n !asm then [] else 
	    begin
	      asm := n :: !asm;
	      rvars2 asm (lookup_name n)
	    end)
      | Attrep (_, n, _) -> rvars2 asm (lookup_name n)
      | Rep ht' | Exe (_, ht') -> rvars2 asm ht' 
      | Alt htl | Seq htl -> 
	  Sortedlist.merge_many compare (List.map (rvars2 asm) htl)
      

let reachable_vars2 ht =
  match ht.rvars2 with
  | Some xs -> xs
  | None ->
      let xs = rvars2 (ref []) ht in
      ht.rvars2 <- Some xs;
      xs

let rec reachable_exe_ids asm ht =
  match ht.def with
  | Elm (c, n, _, _) | Attrep (c, n, _) -> 
      if List.memq n !asm then [] else 
      begin
	asm := n :: !asm;
	reachable_exe_ids asm (lookup_name n)
      end
  | Rep ht -> reachable_exe_ids asm ht
  | Alt htl | Seq htl -> 
      Sortedlist.merge_many compare (List.map (reachable_exe_ids asm) htl)
  | Exe (i, ht') -> i :: reachable_exe_ids asm ht'

let reachable_exe_ids ht = reachable_exe_ids (ref []) ht

(* empty type elimination *)

let elim_empty_asm = ref Setutil.StringSet.empty

let rec elim_empty ht =
  match ht.def with
  | Elm (c, n, _, _) 
  | Attrep (c, n, _) -> 
      let b = elim_empty_top n in
      if Label.is_empty c || b then empty else ht
  | Rep ht' -> 
      let ht'' = elim_empty ht' in
      if is_obviously_empty ht'' || ht'' == epsilon then epsilon else 
      if ht' == ht'' then ht else 
      rep ht''
  | Alt htl -> 
      let htl' = List.map elim_empty htl in
      let htl' = List.filter (fun ht -> not(is_obviously_empty ht)) htl' in
      if Listutil.same_list htl htl' then ht else
      alt htl'
  | Seq htl -> 
      let htl' = List.map elim_empty htl in
      if List.exists is_obviously_empty htl' then empty else 
      if Listutil.same_list htl htl' then ht else
      seq htl'
  | Exe (i, ht') ->
      let ht'' = elim_empty ht' in
      if is_obviously_empty ht'' then empty else
      if ht' == ht'' then ht else
      exe i ht''

and elim_empty_top n =
  let ht = lookup_name n in
  let b = is_empty ht in
  if Setutil.StringSet.mem n !elim_empty_asm then b else begin
    elim_empty_asm := Setutil.StringSet.add n !elim_empty_asm;
    let ht' = elim_empty ht in
    if ht != ht' then redefine_name n ht';
    b
  end

let elim_empty ht = Timer.wrap tm_elim_empty (fun () -> elim_empty ht)

(* generating a sample value from a type *)

open Syn

let rec sample asm ht =
  match ht.def with
  | Elm (c, n, _, _) -> 
      if Label.is_empty c then raise Not_found else
      let p, l = Label.sample c in
      if Sym.rank l = 2 then [MLab (p, l, sample_top asm n)] else
      let Some b = Sym.baseval l in
      [MBase b]
  | Attrep (c, n, _) ->
      if Label.is_empty c then raise Not_found else
      let p, l = Label.sample c in
      [MAtt (p, l, sample_top asm n)] 
  | Alt [] -> 
      raise Not_found
  | Alt (ht :: htl) ->
      begin
	try sample asm ht
	with Not_found ->
	  sample asm (alt htl)
      end
  | Seq htl -> 
      Listutil.mapcat (sample asm) htl
  | Rep _ 
  | Exe _ ->
      []


and sample_top asm n =
  if List.mem n asm then raise Not_found else
  sample (n :: asm) (lookup_name n)

let sample ht = sample [] ht

(* size *)

let rec size ns s ht =
  incr s;
  match ht.def with
  | Elm (c, n, _, _) 
  | Attrep (c, n, _) ->
      if Setutil.StringSet.mem n !ns then () else
      begin 
	ns := Setutil.StringSet.add n !ns;
	size ns s (lookup_name n)
      end
  | Alt hts 
  | Seq hts -> 
      List.iter (size ns s) hts
  | Rep ht' 
  | Exe (_, ht') ->
      size ns s ht'

let size ht =
  let ns = ref (Setutil.StringSet.empty) in
  let s = ref 0 in
  size ns s ht;
  !s

(* printers *)

let rec print p ch ht =
  match ht.def with
  | Elm (s, n, xs, ys) ->
      fprintf ch "@[<2>(%a%a%a@ @[<1>[%s]@])@]"
        print_vars xs print_vars ys Label.print s n
  | Attrep (s, n, xs) ->
      fprintf ch "@[<2>(%a@@%a@ @[<1>[%s]+@])@]"
        print_vars xs Label.print s n
  | Alt [] ->
      fprintf ch "None"
  | Alt l ->
      fprintf ch "@[<1>(";
      Printing.print_list (fun () -> fprintf ch "@ |@ ") (print 1 ch) l;
      fprintf ch ")@]" 
  | Seq l ->
      fprintf ch "@[<1>(";
      Printing.print_list (fun () -> fprintf ch ",@ ") (print 3 ch) l;
      fprintf ch ")@]" 
  | Rep ht ->
      fprintf ch "@[<2>(@[<1>%a@])*@]" (print 0) ht
  | Exe (i, ht) ->
      fprintf ch "%a@ -> %d" (print 0) ht i

and print_vars ch xv =
  match xv with
  | [] -> fprintf ch ""
  | var :: xv -> fprintf ch "%s:%a" var print_vars xv

let print ch x = fprintf ch "@[%a@]" (print 0) x

let print_binding ch () =
  Hashtbl.iter
    (fun x ht -> fprintf ch "type %s = %a@." x print ht)
    binding

