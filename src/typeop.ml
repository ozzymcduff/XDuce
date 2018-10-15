open Htype
open Format

let tm_isect = Timer.create "typeop:isect"
let tm_diff = Timer.create "typeop:diff"
let tm_subst = Timer.create "typeop:subst"
let tm_extract = Timer.create "typeop:extract"
let tm_partition = Timer.create "typeop:partition"
let tm_recov = Timer.create "typeop:recovery"
let tm_construct = Timer.create "typeop:construct"
let tm_shred = Timer.create "typeop:shred"
let tm_att_normalize = Timer.create "typeop:att_normalize"
let ctr_isect_htseq = Counter.create "isect_htseq"
let ctr_subst_htseq = Counter.create "subst_htseq"
let ctr_diff_htseq = Counter.create "diff_htseq"
let ctr_diff_htseq_nondet = Counter.create "diff_htseq_nondet"
let ctr_diff_nondet = Counter.create "diff_nondet"
let tm_tmp = Timer.create "typeop:tmp"


let debug_wrap_level = ref 0
let debug_wrap pin pout f =
  printf "[%d]<= @?" (!debug_wrap_level);
  pin ();
  incr debug_wrap_level;
  let o = f() in
  decr debug_wrap_level;
  printf "[%d]=> @?" (!debug_wrap_level);
  pout o;
  o

(* ATTRIBUTE NORMALIZATION: Transform a given type so that, for each
   pair of attributes, the label classes of these attributes are
   either disjoint or equivalent *)

let rec collect_att_labels ht set =
  match ht.Htype.def with
  | Elm _ | Rep _ -> ()
  | Attrep (c, _, _) -> set := Sortedlist.merge Label.compare [c] !set
  | Alt htl -> List.iter (fun ht -> collect_att_labels ht set) htl
  | Seq htl -> List.iter (fun ht -> collect_att_labels ht set) htl
  | Exe (i, ht') -> collect_att_labels ht' set
  

let rec shred_labels l =
  match l with
  | [] | [_] -> 
      l
  | c :: l ->
      if List.for_all (fun d -> Label.disjoint c d) l then
	Sortedlist.merge Label.compare [c] (shred_labels l)
      else
	let shreded1 = [Label.diff c (Label.union_many l)] in
	let shreded2 =
	  shred_labels 
	    (Listutil.union_many (Sortedlist.merge Label.compare)
	       (List.map (fun d -> [Label.inter c d]) l)) in
	let shreded3 =
	  shred_labels 
	    (Listutil.union_many (Sortedlist.merge Label.compare)
	       (List.map (fun d -> [Label.diff d c]) l)) in
	Sortedlist.merge Label.compare
	  (Sortedlist.merge Label.compare shreded1 shreded2) shreded3
	  
let shred_labels l = Timer.wrap tm_shred (fun () -> shred_labels l)

let rec attnorm ht ds =
  match ht.def with
  | Elm _ | Rep _ -> 
      ht
  | Attrep (c, n, vs) -> 
      let cs = List.filter (fun d -> Label.overlapping c d) ds in
      attnorm_attrep1 cs n vs
  | Alt htl -> 
      if List.exists Htype.nullable htl then
	Htype.alt (List.map (fun ht -> attnorm_nullable ht ds) htl)
      else
	Htype.alt (List.map (fun ht -> attnorm ht ds) htl)
  | Seq htl -> 
      Htype.seq (List.map (fun ht -> attnorm ht ds) htl)
  | Exe (i, ht') ->
      Htype.exe i (attnorm ht' ds)

and attnorm_nullable ht ds =
  match ht.def with
  | Elm _ | Rep _ -> 
      ht
  | Attrep (c, n, vs) -> 
      let cs = List.filter (fun d -> Label.overlapping c d) ds in
      attnorm_attrep0 cs n vs
  | Alt htl -> 
      Htype.alt (List.map (fun ht -> attnorm_nullable ht ds) htl)
  | Seq [] ->
      Htype.epsilon
  | Seq [ht'] -> 
      attnorm_nullable ht' ds
  | Seq _ ->
      attnorm ht ds
  | Exe (i, ht') ->
      Htype.exe i (attnorm_nullable ht' ds)

and attnorm_attrep0 cs n vs =
  Htype.seq 
    (List.map (fun c -> Htype.alt [Htype.epsilon; Htype.attrep c n vs]) cs)

and attnorm_attrep1 cs n vs =
  match cs with
  | [] -> Htype.empty
  | [c] -> Htype.attrep c n vs
  | c :: cs -> 
      Htype.alt [Htype.attrep c n vs;
		 Htype.seq [Htype.alt [Htype.attrep c n vs; Htype.epsilon]; 
			    attnorm_attrep1 cs n vs]]

let att_normalize htl =
  if !Pref.typinglog then Format.printf "@[<2>att normalize...@?";
  Timer.start tm_att_normalize;
  let set = ref [] in
  List.iter (fun ht -> collect_att_labels ht set) htl;
  let ds = shred_labels !set in
  let htl' = List.map (fun ht -> attnorm ht ds) htl in
  Timer.stop tm_att_normalize;
  if !Pref.typinglog then Format.printf "done@]@.";
  htl'

(* AUTOMATA *)

type null_annot = [`Begin of int | `End ]

type state =
    { id : int;
      mutable final : bool;
      mutable next : ((Label.t * string * string list * string list) * state) list;
      mutable desc : Htype.ht option;
      mutable var_free : bool option;
      mutable empty : bool option;
      mutable null : (null_annot * state) list;
      mutable attrep : ((Label.t * string * string list) * state) list;
    } 

let last_id = ref 0

let create_state final next desc =
  incr last_id;
  { id = !last_id; 
    final = final;
    next = next;
    desc = desc;
    var_free = None;
    empty = None;
    null = [];
    attrep = [];
  }

let empty_state = create_state false [] None 

let state_is_obviously_empty x =
  not x.final && x.next = [] && x.null = []

let compare_state x1 x2 = compare x1.id x2.id

let union_trans l1 l2 = l1 @ l2

let state_set_next xs = 
  Listutil.union_many union_trans (List.map (fun x -> x.next) xs)
let state_set_final s = List.exists (fun x -> x.final) s

let mem_state_sets = Sortedlist.mem compare_state
let compare_state_sets = Sortedlist.compare compare_state
let union_state_sets = Sortedlist.merge compare_state
let diff_state_sets = Sortedlist.diff compare_state

let rec hashl xs =
  match xs with
    [] -> 0
  | x :: xs' -> x.id + 239 * hashl xs'

let hash_state_states x xs = (x.id + 17 * hashl xs) land 0x3FFFFFFF

module State =
  struct
    type t = state
    let compare = compare_state
  end

module StateSet = Set.Make(State)
module StateMap = Map.Make(State)

module StatePair = Setutil.MakePair(State)(State)
module StatePairSet = Set.Make(StatePair)
module StatePairMap = Map.Make(StatePair)

module StateStates = Setutil.MakePair(State)(Setutil.MakeSortedlist(State))
module StateStatesSet = Set.Make(StateStates)
module StateStatesMap = Map.Make(StateStates)
 
module VarsStateStates = Setutil.MakeTuple3(Setutil.MakeSortedlist(Setutil.String))(State)(Setutil.MakeSortedlist(State))
module VarsStateStatesSet = Set.Make(VarsStateStates)
module VarsStateStatesMap = Map.Make(VarsStateStates)
 
module StringPair = Setutil.MakePair(Setutil.String)(Setutil.String)
module StringPairSet = Set.Make(StringPair)
module StringPairMap = Map.Make(StringPair)

module StringStrings = Setutil.MakePair(Setutil.String)(Setutil.MakeSortedlist(Setutil.String))
module StringStringsSet = Set.Make(StringStrings)
module StringStringsMap = Map.Make(StringStrings)
 
module VarsStringStrings = Setutil.MakeTuple3(Setutil.MakeSortedlist(Setutil.String))(Setutil.String)(Setutil.MakeSortedlist(Setutil.String))
module VarsStringStringsSet = Set.Make(VarsStringStrings)
module VarsStringStringsMap = Map.Make(VarsStringStrings)
 
let rec compare_htseq l m =
  match l, m with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: l, y :: m -> 
      let c = Htype.comp x y in
      if c <> 0 then c else
      compare_htseq l m

let mem_htseqalt = Sortedlist.mem compare_htseq
let compare_htseqalt = Sortedlist.compare compare_htseq
let union_htseqalt = Sortedlist.merge compare_htseq
let diff_htseqalt = Sortedlist.diff compare_htseq

module Htseq =
  struct
    type t = Htype.ht list
    let compare = compare_htseq
  end

module HtseqSet = Set.Make(Htseq)
module HtseqMap = Map.Make(Htseq)

module HtseqPair = Setutil.MakePair(Htseq)(Htseq)
module HtseqPairSet = Set.Make(HtseqPair)
module HtseqPairMap = Map.Make(HtseqPair)

module HtseqHtseqs = Setutil.MakePair(Htseq)(Setutil.MakeSortedlist(Htseq))
module HtseqHtseqsSet = Set.Make(HtseqHtseqs)
module HtseqHtseqsMap = Map.Make(HtseqHtseqs)
 
module VarsHtseqHtseqs = Setutil.MakeTuple3(Setutil.MakeSortedlist(Setutil.String))(Htseq)(Setutil.MakeSortedlist(Htseq))
module VarsHtseqHtseqsSet = Set.Make(VarsHtseqHtseqs)
module VarsHtseqHtseqsMap = Map.Make(VarsHtseqHtseqs)
 
let rec null_closure' asm s =
  if not(List.memq s !asm) then begin
    asm := s :: !asm;
    List.iter (fun (_, s') -> null_closure' asm s') s.null
  end

let null_closure s = 
  let asm = ref [] in
  null_closure' asm s;
  !asm

let state_set_null_closure ss =
  let asm = ref [] in
  List.iter (fun s -> null_closure' asm s) ss;
  !asm

let state_empty_tbl = ref StateSet.empty
let state_non_empty_tbl = ref StateSet.empty

let rec state_is_empty s =
  if StateSet.mem s !state_empty_tbl then true 
  else if StateSet.mem s !state_non_empty_tbl then false else begin
    let tbl' = !state_empty_tbl in
    state_empty_tbl := StateSet.add s !state_empty_tbl;
    if (not s.final && 
	List.for_all
	  (fun ((c, s1, _, _), s2) ->
	    Label.is_empty c || Htype.is_empty (Htype.lookup_name s1) || 
	    state_is_empty s2)
	  s.next &&
	List.for_all
	  (fun ((c, s1, _), s2) ->
	    Label.is_empty c || Htype.is_empty (Htype.lookup_name s1) || 
	    state_is_empty s2)
	  s.attrep &&
	List.for_all (fun (_, s2) -> state_is_empty s2) s.null)
    then true else begin
      state_empty_tbl := tbl';
      state_non_empty_tbl := StateSet.add s !state_non_empty_tbl;
      false
    end
  end

let rec state_var_free asm s =
  if StateSet.mem s !asm then true else begin
    asm := StateSet.add s !asm;
    match s.var_free with
    | Some b -> b
    | None ->
	List.for_all 
	  (fun ((_, _, xs, ys), s2) -> xs = [] && ys = [] && state_var_free asm s2) 
	  s.next &&
	List.for_all
	  (fun ((_, _, xs), s2) -> xs = [] && state_var_free asm s2)
	  s.attrep &&
	List.for_all (fun (_, s2) -> state_var_free asm s2) s.null 
  end

let state_var_free s =
  let b = state_var_free (ref StateSet.empty) s in
  s.var_free <- Some b;
  b

(* AUTOMATA CONSTRUCTION *)

let rec construct asm htl =
  try HtseqMap.find htl !asm
  with Not_found ->
    let s = create_state false [] (Some (Htype.seq htl)) in
    asm := HtseqMap.add htl s !asm;
    construct' asm (ref HtseqSet.empty) htl s;
    s

and construct' asm asm' htl s =
  if not(HtseqSet.mem htl !asm') then begin
    asm' := HtseqSet.add htl !asm';
    match htl with
    | [] -> 
	s.final <- true
    | ht :: rest ->
	match ht.def with
	| Elm (c, n, xs, ys) -> 
	    let s' = construct asm rest in
	    s.next <- ((c, n, xs, ys), s') :: s.next
	| Rep ht' ->
	    construct' asm asm' rest s;
	    construct' asm asm' ([ht'; ht] @ rest) s
	| Attrep (c, n, xs) ->
	    let s' = construct asm rest in
	    s.attrep <- ((c, n, xs), s') :: s.attrep
	| Alt htl' -> 
	    List.iter (fun ht' -> construct' asm asm' (ht' :: rest) s) htl'
	| Seq htl' ->
	    construct' asm asm' (htl' @ rest) s
	| Exe (i, ht') ->
	    if i == -1 then 
	      let s' = construct asm rest in
	      s.null <- (`End, s') :: s.null
	    else
	      let s' = construct asm (ht' :: Htype.exe (-1) Htype.epsilon :: rest) in
	      s.null <- (`Begin i, s') :: s.null
  end

let construct ht = construct (ref HtseqMap.empty) [ht]

let construct ht = Timer.wrap tm_construct (fun () -> construct ht)

let any_state = construct Htype.any

(* recovery *)

type ht_automaton = 
  {
    mutable states : int list;
    trans : (int * int, Htype.ht) Hashtbl.t;
    mutable init_states : int list;
    mutable fin_states : int list;
    null_trans : (int * int, null_annot) Hashtbl.t;
  }

let create_empty_ht_automaton() =
  { 
    states = []; trans = Hashtbl.create 121; 
    init_states = []; fin_states = [];
    null_trans = Hashtbl.create 121;
  }

let print_ht_automaton m =
  printf "init: ";
  List.iter (fun q -> printf "%d " q) m.init_states;
  printf "@.fin: ";
  List.iter (fun q -> printf "%d " q) m.fin_states;
  printf "@.states: ";
  List.iter (fun q -> printf "%d " q) m.states;
  printf "@.";
  Hashtbl.iter
    (fun (p, q) ht ->
      printf "%d -- %a -> %d @." p Htype.print ht q)
    m.trans;
  Hashtbl.iter
    (fun (p, q) a ->
      match a with
      | `Begin i ->
	  printf "%d -- B%d -> %d @." p i q
      | `End ->
	  printf "%d -- E -> %d @." p q)
    m.null_trans

let get_ht_trans (p, q) m =
  try 
    Hashtbl.find m.trans (p, q)
  with Not_found ->
    if p == q then Htype.epsilon else
    Htype.empty

let add_ht_trans (p, q) ht m =
  try
    let ht' = Hashtbl.find m.trans (p, q) in
    Hashtbl.replace m.trans (p, q) (Htype.alt [ht; ht']) 
  with Not_found ->
    Hashtbl.add m.trans (p, q) ht 

let get_from q m =
  Hashtbl.fold
    (fun (p', q') _ qs -> 
      if q != q' then qs else
      Sortedlist.merge compare [p'] qs)
    m.trans []

let get_to q m =
  Hashtbl.fold
    (fun (p', q') _ qs -> 
      if q != p' then qs else
      Sortedlist.merge compare [q'] qs)
    m.trans []

let remove_state q m =
  m.states <- Sortedlist.diff compare m.states [q];
  m.init_states <- Sortedlist.diff compare m.init_states [q];
  m.fin_states <- Sortedlist.diff compare m.fin_states [q];
  let pairs = 
    Hashtbl.fold
      (fun (p', q') _ pairs -> if p' == q || q' == q then (p', q') :: pairs else pairs)
      m.trans [] in
  List.iter (fun pair -> Hashtbl.remove m.trans pair) pairs

let add_new_state m =
  incr last_id;
  let p = !last_id in
  m.states <- Sortedlist.merge compare [p] m.states;
  p

let rec fill_ht_automaton asm s m =
  if not(StateSet.mem s !asm) then begin
    asm := StateSet.add s !asm;
    m.states <- Sortedlist.merge compare [s.id] m.states;
    if s.final then m.fin_states <- Sortedlist.merge compare [s.id] m.fin_states;
    List.iter 
      (fun ((c, n, xs, ys), s2) ->
	add_ht_trans (s.id, s2.id) (Htype.elm c n xs ys) m;
	fill_ht_automaton asm s2 m)
      s.next;
    List.iter 
      (fun ((c, n, xs), s2) ->
	add_ht_trans (s.id, s2.id) (Htype.attrep c n xs) m;
	fill_ht_automaton asm s2 m)
      s.attrep;
    List.iter
      (fun (a, s2) ->
	match a with
	| `End 
	| `Begin _ ->
	    let p' = add_new_state m in
	    let q' = add_new_state m in
	    Hashtbl.add m.null_trans (p', q') a;
	    add_ht_trans (s.id, p') Htype.epsilon m;
	    add_ht_trans (q', s2.id) Htype.epsilon m;
	    fill_ht_automaton asm s2 m)
      s.null
  end
    
let fill_ht_automaton s m = 
  m.init_states <- [s.id];
  fill_ht_automaton (ref StateSet.empty) s m

let add_source_sink m =
  let src = add_new_state m in
  let snk = add_new_state m in
  List.iter (fun q -> add_ht_trans (src, q) Htype.epsilon m) m.init_states;
  List.iter (fun q -> add_ht_trans (q, snk) Htype.epsilon m) m.fin_states;
  m.init_states <- [src];
  m.fin_states <- [snk];
  src, snk

let get_noncritical_states m =
  let qs = Sortedlist.diff compare m.states m.init_states in
  let qs = Sortedlist.diff compare qs m.fin_states in
  let qs = 
    Hashtbl.fold
      (fun (p, q) _ qs ->
	Sortedlist.diff compare 
	  (Sortedlist.diff compare qs [p]) [q]) 
      m.null_trans qs in
  qs

let eliminate_state q m =
  let fs = Sortedlist.diff compare (get_from q m) [q] in
  let ts = Sortedlist.diff compare (get_to q m) [q] in
  List.iter
    (fun f ->
      List.iter 
	(fun t ->
	  add_ht_trans (f, t) 
	    (Htype.seq 
	       [get_ht_trans (f, q) m;
		Htype.rep (get_ht_trans (q, q) m);
		get_ht_trans (q, t) m])
	    m)
	ts)
    fs;
  remove_state q m

let eliminate_states qs m =
  let tups = List.map (fun q -> (q, get_from q m, get_to q m)) qs in
  let tups = 
    List.sort 
      (fun (q, fs, ts) (q', fs', ts') -> 
	compare (List.length fs * List.length ts) (List.length fs' * List.length ts')) tups in
  List.iter (fun (q, _, _) -> eliminate_state q m) tups

let eliminate_null_trans m =
  Hashtbl.iter
    (fun (p1, q1) a1 ->
      match a1 with
      | `End -> ()
      | `Begin i ->
	  Hashtbl.iter
	    (fun (p2, q2) a2 ->
	      match a2 with
	      | `Begin _ -> ()
	      | `End ->
		  add_ht_trans (p1, q2) 
		    (Htype.exe i (get_ht_trans (q1, p2) m)) m)
	    m.null_trans)
    m.null_trans;
  Hashtbl.clear m.null_trans

let recov s =
  let m = create_empty_ht_automaton() in
  fill_ht_automaton s m;
  if !Pref.typinglog then print_ht_automaton m;
  let src, sink = add_source_sink m in
  if !Pref.typinglog then print_ht_automaton m;
  let ss = get_noncritical_states m in
  eliminate_states (get_noncritical_states m) m;
  if !Pref.typinglog then print_ht_automaton m;
  eliminate_null_trans m;
  if !Pref.typinglog then print_ht_automaton m;
  eliminate_states (get_noncritical_states m) m;
  if !Pref.typinglog then print_ht_automaton m;
  get_ht_trans (src, sink) m

let recov s = Timer.wrap tm_recov (fun () -> recov s)

(* AUXILIARIES *)

let rec flatten_htseq1 ht =
  match ht.def with
  | Elm _
  | Rep _ 
  | Attrep _ 
  | Exe _
  | Alt _ -> [ht]
  | Seq htl -> flatten_htseq htl

and flatten_htseq htl = Listutil.mapcat flatten_htseq1 htl

let rec flatten_htseqalt1 htl =
  match htl with
  | [{ def = Alt htl }] -> 
      flatten_htseqalt (List.map (fun ht -> [ht]) htl)
  | _ -> [flatten_htseq htl]
  
and flatten_htseqalt htls = 
  Listutil.union_many union_htseqalt 
    (List.map flatten_htseqalt1 htls)

let rec combine_non_label_free l non_label_free =
  match l with
  | [] -> 
      if non_label_free = [] then [] else [Htype.seq (List.rev non_label_free)]
  | ht :: l' -> 
      if Label.is_empty ht.ldom then
	ht :: combine_non_label_free l' non_label_free
      else
	combine_non_label_free l' (ht :: non_label_free)

let rec expand_htseq l =
  match l with
    [] ->
      [[]]
  | ht :: l' ->
      match ht.def with
      | Elm _
      | Rep _ 
      |	Exe _
      | Attrep _ -> List.map (fun l'' -> ht :: l'') (expand_htseq l')
      | Alt l'' -> List.map (fun ht' -> ht' :: l') l''
      | Seq htl -> assert false

let rec restrict_att d ht =
  if Label.subset ht.adom d then ht else
  match ht.def with
  | Elm _ 
  | Rep _ -> ht
  | Attrep (c, n, _) -> Htype.empty
  | Alt htl -> Htype.alt (List.map (restrict_att d) htl)
  | Seq htl -> Htype.seq (List.map (restrict_att d) htl)
  | Exe (i, ht') -> Htype.exe i (restrict_att d ht')

let rec restrict_lab d ht =
  if Label.subset ht.ldom d then ht else
  match ht.def with
  | Elm (c, n, xs, ys) -> Htype.elm (Label.inter c d) n xs ys
  | Rep ht -> Htype.rep (restrict_lab d ht)
  | Attrep _ -> ht
  | Alt htl -> Htype.alt (List.map (restrict_lab d) htl)
  | Seq htl -> Htype.seq (List.map (restrict_lab d) htl)
  | Exe (i, ht') -> Htype.exe i (restrict_lab d ht')

let rec partition_htseq partns adom ldom =
  if Label.is_empty adom && Label.is_empty ldom then partns else
  let partns' = 
    List.map
      (fun (_, res) ->
	List.partition
	  (fun ht -> 
	    Label.overlapping ht.adom adom || Label.overlapping ht.ldom ldom)
	  res)
      partns in
  if List.for_all (fun (fac, _) -> fac = []) partns' then partns else
  let adom' = 
    Label.union_many
      (adom ::
       Listutil.mapcat (fun (fac, _) -> List.map (fun ht -> ht.adom) fac) 
	 partns') in
  let ldom' = 
    Label.union_many
      (ldom ::
       Listutil.mapcat (fun (fac, _) -> List.map (fun ht -> ht.ldom) fac) 
	 partns') in
  let partns'' = 
    List.map2 (fun (fac, _) (fac', res') -> (fac @ fac', res')) 
      partns partns' in
  partition_htseq partns'' adom' ldom'

let partition_htseq htls = 
  let htls = List.map (fun l -> combine_non_label_free l []) htls in
  let ht :: _ = 
	   List.find (function (ht :: _) -> not (Label.is_empty ht.adom) | _ -> false) htls in 
  let partns =
    partition_htseq 
      (List.map (fun htl -> ([], htl)) htls) ht.adom ht.ldom in
  if List.for_all (fun (f, r) -> r = []) partns then None else
  Some partns

let partition_htseq htls = Timer.wrap tm_partition (fun () -> partition_htseq htls)

let htseq_is_obviously_empty l = List.exists Htype.is_obviously_empty l
let htseq_is_empty l = List.exists Htype.is_empty l
let htseq_is_att_free l = List.for_all Htype.is_att_free l
let htseq_nullable l = List.for_all Htype.nullable l
let htseq_is_flat l = 
  List.for_all (function { def = Attrep _ } -> true | _ -> false) l
let htseq_singleton_content c1 l =
  match l with 
  | [{ def = Attrep (c2, n, vs) }] when Label.equal c1 c2 -> [(n, vs)]
  | _ -> []
let htseq_adom htl = 
  Label.union_many (List.map (fun ht -> ht.adom) htl)
let htseq_ldom htl = 
  Label.union_many (List.map (fun ht -> ht.ldom) htl)
let htseqalt_singleton_content c1 ms =
  Listutil.union_many (Sortedlist.merge compare)
    (List.map (htseq_singleton_content c1) ms)

let rec ht_contains_exe ht =
  match ht.def with
  | Exe _ -> true
  | Attrep _ | Elm _ -> false
  | Rep ht' -> ht_contains_exe ht'
  | Alt htl | Seq htl -> htseq_contains_exe htl

and htseq_contains_exe htseq = List.exists ht_contains_exe htseq

let rec drop_exe ht =
  match ht.def with
  | Exe (i, ht') -> drop_exe ht'
  | Attrep _ | Elm _ -> ht
  | Rep ht' -> Htype.rep (drop_exe ht')
  | Alt htl -> Htype.alt (List.map drop_exe htl)
  | Seq htl -> Htype.seq (List.map drop_exe htl)

let drop_exe ht = if ht_contains_exe ht then drop_exe ht else ht

(* INTERSECTION: when applied to X and Y, preserves the variables and
   the null-transitions in X. 

   either
   + X is a pattern and Y is a type, or
   + both X and Y are types

   Assumptions: 
   + the variables in X and Y are disjoint
*)

let isect_asm_state = ref StatePairMap.empty
let isect_asm_name = ref StringPairMap.empty
let isect_asm_htype = ref HtseqPairMap.empty

let obviously_subtype s1 s2 =
  state_is_obviously_empty s1 || s2 == any_state || s1 == s2

let rec isect_state comb_vars s1 s2 =
  if obviously_subtype s2 s1 && state_var_free s1 then s2 else
  if obviously_subtype s1 s2 && state_var_free s2 then s1 else
  try StatePairMap.find (s1, s2) !isect_asm_state
  with Not_found ->
    let ss = null_closure s2 in
    let s3 = create_state (s1.final && state_set_final ss) [] None in
    isect_asm_state := StatePairMap.add (s1, s2) s3 !isect_asm_state;
    s3.next <-
      Listutil.mapcat
	(fun ((c1, ht1, xs1, ys1), s1') ->
	  Listutil.mapcat
	    (fun ((c2, ht2, xs2, ys2), s2') ->
	      let c3 = Label.inter c1 c2 in
	      if Label.is_empty c3 then [] else
	      let n3 = isect_top comb_vars ht1 ht2 in
	      if n3 == Htype.empty_name then [] else
	      let s3' = isect_state comb_vars s1' s2' in
	      (*if state_is_obviously_empty s3' then [] else*)
	      let xs3, ys3 = comb_vars (xs1, ys1) (xs2, ys2) in
	      [((c3, n3, xs3, ys3), s3')])
	    (state_set_next ss))
	s1.next;
    s3.null <- 
      List.map (fun (a, s1') -> (a, isect_state comb_vars s1' s2)) s1.null;
    (* @ List.map (fun (a, s2') -> (a, isect_state s1 s2')) s2.null;*) (* XXX *)
    s3
      
and isect_att_free comb_vars ht1 ht2 =
  let s1 = construct ht1 in
  let s2 = construct ht2 in
  let s3 = isect_state comb_vars s1 s2 in
  recov s3

and isect_htseq comb_vars l1 l2 =
  if !Pref.typinglog then
    debug_wrap
      (fun () -> 
	printf "%a &@ %a@." 
	  Htype.print (Htype.seq l1) Htype.print (Htype.seq l2))
      (fun ht ->
	printf "%a@." Htype.print ht)
      (fun () -> isect_htseq' comb_vars l1 l2)
  else isect_htseq' comb_vars l1 l2

and isect_htseq' comb_vars l m =
  Counter.incr ctr_isect_htseq;
  try HtseqPairMap.find (l, m) !isect_asm_htype
  with Not_found ->
    let res = isect_htseq'' comb_vars l m in
    isect_asm_htype := HtseqPairMap.add (l, m) res !isect_asm_htype;
    res

and htseq_contains_bind_header m = true (* XXX *)

and isect_htseq'' comb_vars l m =
  if l == m then Htype.seq l else
  if htseq_is_empty l || htseq_is_empty m then
    Htype.empty 
  else
    let d = Label.inter (htseq_adom l) (htseq_adom m) in
    let l = List.map (restrict_att d) l in
    let m = List.map (restrict_att d) m in
    let d = Label.inter (htseq_ldom l) (htseq_ldom m) in
    let l = List.map (restrict_lab d) l in
    let m = List.map (restrict_lab d) m in
    let l = flatten_htseq l in
    let m = flatten_htseq m in
    match l, m with
    | [], _ ->
	if htseq_nullable m then Htype.epsilon else Htype.empty
    | _, [] when not(htseq_contains_exe l)  ->
	if htseq_nullable l then Htype.epsilon else Htype.empty
    | [{ def = Exe (i, ht) }], _ ->
	Htype.exe i (isect_htseq comb_vars [ht] m)
    | [{ def = Attrep (c1, n1, xs1) }], _ when htseq_is_flat m ->
	(match htseq_singleton_content c1 m with
	| [(n2, _)] -> 
	    let n3 = isect_top comb_vars n1 n2 in 
	    if n3 == Htype.empty_name then Htype.empty else
	    Htype.attrep c1 n3 xs1
	| _ -> Htype.empty)
    | _, [{ def = Attrep (c2, n2, _) }] 
      when htseq_is_flat l && not(htseq_contains_exe l) ->
	(match htseq_singleton_content c2 l with
	| [(n1, xs1)] -> 
	    let n3 = isect_top comb_vars n1 n2 in 
	    if n3 == Htype.empty_name then Htype.empty else
	    Htype.attrep c2 n3 xs1
	| _ -> Htype.empty)
    | [{ def = Alt htl }], _ ->
	Htype.alt (List.map (fun ht -> isect_htseq' comb_vars [ht] m) htl)
    | _, [{ def = Alt htl }] ->
	Htype.alt (List.map (fun ht -> isect_htseq' comb_vars l [ht]) htl)
    | _, _ ->
	if htseq_is_att_free l && htseq_is_att_free m then
	  isect_att_free comb_vars (Htype.seq l) (Htype.seq m) 
	else
	  match partition_htseq [l; m] with
	  | Some [(lf, lr); (mf, mr)] ->
	      Htype.seq [isect_htseq comb_vars lf mf; isect_htseq comb_vars lr mr]
	  | None ->
	      let ls1 = expand_htseq l in
	      let ls2 = expand_htseq m in
	      Htype.alt
		(Listutil.mapcat
		   (fun l -> List.map (fun m -> isect_htseq comb_vars l m) ls2)
		   ls1)

and isect_htype comb_vars ht1 ht2 =
  if ht1 == Htype.any then ht2 else
  if Htype.reachable_vars1 ht1 = [] && ht2 == Htype.any then ht1 else
  let [ht1; ht2] = att_normalize [ht1; ht2] in
  let ht2 = drop_exe ht2 in
  isect_htseq comb_vars [ht1] [ht2]

and isect_top comb_vars n1 n2 =
  (*if n1 == n2 then n1 else*)
  if n1 == Htype.empty_name || n2 == Htype.empty_name then Htype.empty_name else
  try 
    StringPairMap.find (n1, n2) !isect_asm_name
  with Not_found ->
    let n3 = Syn.new_name() in
    isect_asm_name := StringPairMap.add (n1, n2) n3 !isect_asm_name;
    let ht3 = isect_htype comb_vars (Htype.lookup_name n1) (Htype.lookup_name n2) in
    Htype.define_name n3 ht3;
    n3

let isect comb_vars ht1 ht2 =
  if !Pref.experim == 1 then
    begin 
      isect_asm_state := StatePairMap.empty;
      isect_asm_name := StringPairMap.empty;
      isect_asm_htype := HtseqPairMap.empty;
      Timer.reset tm_tmp;
      let size = Htype.size ht1 + Htype.size ht2 in
      let res = Timer.wrap tm_tmp (fun () -> isect_htype comb_vars ht1 ht2) in
      printf "%d %f@." size (Timer.get tm_tmp);
      res
    end
  else
  Timer.wrap tm_isect (fun () -> isect_htype comb_vars ht1 ht2)

let union_vars (xs1, ys1) (xs2, ys2) = 
  (Sortedlist.merge compare xs1 xs2,
   Sortedlist.merge compare ys1 ys2)

let disjoint ht1 ht2 =
  Htype.is_empty(isect union_vars ht1 ht2)

let disjoint_top n1 n2 =
  disjoint (Htype.lookup_name n1) (Htype.lookup_name n2)

let disjoint_state x1 x2 =
  state_is_empty(isect_state union_vars x1 x2)

(* DIFFERENCE: when applied to X and Ys, variables in X are preserved. *)

(*
   coalesce_label: f(A, B) | g(A, B) = (f | g) (A, B)
   coalesce_first: f(A, B) | f(A', B) = f(A | A', B)
   coalesce_second: f(A, B) | f(A, B') = f(A, B | B')
*)

let coalesce_label xsl =
  let xsl =
    Sort.list
      (fun (_, xs1, xs2, vs) (_, ys1, ys2, ws) -> 
        Sortedlist.compare compare xs1 ys1 < 0 &&
        compare_state_sets xs2 ys2 < 0 &&
        Sortedlist.compare compare vs ws < 0) xsl in
  List.fold_right
    (fun (c, xs1, xs2, vs) rem ->
      match rem with
        (d, ys1, ys2, ws) :: rem' when
          Sortedlist.compare compare xs1 ys1 = 0 && 
          compare_state_sets xs2 ys2 = 0 &&
	  Sortedlist.compare compare vs ws = 0 ->
          (Label.union c d, xs1, xs2, vs) :: rem'
      | _ ->
          (c, xs1, xs2, vs) :: rem)
    xsl []

let coalesce_cont xsl =
  let xsl =
    Sort.list 
      (fun (c, _, xs2, vs) (d, _, ys2, ws) -> 
        Label.compare c d < 0 &&
        compare_state_sets xs2 ys2 < 0 &&
	Sortedlist.compare compare vs ws < 0) xsl in
  List.fold_right
    (fun (c, xs1, xs2, vs) rem ->
      match rem with
        (d, ys1, ys2, ws) :: rem' 
        when Label.compare c d = 0 && compare_state_sets xs2 ys2 = 0 &&
	  Sortedlist.compare compare vs ws = 0 ->
          (c, Sortedlist.merge compare xs1 ys1, xs2, vs) :: rem'
      | _ ->
          (c, xs1, xs2, vs) :: rem)
    xsl []

let coalesce_rem xsl =
  let xsl =
    Sort.list 
      (fun (c, xs1, _, vs) (d, ys1, _, ws) -> 
        Label.compare c d < 0 &&
        Sortedlist.compare compare xs1 ys1 < 0 &&
	Sortedlist.compare compare vs ws < 0) xsl in
  List.fold_right
    (fun (c, xs1, xs2, vs) rem ->
      match rem with
        (d, ys1, ys2, ws) :: rem' 
        when Label.compare c d = 0 && 
	  Sortedlist.compare compare xs1 ys1 = 0 &&
	  Sortedlist.compare compare vs ws = 0 ->
          (c, xs1, union_state_sets xs2 ys2, vs) :: rem'
      | _ ->
          (c, xs1, xs2, vs) :: rem)
    xsl []

let coalesce_trans xsl =
  coalesce_cont
    (coalesce_rem
       (coalesce_label xsl))

let coalesce_first xsl =
  let xsl =
    Sort.list 
      (fun (_, xs2) (_, ys2) -> 
        compare_htseqalt xs2 ys2 < 0) xsl in
  List.fold_right
    (fun (xs1, xs2) rem ->
      match rem with
        (ys1, ys2) :: rem' 
        when compare_htseqalt xs2 ys2 = 0 ->
          (union_htseqalt xs1 ys1, xs2) :: rem'
      | _ ->
          (xs1, xs2) :: rem)
    xsl []

let coalesce_second xsl =
  let xsl =
    Sort.list 
      (fun (xs1, _) (ys1, _) -> 
        compare_htseqalt xs1 ys1 < 0) xsl in
  List.fold_right
    (fun (xs1, xs2) rem ->
      match rem with
        (ys1, ys2) :: rem' 
        when compare_htseqalt xs1 ys1 = 0 ->
          (xs1, union_htseqalt xs2 ys2) :: rem'
      | _ ->
          (xs1, xs2) :: rem)
    xsl []

let coalesce_partns xsl =
  coalesce_second (coalesce_first xsl)

let diff_asm_state = ref VarsStateStatesMap.empty
let diff_asm_name = ref VarsStringStringsMap.empty
let diff_asm_htype = ref VarsHtseqHtseqsMap.empty

let rec diff_rec ign x ys =
  if List.exists (fun y -> obviously_subtype x y) ys then empty_state else
  if List.for_all state_is_empty ys then x else
  try VarsStateStatesMap.find (ign, x, ys) !diff_asm_state
  with Not_found ->
    let ys' = state_set_null_closure ys in
    let z = create_state (x.final && not(state_set_final ys')) [] None in
    diff_asm_state := VarsStateStatesMap.add (ign, x, ys) z !diff_asm_state;
    let xl = 
      List.map (fun ((c, x1, vs, ws), x2) -> (c, x1, [], x2, [], vs, ws)) x.next in
    let yl = 
      List.map (fun ((c, y1, _, ws), y2) -> (c, [y1], [y2], ws)) 
	(state_set_next ys') in
    z.next <- 
      Listutil.mapcat 
	(fun ((c, _, _, _, _, _, _) as xe) -> 
	  let yl = List.filter (fun (d, _, _, _) -> Label.overlapping c d) yl in
	  let yl = coalesce_trans yl in
	  if List.length yl > 1 then Counter.incr ctr_diff_nondet;
	  diff_one_many_iter ign xe yl) xl;
    z.null <- List.map (fun (i, x2) -> (i, diff_rec ign x2 ys)) x.null;
    if not z.final && z.next = [] && z.null = [] then empty_state else
    z

and diff_one_many_iter ign (c, x1, xs1, x2, xs2, vs, ws) ysl =
  if Label.is_empty c (*|| 
			 Sub.subtype [x1] xs1 == `Succeed ||
			 Sub.subtype [x2] xs2 == `Succeed *) then
    [] 
  else
    match ysl with
      (d, ys1, ys2, us) :: ysl' ->
	if Sortedlist.diff compare (Sortedlist.diff compare us ign) ws = [] then
          diff_one_many_iter ign (Label.diff c d, x1, xs1, x2, xs2, vs, ws) ysl' @
          diff_one_many_iter ign
            (Label.inter c d, x1, Sortedlist.merge compare xs1 ys1, x2, xs2, vs, ws) ysl' @
          diff_one_many_iter ign
	    (Label.inter c d, x1, xs1, x2, union_state_sets xs2 ys2, vs, ws) ysl'
	else diff_one_many_iter ign (c, x1, xs1, x2, xs2, vs, ws) ysl'
    | [] -> 
        let z1 = if List.for_all (fun n' -> disjoint_top x1 n') xs1 then x1 else diff_top ign x1 xs1 in
        if z1 == Htype.empty_name then [] else
        let z2 = if List.for_all (fun x' -> disjoint_state x2 x') xs2 then x2 else diff_rec ign x2 xs2 in
        (*if state_is_obviously_empty z2 then [] else*)
	if z2 == empty_state then [] else
        [((c, z1, vs, ws), z2)]

and diff_att_free ign ht1 hts2 =
  let x = construct ht1 in
  let ys = List.map construct hts2 in
  let z = diff_rec ign x ys in
  recov z

and diff_htseq ign l ms =
  if !Pref.typinglog then
    debug_wrap
      (fun () -> 
	printf "%a \\@ %a@." 
	  Htype.print (Htype.seq l) Htype.print (Htype.alt (List.map Htype.seq ms)))
      (fun ht ->
	printf "%a@." Htype.print ht)
      (fun () -> diff_htseq' ign l ms)
  else diff_htseq' ign l ms

and diff_htseq' ign l ms =
  Counter.incr ctr_diff_htseq;
  try VarsHtseqHtseqsMap.find (ign, l, ms) !diff_asm_htype 
  with Not_found ->
    let res = diff_htseq'' ign l ms in
    diff_asm_htype := VarsHtseqHtseqsMap.add (ign, l, ms) res !diff_asm_htype;
    res

and diff_htseq'' ign l ms =
  if htseq_is_empty l then Htype.empty else
  let ms = List.filter (fun m -> not(htseq_is_empty m)) ms in
  if ms = [] then Htype.seq l else
  if List.memq l ms then Htype.empty else
  let ms = List.map (List.map (restrict_att (htseq_adom l))) ms in
  let ms = List.map (List.map (restrict_lab (htseq_ldom l))) ms in
  let l = flatten_htseq l in
  let ms = flatten_htseqalt ms in
  let ms = 
    if List.exists (fun m -> m != [] && htseq_nullable m) ms then
      List.filter (fun m -> m != []) ms 
    else ms in
  match l with
  | [] -> 
      if List.exists htseq_nullable ms then Htype.empty else Htype.epsilon
  | [{ def = Attrep (c1, n1, vs) }] when List.for_all htseq_is_flat ms ->
      let ns2, _ = List.split (htseqalt_singleton_content c1 ms) in
      let n3 = diff_top ign n1 ns2  in
      if n3 == Htype.empty_name then Htype.empty else
      Htype.attrep c1 n3 vs
  | [{ def = Exe (i, ht) }] ->
      Htype.exe i (diff_htseq ign [ht] ms)
  | [{ def = Alt htl1 }] ->
      Htype.alt (List.map (fun ht1 -> diff_htseq ign [ht1] ms) htl1)
  | _ ->
      if htseq_is_att_free l && List.for_all htseq_is_att_free ms then
	diff_att_free ign (Htype.seq l) (List.map Htype.seq ms) 
      else
	match partition_htseq (l :: ms) with
	| Some ((lf, lr) :: partns) ->
	    let partns = List.map (fun (m1, m2) -> ([m1], [m2])) partns in
	    let partns = coalesce_partns partns in
	    if List.length partns > 1 then 
	      begin Counter.incr ctr_diff_htseq_nondet;
		(*printf "l = %a@."  Htype.print (Htype.seq l);
		List.iter (fun m -> printf "m = %a@." Htype.print (Htype.seq m)) ms*)
	      end;
	    diff_htseq_pairs ign (lf, [], lr, []) partns
	| None ->
	    let ls = expand_htseq l in
	    let ms = Listutil.mapcat expand_htseq ms in
	    Htype.alt (List.map (fun l -> diff_htseq ign l ms) ls)

and diff_htseq_pairs ign (l1, ls1, l2, ls2) partns =
  match partns with
    (m1, m2) :: partns' ->
      Htype.alt
	[diff_htseq_pairs ign (l1, union_htseqalt m1 ls1, l2, ls2) partns';
	 diff_htseq_pairs ign (l1, ls1, l2, union_htseqalt m2 ls2) partns']
  | [] ->
      let ht1 = diff_htseq ign l1 ls1 in
      if Htype.is_obviously_empty ht1 then Htype.empty else
      let ht2 = diff_htseq ign l2 ls2 in
      if Htype.is_obviously_empty ht2 then Htype.empty else
      Htype.seq [ht1; ht2]

and diff_htype ign ht1 hts2 =
  if List.exists (fun ht -> ht == Htype.any) hts2 then Htype.empty else
  let (ht1 :: hts2) = att_normalize (ht1 :: hts2) in
  let hts2 = List.map drop_exe hts2 in
  diff_htseq ign [ht1] (List.map (fun ht2 -> [ht2]) hts2)

and diff_top ign n1 ns2 =
  if !Pref.typinglog then
    debug_wrap
      (fun () -> 
	printf "%s \\@ " n1;
	List.iter (fun n2 -> printf "%s " n2) ns2;
	printf "@.")
      (fun n3 ->
	printf "%s@." n3)
      (fun () -> diff_top' ign n1 ns2)
  else diff_top' ign n1 ns2

and diff_top' ign n1 ns2 =
  if ns2 = [] then n1 else
  if List.memq n1 ns2 then Htype.empty_name else
  try
    VarsStringStringsMap.find (ign, n1, ns2) !diff_asm_name
  with Not_found -> begin
    let n3 = Syn.new_name() in
    diff_asm_name := VarsStringStringsMap.add (ign, n1, ns2) n3 !diff_asm_name;
    let ht3 = 
      diff_htype ign (Htype.lookup_name n1) (List.map Htype.lookup_name ns2) in
    Htype.define_name n3 ht3;
    n3
  end

let diff ign ht1 ht2 =
  if !Pref.experim == 2 then
    begin 
      diff_asm_state := VarsStateStatesMap.empty;
      diff_asm_name := VarsStringStringsMap.empty;
      diff_asm_htype := VarsHtseqHtseqsMap.empty;
      Timer.reset tm_tmp;
      let size = Htype.size ht1 + Htype.size ht2 in
      let res = Timer.wrap tm_tmp (fun () -> diff_htype ign ht1 [ht2]) in
      printf "%d %f@." size (Timer.get tm_tmp);
      res
    end
  else
  Timer.wrap tm_diff (fun () -> diff_htype ign ht1 [ht2])

let subtype ht1 ht2 =
  let ht3 = diff [] ht1 ht2 in
  Htype.is_empty ht3

let subtype_ignoring_vars ign ht1 ht2 =
  let ht3 = diff ign ht1 ht2 in
  Htype.is_empty ht3

(* Note:

   + Attribute normalization is critical.  This allows to check
   overlapping of attribute names by physical equality, drastically
   improving performance.

   + @A+ makes a lot of troubles.  Realignment makes it an ugly
   combination of unions and concatenations of other @A+'s:  
 
     @(A|B)+  =  @A+ | (@A+|()), @B+

   It makes bool operations very inefficient.  On the other hand,
   realignment of @A* is much easier to treat:

     @(A|B)*  =  @A*,@B*

   So it is important to keep @A* from the surface language to the
   internal representation.

  To do:

   + subtype error report (typath)

*)

(* INFERENCE *)

let rec extract_for_tyvar x ht =
  if not(List.mem x (Htype.reachable_vars1 ht)) then
    Htype.empty 
  else
    match ht.def with
    | Elm (c, n, xs, ys) -> 
	if List.mem x xs then Htype.elm c n [] ys else
	extract_for_tyvar x (Htype.lookup_name n)
    | Rep ht' ->
	extract_for_tyvar x ht'
    | Attrep (c, n, xs) -> 
	extract_for_tyvar x (Htype.lookup_name n)
    | Alt htl -> 
	Htype.alt (List.map (extract_for_tyvar x) htl)
    | Seq htl -> 
	Htype.alt (List.map (extract_for_tyvar x) htl)
    | Exe _ ->
	assert false

let extract_for_tyvar x ht = Timer.wrap tm_extract (fun () -> extract_for_tyvar x ht)

let rec extract_for_var x ht =
  if not(List.mem x (Htype.reachable_vars1 ht)) then
    if Htype.is_empty ht then Htype.empty else Htype.epsilon
  else
    match ht.def with
    | Elm (c, n, xs, ys) -> 
	if List.mem x xs then Htype.elm c n [] ys else
	extract_for_var x (Htype.lookup_name n)
    | Rep ht' ->
	Htype.rep (extract_for_var x ht')
    | Attrep (c, n, xs) -> 
	if List.mem x xs then Htype.attrep c n [] else
	extract_for_var x (Htype.lookup_name n)
    | Alt htl -> 
	Htype.alt (List.map (extract_for_var x) htl)
    | Seq htl -> 
	Htype.seq (List.map (extract_for_var x) htl)
    | Exe _ ->
	assert false

let extract_for_var x ht = Timer.wrap tm_extract (fun () -> extract_for_var x ht)

let infer_pat xs ht1 ht2 =
  let ht3 = isect (fun (xs2, _) (_, ys1) -> (xs2, ys1)) ht2 ht1 in
  let ht3 = Htype.elim_empty ht3 in
  let res = List.map (fun x -> (x, extract_for_var x ht3)) xs in
  if !Pref.typinglog then begin
    List.iter 
      (fun (x, ht) -> printf "%s: %a@." x Htype.print ht)
      res
  end;
  res
    
let infer_ty ys ht1 ht2 =
  let ht3 = isect (fun (_, ys2) (_, ys1) -> (ys2, ys1)) ht2 ht1 in
  let ht3 = Htype.elim_empty ht3 in
  let res = List.map (fun y -> (y, extract_for_tyvar y ht3)) ys in
  if !Pref.typinglog then begin
    List.iter 
      (fun (x, ht) -> printf "%s: %a@." x Htype.print ht)
      res
  end;
  res

let rec extract_for_id asm i ht =
  match ht.def with
  | Elm (_, n, _, _) 
  | Attrep (_, n, _) ->
      if Setutil.StringSet.mem n !asm then Htype.empty else begin
	asm := Setutil.StringSet.add n !asm;
	extract_for_id asm i (Htype.lookup_name n)
      end
  | Rep ht' -> 
      extract_for_id asm i ht'
  | Alt htl 
  | Seq htl ->
      Htype.alt (List.map (extract_for_id asm i) htl)
  | Exe (j, ht') ->
      if i = j then ht' else Htype.empty

let extract_for_id i ht = extract_for_id (ref Setutil.StringSet.empty) i ht

let rec recon_filter_type asm id_to_type ht =
  match ht.def with
  | Elm (c, n, vs, ws) -> 
      Htype.elm c (recon_filter_type_top asm id_to_type n) vs ws
  | Attrep (c, n, vs) -> 
      Htype.attrep c (recon_filter_type_top asm id_to_type n) vs
  | Rep ht' ->
      Htype.rep (recon_filter_type asm id_to_type ht')
  | Alt htl -> 
      Htype.alt (List.map (recon_filter_type asm id_to_type) htl)
  | Seq htl -> 
      Htype.seq (List.map (recon_filter_type asm id_to_type) htl)
  | Exe (i, _) ->
      List.assq i id_to_type

and recon_filter_type_top asm id_to_type n =
  try
    Setutil.StringMap.find n !asm 
  with Not_found -> begin
    let ht = Htype.lookup_name n in
    if Htype.reachable_exe_ids ht = [] then n else
    let n' = Syn.new_name() in		
    asm := Setutil.StringMap.add n n' !asm;
    let ht' = recon_filter_type asm id_to_type ht in
    Htype.define_name n' ht';
    n'
  end

let recon_filter_type id_to_type n = 
  recon_filter_type (ref Setutil.StringMap.empty) id_to_type n

(* Substitution s1{x -> s2} where s2's initial state is n2i  *)
(* We assume that s2 matches exactly a sequence with one element *)

module SubstMap = Map.Make(Setutil.MakeTuple3(Setutil.String)(Setutil.String)(Htype.Ht))

let subst_asm = ref SubstMap.empty

let rec subst_htype ht1 x ht2 =
  if not(List.mem x (Htype.reachable_vars2 ht1)) then
    ht1
  else
    match ht1.def with
    | Elm (c, n, xs, ys) -> 
	if not(List.mem x ys) then 
	  Htype.elm c (subst_top n x ht2) xs ys
	else
	  isect_htype union_vars (Htype.elm c n xs (Sortedlist.diff compare ys [x])) ht2
    | Rep ht1' ->
	Htype.rep (subst_htype ht1' x ht2)
    | Attrep (c, n, xs) -> 
	Htype.attrep c (subst_top n x ht2) xs
    | Alt htl -> 
	Htype.alt (List.map (fun ht1 -> subst_htype ht1 x ht2) htl)
    | Seq htl -> 
	Htype.seq (List.map (fun ht1 -> subst_htype ht1 x ht2) htl)
    | Exe _ ->
	assert false

and subst_top n1 x ht2 =
  try SubstMap.find (n1, x, ht2) !subst_asm
  with Not_found -> begin
    let ht1 = Htype.lookup_name n1 in
    if ht1 == Htype.any then n1 else
    if not(List.mem x (Htype.reachable_vars2 ht1)) then n1 else
    let n3 = Syn.new_name() in
    subst_asm := SubstMap.add (n1, x, ht2) n3 !subst_asm;
    let ht3 = subst_htype ht1 x ht2 in
    Htype.define_name n3 ht3;
    n3
  end

let subst ht1 x ht2 =
  Timer.wrap tm_subst (fun () -> subst_htype ht1 x ht2)

(* Marking ambiguity check *)

let rec marks_same asm ht =
  if Htype.HtSet.mem ht !asm then true else begin
    asm := Htype.HtSet.add ht !asm;
    match ht.Htype.def with
    | Elm (c, n, xs, ys) -> 
	Sortedlist.compare compare xs ys = 0 &&
	marks_same asm (Htype.lookup_name n)
    | Rep ht' ->
	marks_same asm ht'
    | Attrep (c, n, xs) -> 
	marks_same asm (Htype.lookup_name n)
    | Alt htl -> 
	List.for_all (marks_same asm) htl
    | Seq htl -> 
	List.for_all (marks_same asm) htl
    | Exe _ ->
	assert false
  end

let is_marking_ambiguous zs ht =
  let ht1 = 
    isect_htype 
      (fun (_, ys1) (_, ys2) ->
	(Sortedlist.isect compare ys1 zs,
	 Sortedlist.isect compare ys2 zs))
      ht ht in
  let ht1 = Htype.elim_empty ht1 in
  not(marks_same (ref Htype.HtSet.empty) ht1)
