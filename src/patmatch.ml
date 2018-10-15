open Htype
open Format

(* AUTOMATA *)

type null_annot = [`Begin of int | `End]

type state =
    { id : int;
      mutable final : bool;
      mutable next : ((Label.t * top_state * string list * string list) * state) list;
      mutable attrep : ((Label.t * top_state * string list) * state) list;
      mutable attexc : (Label.t * state) list;
      mutable null : (null_annot * state) list;
      mutable any : bool;
    } 

and top_state =
    { top_id : int;
      mutable start : state list;
      mutable attrep_pool : (Label.t * top_state) list;
      mutable attexc_pool : Label.t list;
    } 

let last_id = ref 0

let create_state ()  =
  incr last_id;
  { id = !last_id; 
    final = false;
    next = [];
    attrep = [];
    attexc = [];
    null = [];
    any = false;
  }

let create_top_state()  =
  incr last_id;
  { top_id = !last_id; 
    start = [];
    attrep_pool = [];
    attexc_pool = [];
  }

let add_attrep (c, s) t =
  if List.exists (fun (c', s') -> Label.equal c c' && s == s') t.attrep_pool
  then ()
  else t.attrep_pool <- t.attrep_pool @ [(c, s)]

let add_attexc c t =
  if List.exists (fun c' -> Label.equal c c') t.attexc_pool
  then ()
  else t.attexc_pool <- t.attexc_pool @ [c]

let empty_state = create_state ()

let compare_state x1 x2 = compare x1.id x2.id
let compare_top_state x1 x2 = compare x1.top_id x2.top_id

let union_trans l1 l2 = l1 @ l2

let state_set_next xs = 
  Listutil.union_many union_trans (List.map (fun x -> x.next) xs)
let state_set_final s = List.exists (fun x -> x.final) s

let mem_state_sets = Sortedlist.mem compare_state
let compare_state_sets = Sortedlist.compare compare_state
let union_state_sets = Sortedlist.merge compare_state
let diff_state_sets = Sortedlist.diff compare_state

let mem_top_state_sets = Sortedlist.mem compare_top_state
let compare_top_state_sets = Sortedlist.compare compare_top_state
let union_top_state_sets = Sortedlist.merge compare_top_state
let diff_top_state_sets = Sortedlist.diff compare_top_state

(* AUTOMATA CONSTRUCTION *)

module HtList =
  struct
    type t = Htype.ht list
    let compare = compare
  end

module HtlLab = Setutil.MakePair(HtList)(Label)

module AsmMap = Map.Make(HtlLab)
module AsmSet = Set.Make(HtlLab)
module AsmTop = Map.Make(Setutil.String)

let asm_top = ref AsmTop.empty

let rec construct_top n =
  try AsmTop.find n !asm_top
  with Not_found ->
    let t = create_top_state () in
    asm_top := AsmTop.add n t !asm_top;
    let asm = ref AsmMap.empty in

    let rec construct htl adom =
      try AsmMap.find (htl, adom) !asm
      with Not_found ->
	let s = create_state () in
	asm := AsmMap.add (htl, adom) s !asm;
	if htl = [Htype.any] then s.any <- true;
	let asm' = ref AsmSet.empty in

	let rec construct' htl adom =
	  if not(AsmSet.mem (htl, adom) !asm') then begin
	    asm' := AsmSet.add (htl, adom) !asm';
	    let htl_adom = Label.union_many (List.map (fun ht -> ht.adom) htl) in
	    let adom' = Label.diff adom htl_adom in
	    if not (Label.is_empty adom') then
	      let s' = construct htl htl_adom in
	      add_attexc adom' t;
	      s.attexc <- (adom', s') :: s.attexc
	    else
	      match htl with
	      | [] -> 
		  s.final <- true
	      | ht :: rest ->
		  match ht.def with
		  | Elm (c, n, xs, ys) -> 
		      let s' = construct rest adom in
		      let s'' = construct_top n in
		      s.next <- ((c, s'', xs, ys), s') :: s.next
		  | Rep ht' ->
		      construct' rest adom;
		      construct' ([ht'; ht] @ rest) adom
		  | Attrep (c, n, xs) ->
		      let s' = construct rest (Label.diff adom c) in
		      let s'' = construct_top n in
		      add_attrep (c, s'') t;
		      s.attrep <- ((c, s'', xs), s') :: s.attrep
		  | Alt htl' -> 
		      List.iter (fun ht' -> construct' (ht' :: rest) adom) htl'
		  | Seq htl' ->
		      construct' (htl' @ rest) adom
		  | Exe (i, ht') ->
		      if i == -1 then 
			let s' = construct rest adom in
			s.null <- (`End, s') :: s.null
		      else 
			let s' = 
			  construct (ht' :: Htype.exe (-1) Htype.epsilon :: rest)
			    adom in
			s.null <- (`Begin i, s') :: s.null
	  end in
	construct' htl adom;
	s in

    t.start <- [construct [Htype.lookup_name n] Label.any_label];
    t
      
let construct ht =
  let n = Htype.give_unique_name ht in
  construct_top n

(* Validation: assumes there to be no null transitions *)

open Syn

let match_baseval b c =
  Label.subset (Label.single b) c

let match_label ns l c =
  Label.subset (Label.label ns l) c

let separate_atts va =
  Listutil.mapcat (function MAtt(ns, c, va) -> [(ns, c, va)] | _ -> []) va,
  List.filter (function MAtt _ -> false | _ -> true) va

let convert_to c v = v  

let get_rem_states pairs =
  Listutil.union_many union_state_sets
    (Listutil.mapcat (fun (_, xl) -> List.map (fun (_, x) -> [x]) xl) 
       pairs)

let get_cont_states pairs =
  Listutil.union_many union_top_state_sets
    (Listutil.mapcat (fun (_, xl) -> List.map (fun ((_, x, _, _), _) -> [x]) xl) 
       pairs)

exception Fail of Typath.t

let make_res f pairs =
  Listutil.mapcat
    (fun (x, xl) -> if List.exists f xl then [x] else [])
    pairs

let epsilon_closure xs (tbl_rep, tbl_exc) =
  let rec iter ys xs =
    let attrep = Listutil.mapcat (fun y -> y.attrep) ys in
    let attexc = Listutil.mapcat (fun y -> y.attexc) ys in
    let rem = 
      List.sort compare_state
	(Listutil.mapcat
	   (fun ((c, x1, _), x2) -> 
	     if Hashtbl.find tbl_rep (c, x1) then [x2] else [])
	   attrep @
	 Listutil.mapcat
	   (fun (c, x2) -> 
	     if Hashtbl.find tbl_exc c then [x2] else [])
	   attexc) in
    let xs' = diff_state_sets rem xs in
    if xs' = [] then xs else
    iter xs' (union_state_sets xs' xs) in
  iter xs xs

let filter_next f m =
  List.map (fun (x, ys) -> (x, List.filter f (state_set_next ys))) m

let filter_final m =
  let fin = List.filter (fun (x, ys) -> state_set_final ys) m in
  let res, _ = List.split fin in
  res

let rec validate_main xs tbl va =
  let epsclos_map = List.map (fun x -> (x, epsilon_closure [x] tbl)) xs in
  match va with
  | [] ->
      let res = filter_final epsclos_map in
      if res = [] then `Fail `Empty else `Succeed res
  | MWs _ :: va1 -> 
      validate_main xs tbl va1
  | MBase b :: va1 ->
      let pairs = filter_next (fun ((c, _, _, vs), _) -> match_baseval b c && vs = []) epsclos_map in
      let xs2 = get_rem_states pairs in
      if xs2 = [] then `Fail (`BaseVal (b, `Any)) else
      (match validate_main xs2 tbl va1 with
      | `Fail w -> 
          `Fail (`BaseVal (b, w))
      | `Succeed res -> 
          `Succeed (make_res (fun (_, x2) -> List.memq x2 res) pairs))
  | MLab (ns, l, va1) :: va2 ->
      let pairs = filter_next (fun ((c, _, _, vs), _) -> match_label ns l c && vs = []) epsclos_map in
      let xs1 = get_cont_states pairs in
      let xs2 = get_rem_states pairs in
      if xs1 = [] || xs2 = [] then
        `Fail (`Lab (Label.label ns l, `Any, `Any))
      else
        (match validate_top xs1 va1 with
        | `Fail w1 -> `Fail (`Lab (Label.label ns l, w1, `Any))
        | `Succeed res1 ->
            (match validate_main xs2 tbl va2 with
            | `Fail w2 -> `Fail (`Lab (Label.label ns l, `Any, w2))
            | `Succeed res2 ->
                let res =
		  make_res 
		    (fun ((_, x1, _, _), x2) -> 
		      List.memq x1 res1 && List.memq x2 res2)
		    pairs in
                if res = [] then `Fail (`Lab (Label.label ns l, `Any, `Any))
                      (* XXX: Need a postprocessing to improve the error message *)
                else `Succeed res))
  | MAtt _ :: _ ->
      assert false

and validate_att rep exc ava =
  let tbl_exc = Hashtbl.create 13 in
  let tbl_rep = Hashtbl.create 13 in
  List.iter
    (fun c -> 
      Hashtbl.add tbl_exc c
        (not (List.exists (fun (ns, l, _) -> match_label ns l c) ava)))
    exc;
  try
    let res =
      List.map
	(fun (ns, l, va) ->
	  let xs = 
	    Listutil.union_many union_top_state_sets
	      (List.map (fun (c, x) -> if match_label ns l c then [x] else [])
		 rep) in
	  if xs = [] then
	    raise (Fail (`Att(Label.label ns l, `Any, `Any))) else
	  match validate_top xs va with
	  | `Fail w -> raise (Fail (`Att(Label.label ns l, w, `Any)))
	  | `Succeed res -> (ns, l, res))
	ava in
    List.iter
      (fun (c, x) ->
	Hashtbl.add tbl_rep (c, x)
	  (List.for_all 
	     (fun (ns, l, xs) -> 
	       not(match_label ns l c) || List.memq x xs) res &&
	   List.exists 
	     (fun (ns, l, xs) -> match_label ns l c) res))
      rep;
    `Succeed (tbl_rep, tbl_exc)
  with Fail w -> `Fail w

and validate_top xs va =
  let ava, va = separate_atts va in
  let xs' = 
    Listutil.union_many union_state_sets (List.map (fun x -> x.start) xs) in
  let attrep_pool = List.concat (List.map (fun x -> x.attrep_pool) xs) in
  let attexc_pool = List.concat (List.map (fun x -> x.attexc_pool) xs) in
  match validate_att attrep_pool attexc_pool ava with
  | `Fail w -> `Fail w
  | `Succeed tbl ->
      (match validate_main xs' tbl va with
      | `Fail w ->			(* XXX: imprecise error message *)
	  `Fail 
	    (List.fold_right (fun (ns, l, _) w -> 
	      `Att(Label.label ns l, `Any, w))
	       ava w)
      | `Succeed res ->
	  `Succeed
	    (List.filter
	       (fun x -> 
		 List.exists (fun x' -> List.memq x' res) x.start) xs))

let validate x va =
  validate_top [x] va

(* Pattern matching *)

let rec patmatch_top x va =
  let ava, va = separate_atts va in
  patmatch_state (List.hd x.start) ava va

and patmatch_state x ava va =
  if x.any then 
    `Succeed [`Val (List.map (fun (ns, c, va') -> MAtt(ns, c, va')) ava @ va)] 
  else if x.final && va = [] then `Succeed [] else 
  match va with
  | MWs _ :: va1 -> 
      patmatch_state x ava va1
  | _ ->
      match patmatch_attexc x.attexc ava va with
      | `Succeed decova -> `Succeed decova
      | `Fail ->
	  match patmatch_attrep x.attrep ava va with
	  | `Succeed decova -> `Succeed decova
	  | `Fail -> 
	      match patmatch_null x.null ava va with
	      |	`Succeed decova -> `Succeed decova
	      |	`Fail -> patmatch_tran x.next ava va

and patmatch_tran xl ava va =
  match xl with
  | [] -> `Fail
  | ((c, x1, xs, _), x2) :: xl ->
      match va with
      |	[] -> `Fail
      |	MBase b :: va1 ->
	  if match_baseval b c then 
	    match patmatch_state x2 ava va1 with
	    | `Succeed decova'' -> `Succeed (`Bind (xs, `Base b) :: decova'')
	    | `Fail -> patmatch_tran xl ava va
	  else
	    patmatch_tran xl ava va 
      |	MLab (ns, l, va1) :: va2 ->
	  if match_label ns l c then
	    match patmatch_top x1 va1 with
	    | `Succeed decova' ->
		begin
		  match patmatch_state x2 ava va2 with
		  | `Succeed decova'' -> 
		      `Succeed (`Bind (xs, (`Lab (ns, l, decova'))) :: decova'')
		  | `Fail -> 
		      patmatch_tran xl ava va 
		end
	    | `Fail -> patmatch_tran xl ava va
	  else
	    patmatch_tran xl ava va 
      |	_ -> assert false

and patmatch_attexc exc ava va =
  match exc with
  | [] -> `Fail
  | (c, x2) :: exc ->
      if List.exists (fun (ns, l, _) -> match_label ns l c) ava then
	patmatch_attexc exc ava va 
      else
	match patmatch_state x2 ava va with
	| `Succeed decova' -> `Succeed decova'
	| `Fail -> patmatch_attexc exc ava va

and patmatch_attrep rep ava va =
  match rep with
  | [] -> `Fail
  | ((c, x1, xs), x2) :: rep ->
      if List.exists (fun (ns, l, _) -> match_label ns l c) ava then
	let rec iter ava1 =
	  match ava1 with
	  | [] ->  
	      patmatch_state x2 ava va 
	  | (ns, l, va1) :: ava1 -> 
	      if match_label ns l c then
		match patmatch_top x1 va1 with
		| `Succeed decova' ->
		    (match iter ava1 with
		      `Succeed decova'' -> `Succeed (`Bind(xs, `Att (ns, l, decova')) :: decova'')
		    | `Fail -> patmatch_attrep rep ava va)
		| `Fail ->
		    patmatch_attrep rep ava va 
	      else
		iter ava1 in
	iter ava
      else
	patmatch_attrep rep ava va 

and patmatch_null null ava va =
  match null with
  | [] -> `Fail
  | (a, x2) :: null ->
      match patmatch_state x2 ava va with
      |	`Succeed decova' -> `Succeed (`Exe a :: decova')
      |	`Fail -> patmatch_null null ava va

let rec recon_value d =
  match d with
  | [] ->
      []
  | `Bind (_, `Base b) :: d2 -> 
      MBase b :: recon_value d2
  | `Bind (_, `Lab (ns, l, d1)) :: d2 -> 
      MLab (ns, l, recon_value d1) :: recon_value d2
  | `Bind (_, `Att (ns, l, d1)) :: d2 -> 
      MAtt (ns, l, recon_value d1) :: recon_value d2
  | `Val va :: d2 -> 
      va @ recon_value d2
  | `Exe _ :: _ -> 
      assert false

let rec recon_binding var d =
  match d with
  | [] -> []
  | `Bind (xs, `Base b) :: d2 ->
      if List.mem var xs then MBase b :: recon_binding var d2 else
      recon_binding var d2
  | `Bind (xs, `Lab (ns, l, d1)) :: d2 ->
      if List.mem var xs then 
	MLab (ns, l, recon_value d1) :: recon_binding var d2
      else
	let va = recon_binding var d2 in
	if va = [] then recon_binding var d1 else
	va
  | `Bind (xs, `Att (ns, l, d1)) :: d2 ->
      if List.mem var xs then 
	MAtt (ns, l, recon_value d1) :: recon_binding var d2
      else
	let va = recon_binding var d2 in
	if va = [] then recon_binding var d1 else
	va
  | `Val va :: d2 ->
      recon_binding var d2
  | `Exe _ :: _ ->
      assert false

let rec print_va ff = function
  | [] -> 
      fprintf ff "()" 
  | [elem] -> 
      fprintf ff "@[%a@]" print_elem elem
  | elems ->  
      fprintf ff "@[(@[%a@])@]" print_elem_seq elems

and print_elem_seq ff = function
  | [] -> 
      ()
  | [elem] ->
      print_elem ff elem 
  | elem::elems ->
      fprintf ff "%a,@ %a" print_elem elem print_elem_seq elems

and print_elem ff = function 
  | `Bind(xs, `Base baseval) ->
      fprintf ff "@[%a%s@]" print_vars xs (Base.string_of_baseval baseval)
  | `Bind(xs, `Lab (ns, s, va1)) -> 
      fprintf ff "@[%a%a:%a[@[%a@]]@]" print_vars xs Sym.print ns Sym.print s print_elem_seq va1
  | `Bind(xs, `Att (ns, s, va1)) -> 
      fprintf ff "@[@@%a%a:%a[@[%a@]]@]" print_vars xs Sym.print ns Sym.print s print_elem_seq va1
  | `Val va ->
      fprintf ff "%a" Synutil.print_va va
  | `Exe (`Begin i) ->
      fprintf ff "begin-%d" i
  | `Exe `End ->
      fprintf ff "end"

and print_vars ch xv =
  match xv with
  | [] -> fprintf ch ""
  | var :: xv -> fprintf ch "%s:%a" var print_vars xv


let patmatch vars x va =
  match patmatch_top x va with
  | `Fail -> 
      `Fail
  | `Succeed d -> 
      `Succeed (List.map (fun var -> (var, recon_binding var d)) vars)

let rec split_by_end d =
  match d with
  | `Exe `End :: d2 -> [], d2
  | x :: d2 ->
      let d3, d4 = split_by_end d2 in
      x :: d3, d4
  | [] -> [], []

let rec recon eval d =
  match d with
  | [] ->
      []
  | `Bind (_, `Base b) :: d2 ->
      MBase b :: recon eval d2
  | `Bind (_, `Lab (ns, l, d1)) :: d2 ->
      MLab (ns, l, recon eval d1) :: recon eval d2
  | `Bind (_, `Att (ns, l, d1)) :: d2 ->
      MAtt (ns, l, recon eval d1) :: recon eval d2
  | `Val va :: d2 ->
      va @ recon eval d2
  | `Exe (`Begin i) :: d2 ->
      let d3, d4 = split_by_end d2 in
      eval i d3 @ recon eval d4
  | `Exe `End :: _ ->
      assert false

let eval_filter id_to_dom x va eval =
  match patmatch_top x va with
  | `Fail -> 
      `Fail
  | `Succeed decova ->
      `Succeed
	(recon
	   (fun i d -> 	     
	     let env = 
	       List.map (fun var -> (var, recon_binding var d)) 
		 (List.assq i id_to_dom) in
	     eval env i)
	   decova)

