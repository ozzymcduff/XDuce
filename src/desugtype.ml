open Finfo
open Syn

let timer_desugtype = Timer.create "desug:type"

exception Ill_formed_type of finfo * string

let rec eval_nset fi nset =
  match nset with
  | NQName (p, l) -> Label.label (Ctx.lookup_nsdef fi p) l
  | NNSName p -> Label.ns_label (Ctx.lookup_nsdef fi p)
  | NAnyName -> Label.any_label
  | NOr (nset1, nset2) -> Label.union (eval_nset fi nset1) (eval_nset fi nset2)
  | NDiff (nset1, nset2) -> Label.diff (eval_nset fi nset1) (eval_nset fi nset2)

(* mapping from parse-trees to hash type variables *)

let hash_combine h h' = h + 17 * h'
let hash_list l = List.fold_left (fun h x -> hash_combine x h) 0 l

let rec hash_nset nset =
  match nset with
  | NQName (p, l) -> Hashtbl.hash l
  | NNSName p -> Hashtbl.hash p
  | NAnyName -> 13
  | NOr (nset1, nset2) -> hash_combine (hash_nset nset1) (hash_nset nset2)
  | NDiff (nset1, nset2) -> hash_combine (hash_nset nset1) (hash_nset nset2)

let rec hash_ty t i =
  if i = 4 then 0 else
  let i = i + 1 in
  match t with
  | TVar(fi, s) -> Hashtbl.hash s
  | TBase(fi, b) -> Hashtbl.hash b
  | TSingle(fi, b) -> Hashtbl.hash b
  | TLab(fi, nset, t1) -> hash_combine (hash_nset nset) (hash_ty t1 i)
  | TEmpty fi -> 3
  | TNone fi -> 7
  | TCat (fi, t1, t2) -> hash_combine (hash_ty t1 i) (hash_ty t2 i)
  | TClos (fi, t1) -> hash_combine 17 (hash_ty t1 i)
  | TClos1 (fi, t1) -> hash_combine 19 (hash_ty t1 i)
  | TAtt(fi, nset, t1) -> hash_nset nset
  | TAttRem _ -> 11
  | TUnion(fi, t1, t2) -> hash_combine 23 (hash_ty t1 i)
  | TUnionF(fi, t1, t2) -> hash_combine 29 (hash_ty t1 i)
  | TTyAs (fi, x, t1) -> hash_ty t1 i
  | TAs (fi, x, t1) -> hash_ty t1 i
  | TRule (fi, t1, _, i1) -> hash_combine i1 (hash_ty t1 i)
  | TSubst (fi, t1, s, t2) -> hash_combine (hash_ty t1 i) (hash_combine (Hashtbl.hash s) (hash_ty t2 i))
  | TApp _ -> assert false

let hash_ty t = (hash_ty t 0) land 0x3FFFFFFF

(* equalities between namesets and between types *)

let rec equal_nset nset nset' =
  nset == nset' ||
  match nset, nset' with
  | NQName(ns, ln), NQName(ns', ln') ->
      ns == ns' && ln == ln'
  | NNSName ns, NNSName ns' ->
      ns == ns'
  | NAnyName, NAnyName ->
      true
  | NOr(nset1, nset2), NOr(nset1', nset2') ->
      equal_nset nset1 nset1' && equal_nset nset2 nset2'
  | NDiff(nset1, nset2), NDiff(nset1', nset2') ->
      equal_nset nset1 nset1' && equal_nset nset2 nset2'
  | _ -> 
      false

let rec equal_ty t t' =
  t == t' ||
  match t,t' with
  | TVar(_, s), TVar(_, s') -> s = s'
  | TBase(_, b), TBase(_, b') -> b = b'
  | TSingle(_, b), TSingle(_, b') -> b = b'
  | TEmpty _, TEmpty _ 
  | TNone _, TNone _ -> true
  | TAtt(fi, nset1, t1), TAtt(fi', nset1', t1')
  | TLab(fi, nset1, t1), TLab(fi', nset1', t1') -> 
      Label.equal (eval_nset fi nset1) (eval_nset fi' nset1') && 
      equal_ty t1 t1'
  | TUnion(_, t1, t2), TUnion(_, t1', t2') 
  | TUnionF(_, t1, t2), TUnionF(_, t1', t2') 
  | TCat (_, t1, t2), TCat (_, t1', t2') -> equal_ty t1 t1' && equal_ty t2 t2'
  | TClos1 (_, t1), TClos1 (_, t1') 
  | TClos (_, t1), TClos (_, t1') -> equal_ty t1 t1'
  | TAs (_, x, t1), TAs (_, x', t1') -> x = x' && equal_ty t1 t1'
  | TRule (_, t1, _, i1), TRule (_, t1', _, i1') -> equal_ty t1 t1' && i1 == i1'
  | TSubst (_, t1, s, t2), TSubst (_, t1', s', t2') -> equal_ty t1 t1' && s = s' && equal_ty t2 t2'
  | _ -> false

module Tbl = Hashtbl.Make
    (struct 
      type t = Syn.ty 
      let hash = hash_ty
      let equal = equal_ty
    end)

let desug_tbl = Tbl.create 101

(* well-formedness *)

exception Ill_formed_pattern of finfo * string

let wf_type () =
  let rec check_regular asm x ty toplevel insubst = 
    match ty with
    | TVar (fi, y) ->
	if x = y && toplevel then
	  raise (Ill_formed_type (fi, "Top-level type recursion"));
	if x = y && insubst then
	  raise (Ill_formed_type (fi, "Recursion in substituted type"));
	if not(Setutil.StringSet.mem y !asm) then begin
	  asm := Setutil.StringSet.add y !asm;
	  check_regular asm x (Ctx.lookup_tydef fi y) toplevel insubst
	end
    | TBase _ 
    | TSingle _ 
    | TEmpty _ 
    | TNone _ 
    | TAttRem _ ->
	()
    | TLab (_, _, ty1) 
    | TAtt (_, _, ty1) ->
	check_regular asm x ty1 false insubst
    | TCat(_, ty1, ty2) 
    | TUnion(_, ty1, ty2) 
    | TUnionF(_, ty1, ty2) ->
	check_regular asm x ty1 toplevel insubst;
	check_regular asm x ty2 toplevel insubst
    | TClos (_, ty) 
    | TClos1 (_, ty)
    | TTyAs (_, _, ty) 
    | TAs (_, _, ty) 
    | TRule (_, ty, _, _) ->
	check_regular asm x ty toplevel insubst
    | TSubst (_, ty1, _, ty2) ->
	check_regular asm x ty1 toplevel insubst; 
	check_regular asm x ty2 toplevel true; 
    | TApp _ ->
	assert false
  in
  Ctx.iter_tydef
    (fun name (fi, ty) -> 
      check_regular (ref Setutil.StringSet.empty) name ty true false)
  
let rec check_pattern_linear_and_get_variables pat =
  match pat with
  | TVar _ 
  | TBase _
  | TSingle _
  | TEmpty _ 
  | TNone _  
  | TAttRem _ ->
      []
  | TLab (_, _, pat1) -> 
      check_pattern_linear_and_get_variables pat1
  | TAtt (_, _, pat1) -> 
      check_pattern_linear_and_get_variables pat1
  | TCat (fi, pat1, pat2) -> 
      let xs1 = check_pattern_linear_and_get_variables pat1 in
      let xs2 = check_pattern_linear_and_get_variables pat2 in
      if Sortedlist.isect compare xs1 xs2 <> [] then 
	raise (Ill_formed_pattern (fi, "nonlinear"))
      else Sortedlist.merge compare xs1 xs2
  | TAs (fi, x, pat1) ->
      let xs = check_pattern_linear_and_get_variables pat1 in
      if Sortedlist.mem compare x xs then
	raise (Ill_formed_pattern (fi, "nonlinear"))
      else Sortedlist.merge compare [x] xs
  | TUnion (fi, pat1, pat2) 
  | TUnionF (fi, pat1, pat2) ->
      let xs1 = check_pattern_linear_and_get_variables pat1 in
      let xs2 = check_pattern_linear_and_get_variables pat2 in
      if Sortedlist.compare compare xs1 xs2 <> 0 then 
	raise (Ill_formed_pattern (fi, "nonlinear"))
      else xs1
  | TClos (fi, pat1) ->
      let xs = check_pattern_linear_and_get_variables pat1 in
      if xs <> [] then
	raise (Ill_formed_pattern (fi, "nonlinear"))
      else []
  | TClos1 (fi, pat1) ->
      let xs = check_pattern_linear_and_get_variables pat1 in
      if xs <> [] then
	raise (Ill_formed_pattern (fi, "nonlinear"))
      else []
  | TSubst (fi, pat1, x, pat2) ->
      let xs1 = check_pattern_linear_and_get_variables pat1 in
      let xs2 = check_pattern_linear_and_get_variables pat2 in
      Sortedlist.merge compare (Sortedlist.diff compare xs1 [x]) xs2
  | TTyAs _
  | TRule _ 
  | TApp _ ->
      assert false	

let check_pattern_linear pat =
  ignore(check_pattern_linear_and_get_variables pat)

let rec check_filter_linear r =
  match r with
  | TVar _
  | TBase _
  | TSingle _
  | TEmpty _ 
  | TNone _ 
  | TAttRem _ ->
      ()
  | TUnion(_, r1, r2) 
  | TUnionF(_, r1, r2) 
  | TCat(_, r1, r2) -> 
      check_filter_linear r1;
      check_filter_linear r2
  | TClos(_, r1) 
  | TClos1(_, r1) 
  | TLab (_, _, r1) 
  | TAtt (_, _, r1) -> 
      check_filter_linear r1
  | TRule(_, p, _, _) ->
      check_pattern_linear p
  | TTyAs _
  | TAs _ 
  | TSubst _ 
  | TApp _ ->
      assert false

(* desugarring attributes *)

(* Note: The following functions always terminate since all recursive
   type names must appear within labels. *)

let rec check_attr_dup t =
  match t with
  | TVar(fi, s) -> 
      check_attr_dup (Ctx.lookup_tydef fi s) 
  | TBase _ 
  | TSingle _
  | TLab _
  | TEmpty _ 
  | TNone _ ->
      Label.empty, false
  | TAttRem _ ->      
      Label.empty, true
  | TCat (fi, t1, t2) -> 
      let c1, b1 = check_attr_dup t1 in
      let c2, b2 = check_attr_dup t2 in
      if (b1 && b2) || (Label.overlapping c1 c2) then
	raise (Ill_formed_type(fi, "duplicated attributes"))
      else
	Label.union c1 c2, (b1 || b2)
  | TTyAs (_, _, t1)
  | TClos (_, t1) | TClos1 (_, t1) | TAs (_, _, t1) | TRule(_, t1, _, _) ->
      check_attr_dup t1
  | TAtt(fi, nset, _) ->
      eval_nset fi nset, false
  | TUnion(_, t1, t2) 
  | TUnionF(_, t1, t2) -> 
      let c1, b1 = check_attr_dup t1 in
      let c2, b2 = check_attr_dup t2 in
      Label.union c1 c2, (b1 || b2)
  | TSubst (fi, t1, x, t2) -> 
      let c1, b1 = check_attr_dup t1 in
      let c2, b2 = check_attr_dup t2 in
      if not(Label.is_empty c2) || b2 then (* XXX: More flexibility? *)
	raise (Ill_formed_type(fi, "substitute type with attributes"));
      c1, b1
  | TApp _ -> 
      assert false

let rec contains_atts t =
  match t with
  | TVar(fi, s) -> 
      contains_atts (Ctx.lookup_tydef fi s)
  | TBase _ 
  | TSingle _
  | TLab _
  | TEmpty _ 
  | TNone _ -> 
      false
  | TCat (_, t1, t2) | TUnion(_, t1, t2) | TUnionF(_, t1, t2) 
  | TSubst(_, t1, _, t2) ->
      (contains_atts t1 || contains_atts t2)
  | TClos (_, t1) | TClos1 (_, t1) | TRule (_, t1, _, _) -> 
      contains_atts t1
  | TAtt(fi, _, _) 
  | TAttRem fi ->
      true
  | TTyAs (_, x, t1) 
  | TAs (_, x, t1) ->
      contains_atts t1
  | TApp _ ->
      assert false

let rec extract_atts t =
  match t with
  | TVar(fi, s) -> 
      extract_atts (Ctx.lookup_tydef fi s)
  | TBase _ 
  | TSingle _
  | TLab _
  | TEmpty _ 
  | TNone _ -> 
      [], t
  | TCat (fi, _, _)
  | TClos (fi, _)
  | TClos1 (fi, _) -> 
      if contains_atts t then
	raise (Ill_formed_type(fi, "Attributes under repetition/concatenation under repetition"));
      [], t
  | TAtt(fi, nset, t1) ->
      [(eval_nset fi nset, t1)], TEmpty fi
  | TAttRem fi ->
      raise (Ill_formed_type(fi, "Attribute remainder under repetition"))
  | TUnion(fi, t1, t2) ->
      let a1, e1 = extract_atts t1 in
      let a2, e2 = extract_atts t2 in
      a1 @ a2, TUnion(fi, e1, e2)
  | TUnionF(fi, t1, t2) -> 
      let a1, e1 = extract_atts t1 in
      let a2, e2 = extract_atts t2 in
      a1 @ a2, TUnionF(fi, e1, e2)
  | TTyAs (fi, x, t1) ->
      let a1, e1 = extract_atts t1 in
      a1, TTyAs(fi, x, e1)
  | TAs (fi, x, t1) ->
      let a1, e1 = extract_atts t1 in
      a1, TAs(fi, x, e1)
  | TRule (fi, t1, exp, i1) ->
      let a1, e1 = extract_atts t1 in
      a1, TRule(fi, e1, exp, i1)
  | TSubst (fi, t1, x, t2) ->
      extract_atts t1 (* XXX: really OK? *)
  | TApp _ ->
      assert false

let rec make_rep1 htl =
  match htl with
    [] -> Htype.epsilon
  | [ht] -> ht
  | ht :: htl -> 
      Htype.alt [ht; Htype.seq [Htype.alt [ht; Htype.epsilon]; make_rep1 htl]]

let rec desug t xs ys eli =
  match t with
  | TVar(fi, "Any") when xs = [] && ys = [] -> 
      Htype.any
  | TVar(fi, s) -> 
      desug (Ctx.lookup_tydef fi s) xs ys eli
  | TBase(_, b) -> 
      Htype.base b xs ys
  | TSingle(_, b) -> 
      Htype.single b xs ys
  | TEmpty _ -> 
      Htype.epsilon
  | TLab(fi, nset, t) -> 
      let s = eval_nset fi nset in
      Htype.elm s (desug_top t) xs ys
  | TAtt(fi, nset, t1) -> 
      let s = eval_nset fi nset in
      let ht = desug_top t1 in
      if Label.is_finite s then
	Htype.alt
	  (List.map
	     (fun (p, l) -> Htype.attrep (Label.label p l) ht xs)
	     (Label.elt s))
      else
	raise (Ill_formed_type (fi, "single-attribute with infinite label set"))
  | TAttRem fi ->
      Htype.alt [Htype.epsilon; Htype.attrep eli (desug_top (TVar(fi, "AnyAttrContent"))) xs]
  | TCat(_, t1, t2) -> 
      Htype.seq [desug t1 xs ys eli; desug t2 xs ys eli]
  | TUnion(_, t1, t2) -> 
      Htype.alt [desug t1 xs ys eli; desug t2 xs ys eli]
  | TUnionF(_, t1, t2) -> 
      Htype.alt [desug t1 xs ys eli; Typeop.diff [] (desug t2 xs ys eli) (desug t1 xs ys eli)]
  | TClos(_, t) -> 
      let a, e = extract_atts t in
      Htype.seq
	(List.map
	   (fun (s, t') -> 
	     Htype.alt [Htype.attrep s (desug_top t') xs; Htype.epsilon])
	   a @
	 (match e with TEmpty _ -> [] | _ -> [Htype.rep (desug e xs ys eli)]))
  | TClos1(_, t) -> 
      let a, e = extract_atts t in
      let l =
	(List.map
	   (fun (s, t') -> 
	     Htype.attrep s (desug_top t') xs) a @
	 (match e with
	 | TEmpty _ -> [] 
	 | _ -> 
	     let e' = desug e xs ys eli in
	     [Htype.seq [e'; Htype.rep e']])) in
      make_rep1 l
  | TNone _ -> 
      Htype.empty
  | TTyAs (fi, y, t) ->
      let ht = desug t xs (Sortedlist.merge compare [y] ys) eli in
      if not(Typeop.subtype ht Htype.any_elm) then
	raise (Ill_formed_type(fi, "Type variable can quantify over 1-width types with no attributes."));
      ht
  | TAs (_, x, t) ->
      desug t (Sortedlist.merge compare [x] xs) ys eli
  | TRule (_, t1, _, i1) ->
      Htype.exe i1 (desug t1 xs ys eli)
  | TSubst (_, t1, z, t2) ->
      let r1 = desug t1 xs ys eli in
      let r2 = desug t2 xs ys eli in
      Typeop.subst r1 z r2
  | TApp _ ->
      assert false
	
and desug_top t =
  let t' = t(*strip_finfo t*) in
  try
    Tbl.find desug_tbl t'
  with Not_found ->
    let n = new_name() in
    Tbl.add desug_tbl t' n;
    let c, _ = check_attr_dup t in
    let eli = Label.compl c in
    let ht = desug t [] [] eli in
    Htype.define_name n ht;
    n

let desug t = 
  if !Pref.typinglog then Format.printf "@[<2>desugarring types...@?";
  Timer.start timer_desugtype;
  let c, _ = check_attr_dup t in
  let eli = Label.compl c in
  let ht = desug t [] [] eli in
  Timer.stop timer_desugtype;
  if !Pref.typinglog then Format.printf "done@]@.";
  ht


