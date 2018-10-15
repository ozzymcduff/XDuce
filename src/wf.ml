open List 
open Sym
open Syn
open Finfo
open Format

(* well-formedness *)

exception Ill_formed of finfo * string * ty
exception Ill_formed_pattern of finfo * ty
exception Ill_formed_internal

let wf_type () =
  let rec disconnected x seen = function
      TVar (_, y) when x = y ->
	raise Ill_formed_internal 
    | TVar (_, y) when mem y seen ->
	seen
    | TVar (fi, y) ->
	let r = Ctx.lookup_tydef fi x in
	disconnected x (y :: seen) r
    | TBase _ 
    | TSingle _ 
    | TEmpty _ 
    | TNone _ 
    | TLab (_, _, _) 
    | TAtt (_, _, _) 
    | TAttRem _ ->
	seen
    | TCat(_, ty1, ty2) 
    | TUnion(_, ty1, ty2) 
    | TUnionF(_, ty1, ty2) ->
	let seen = disconnected x seen ty1 in
	disconnected x seen ty2 
    | TClos (_, ty) 
    | TClos1 (_, ty)
    | TAs (_, _, ty) 
    | TRule (_, ty, _, _) ->
	disconnected x seen ty
    | TApp _ ->
	assert false
  in
  Ctx.iter_tydef
    (fun name (fi, ty) -> 
      try ignore(disconnected name [] ty)
      with Ill_formed_internal ->
	raise (Ill_formed (fi, name, ty)))
  
exception Non_linear_pattern of finfo * ty

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
	raise (Non_linear_pattern (fi, pat))
      else Sortedlist.merge compare xs1 xs2
  | TAs (fi, x, pat1) ->
      let xs = check_pattern_linear_and_get_variables pat1 in
      if Sortedlist.mem compare x xs then
	raise (Non_linear_pattern (fi, pat))
      else Sortedlist.merge compare [x] xs
  | TUnion (fi, pat1, pat2) 
  | TUnionF (fi, pat1, pat2) ->
      let xs1 = check_pattern_linear_and_get_variables pat1 in
      let xs2 = check_pattern_linear_and_get_variables pat2 in
      if Sortedlist.compare compare xs1 xs2 <> 0 then 
	raise (Non_linear_pattern (fi, pat))
      else xs1
  | TClos (fi, pat1) ->
      let xs = check_pattern_linear_and_get_variables pat1 in
      if xs <> [] then
	raise (Non_linear_pattern (fi, pat))
      else []
  | TClos1 (fi, pat1) ->
      let xs = check_pattern_linear_and_get_variables pat1 in
      if xs <> [] then
	raise (Non_linear_pattern (fi, pat))
      else []
  | TRule _ ->
      assert false
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
  | TAs _ ->
      assert false
  | TApp _ ->
      assert false
