open List
open Syn
open Finfo
open Base
open Format
open Ctx

let timer_subtyping = Timer.create "subtyping"
let timer_header = Timer.create "check_function_header"

(* type environments *)

type tenv = Htype.ht Env.t

(* compiled patterns *)

let ptbl = Hashtbl.create 121
let rtbl = Hashtbl.create 121
let ctr_id = Counter.make()
let new_id() = Counter.next ctr_id

(* types of patterns *)

let ty_of_pat pat = Desugtype.desug pat 

let union_env env1 env2 =
  Env.fold
    (fun key ty1 env2 ->
      try
	let ty2 = Env.find key env2 in
	Env.add key (Htype.alt [ty1; ty2]) env2
      with
	Not_found ->
	  Env.add key ty1 env2)
    env1 env2

let rec env_of_pat tenv = function
  | TVar _ | TBase _ | TSingle _ | TEmpty _ | TNone _ | TAttRem _
  | TClos _ | TClos1 _ ->
      tenv
  | TTyAs (fi, x, pat) ->
      env_of_pat tenv pat
  | TAs (fi, x, pat) ->
      env_of_pat (Env.add x (ty_of_pat pat) tenv) pat
  | TLab (_, _, pat1) -> 
      env_of_pat tenv pat1
  | TAtt (_, _, pat1) -> 
      env_of_pat tenv pat1
  | TCat (_, pat1, pat2) -> 
      env_of_pat (env_of_pat tenv pat1) pat2 
  | TUnion (_, pat1, pat2) 
  | TUnionF (_, pat1, pat2) ->
      union_env (env_of_pat tenv pat1) (env_of_pat tenv pat2)
  | TSubst (_, pat1, x, pat2) ->
      let tenv1 = env_of_pat Env.empty pat1 in
      let ht2 = ty_of_pat pat2 in
      let tenv1' = Env.map (fun ht -> Typeop.subst ht x ht2) tenv1 in
      Env.fold Env.add tenv1' tenv 
  | TRule _ 
  | TApp _ ->
      assert false

let rec replace_function_call_rules r =
  match r with
  | TVar _ ->
      r
  | TApp (fi, f, args) ->
      let (_, params, _, _) = Ctx.lookup_fundef fi f in	(* XXX: type params? *)
      if List.length args != List.length params then
	failwith "Function arguments too many or too few";
      if List.length (List.find_all (fun p -> p = None) args) != 1 then
	failwith "Too many or few targets in the function call filter";
      let i = Listutil.index (fun p -> p = None) args in
      let (t, _) = List.nth params i in
      let x = Syn.new_name() in
      let i = Syn.next_filter_id() in
      let args =
	List.map (function None -> EVar (fi, x) | Some e -> e) args in
      TRule(fi, TAs(fi, x, t), EApp(fi, f, args), i)
  | TUnion(fi, r1, r2)  ->
      TUnion(fi, replace_function_call_rules r1, 
	     replace_function_call_rules r2)
  | TUnionF(fi, r1, r2) ->
      TUnionF(fi, replace_function_call_rules r1, 
	      replace_function_call_rules r2)
  | TCat(fi, r1, r2) ->
      TCat(fi, replace_function_call_rules r1, 
	   replace_function_call_rules r2)
  | TClos(fi, r1) ->
      TClos(fi, replace_function_call_rules r1)
  | TClos1(fi, r1) ->
      TClos1(fi, replace_function_call_rules r1)
  | TRule _ -> 
      r
  | TAs (fi, x, r) -> 
      TAs(fi, x, replace_function_call_rules r)
  | TAtt (fi, l, r) ->
      TAtt(fi, l, replace_function_call_rules r)
  | TLab (fi, l, r) ->
      TLab(fi, l, replace_function_call_rules r)
  | TEmpty _ | TSingle (_, _) | TBase (_, _) | TNone _ | TAttRem _ ->
      r
  | TTyAs _ 
  | TSubst _ ->
      assert false

(* subtyping *)

exception Subtyping of finfo * Htype.ht * Htype.ht * Typath.t

let subtype_ignoring_vars fi ign t1 t2 =
  if !Pref.showphase then Format.printf "@[<2>subtype checking at %s...@?" (finfo_to_string fi);
  let t3 = Typeop.diff ign t1 t2 in
  if !Pref.showphase then Format.printf "done@]@.";
  if not(Htype.is_empty t3) then 
    let va = Htype.sample t3 in
    let x = Patmatch.construct t2 in
    match Patmatch.validate x va with
    | `Succeed _ -> assert false
    | `Fail w -> raise (Subtyping(fi, t1, t2, w))

let subtype fi t1 t2 = subtype_ignoring_vars fi [] t1 t2

let isect_and_subtype fi t1 t2 t3 =
  if !Pref.showphase then Format.printf "@[<2>computing intersection at %s...@?" (finfo_to_string fi);
  let t4 = Typeop.isect (fun (xs2, ys2) (_, ys1) -> (xs2, Sortedlist.merge compare ys1 ys2)) t1 t2 in
  if !Pref.showphase then Format.printf "done@]@.";
  if !Pref.showphase then Format.printf "@[<2>subtype checking at %s...@?" (finfo_to_string fi);
  let res = Typeop.subtype t4 t3 in
  if !Pref.showphase then Format.printf "done@]@.";
  res

(* type inference for pattern matching *)

let infer_pat fi xs tenv ty pat =
  if !Pref.showphase then Format.printf "type inferece:@.";
  let m = Typeop.infer_pat xs ty pat in
  if !Pref.showphase then Format.printf "done@]@.";
  List.fold_right (fun (x, t) tenv -> Env.add x t tenv) m tenv

(* obtain the union of the "top" labels of a given type *)

let rec top_level_label env ht =
  match ht.Htype.def with
  | Htype.Elm (l, _, _, _) -> 
      l
  | Htype.Alt hts -> 
      List.fold_right
	(fun ht' l -> Label.union (top_level_label env ht') l) 
	hts Label.empty
  | Htype.Seq hts ->
      List.fold_right
	(fun ht' l -> Label.union (top_level_label env ht') l) 
	hts Label.empty
  | Htype.Rep ht' ->
      top_level_label env ht'
  | Htype.Attrep _ 
  | Htype.Exe _ ->
      Label.empty

(* type checking *)

exception Non_exhaustive of finfo * Htype.ht * clause list * Typath.t
exception Redundant_pattern of finfo
exception Ambiguous_pattern of finfo
exception Wrong_num_arguments of finfo * int * int

let rec check (tenv : tenv) (expr : expr) : Htype.ht =
  match expr with
  | EVar (fi, var_name) -> 
      (try 
	Env.find var_name tenv
      with Not_found ->
	raise (Ctx.Unbound (fi, "variable", var_name)))
  | EBase (_, baseval) -> 
      Htype.single baseval [] []
  | EEmpty _ -> 
      Htype.epsilon
  | ELab(fi, p, l, expr1) -> 
      let ty1 = check tenv expr1 in
      let ns = Ctx.lookup_nsdef fi p in
      Htype.elm (Label.label ns l) (Htype.give_unique_name ty1) [] []
  | EAtt(fi, p, l, expr1) -> 
      let ty1 = check tenv expr1 in
      let ns = Ctx.lookup_nsdef fi p in
      Htype.attrep (Label.label ns l) (Htype.give_unique_name ty1) []
  | EAnyLab(_, expr1, expr2, expr3) -> 
      let ty1 = check tenv expr1 in
      subtype (Synutil.finfo_of_expr expr1) ty1 Htype.string;
      let ty2 = check tenv expr2 in
      subtype (Synutil.finfo_of_expr expr1) ty2 Htype.string;
      let ty3 = check tenv expr3 in
      Htype.elm Label.any_label (Htype.give_unique_name ty3) [] []
  | ECopyLab(_, expr1, expr2) -> 
      let ty1 = check tenv expr1 in
      let ty1' = Htype.elm Label.any_label Htype.any_name [] [] in
      subtype (Synutil.finfo_of_expr expr1) ty1 ty1';
      let l = top_level_label [] ty1 in
      let ty2 = check tenv expr2 in
      Htype.elm l (Htype.give_unique_name ty2) [] []
  | ECat(fi, expr1, expr2) ->
      let ty1 = check tenv expr1 in
      let ty2 = check tenv expr2 in
      if Label.overlapping ty1.Htype.adom ty2.Htype.adom then
	raise (Desugtype.Ill_formed_type(fi, "duplicated attributes"))
      else
	Htype.seq [ty1;ty2]
  | EApp(fi, fun_name, exprs) ->
      let typarams, paramtys, resty = 
	if Ctx.is_bltin fun_name then
	  let typarams, paramtys, resty, _ = Ctx.lookup_bltin fi fun_name in
	  let paramtys = List.map Desugtype.desug paramtys in
	  let resty = Desugtype.desug resty in
	  typarams, paramtys, resty
	else
	  let typarams, pat_cell_pairs, resty, _ = Ctx.lookup_fundef fi fun_name in
	  let paramtys = List.map (fun (pat, _) -> ty_of_pat pat) pat_cell_pairs in
	  let resty = Desugtype.desug resty in
	  typarams, paramtys, resty in
      if List.length exprs != List.length paramtys then
	raise (Wrong_num_arguments(fi, List.length exprs, List.length paramtys));
      let argtys = List.map (fun expr -> check tenv expr) exprs in
      List.iter2
	(fun argty paramty -> 
	  subtype_ignoring_vars (Synutil.finfo_of_expr expr) typarams argty paramty) 
	argtys paramtys;
      let ms = 
	List.map2 (fun argty paramty -> Typeop.infer_ty typarams argty paramty)
	  argtys paramtys in
      let m = 
	List.fold_right
	  (fun m1 m2 -> List.map2 (fun (x, ht1) (_, ht2) -> (x, Htype.alt [ht1; ht2])) m1 m2)
	  ms (List.map (fun typaram -> (typaram, Htype.empty)) typarams) in
      List.fold_right
	(fun (x, ht) resty -> Typeop.subst resty x ht)
	m resty
  | ESeq (_, expr1, expr2) ->
      let _ = check tenv expr1 in
      check tenv expr2
  | EFilter (fi, expr, filter, idref) ->
      let filter = replace_function_call_rules filter in
      let argty = check tenv expr in
      let resty = infer_compile_filter fi tenv argty filter idref in
      resty
  | ECast (fi, ty, expr, _, idref, elsecl) ->
      let argty = check tenv expr in
      if not(!Pref.noeval) then begin
	let p = Desugtype.desug ty in
	let p = Patmatch.construct p in
	let id = new_id() in
	Hashtbl.add ptbl id p;
	idref := id;
      end;
      let ty = Desugtype.desug ty in
      begin match elsecl with
	Some elseexpr -> 
	  let elsety = check tenv elseexpr in
	  Htype.alt [ty; elsety]
      | None ->
	  ty
      end
  | ETry (fi, expr1, x, expr2) ->
      Htype.alt
	[check (Env.add x Htype.any tenv) expr2;
	 check tenv expr1]
  | ERaise (fi, expr1) ->
      ignore(check tenv expr1);
      Htype.empty

and check_exhaustive fi argty clauses =
  let patty = Htype.alt (map (fun (pat, _, _) -> ty_of_pat pat) clauses) in
  if !Pref.showphase then Format.printf "exhaustiveness check:@.";
  try 
    subtype fi argty patty
  with Subtyping(_, _, _, w) ->
    raise (Non_exhaustive(fi, argty, clauses, w))

and compile_optimize_and_register_pattern clauses argty =
  List.iter 
    (fun (pat, _, cell) ->
      if !Pref.showphase then Format.printf "pattern optimization at %s...@?" (finfo_to_string (Synutil.finfo_of_typ pat));
      let p = Desugtype.desug pat in
      let y = Patmatch.construct p in
      if !Pref.showphase then Format.printf "done@.";
      let id = new_id() in
      Hashtbl.add ptbl id y;
      cell := id)
    clauses

and infer_compile_filter fi tenv t r idref =
  Desugtype.check_filter_linear r;
  let id_to_dom = Synutil.filter_id_to_dom r in
  let id_to_body = Synutil.filter_id_to_body r in
  let id_to_finfo = Synutil.filter_id_to_finfo r in
  if !Pref.showphase then Format.printf "exhaustiveness check:@.";
  let r = Desugtype.desug r in
  if Htype.reachable_vars2 r <> [] then
    raise (Desugtype.Ill_formed_pattern (fi, "This filter/pattern contains a type variable."));
  (try 
    subtype fi t r
  with Subtyping(_, _, _, w) ->
    raise (Non_exhaustive(fi, t, [], w)));
  if !Pref.showphase then Format.printf "filter inference:@.";
  let p = Patmatch.construct r in
  let id = new_id() in
  Hashtbl.add rtbl id (p, id_to_dom, id_to_body);  
  idref := id;
  let r = Typeop.isect (fun (xs2, _) (_, ys1) -> (xs2, ys1)) r t in
  let r = Htype.elim_empty r in
  if !Pref.typinglog then begin
    printf "specialized filter: %a@." Htype.print r
  end;
  let id_to_tenv =
    List.map
      (fun (id, vars) ->
	let ht = Typeop.extract_for_id id r in
	if Htype.is_empty ht then
	  raise (Redundant_pattern(List.assq id id_to_finfo));
	if !Pref.typinglog then begin
	  printf "filter: %d : %a@." id Htype.print ht
	end;
	(id, List.map (fun var -> (var, Typeop.extract_for_var var ht)) vars))
      id_to_dom in
  let id_to_type = 
    List.map 
      (fun (id, m) -> 
	(id, 
	 check
	   (List.fold_right (fun (var, t) tenv -> Env.add var t tenv) m tenv)
	   (List.assq id id_to_body)))
      id_to_tenv in
  Typeop.recon_filter_type id_to_type r

let check_fundef tenv (fi, name, typarams, pat_cell_pairs, resty, body)  =
  Timer.start timer_header;
  List.iter 
    (fun (pat, cell) ->
      let ty = Desugtype.desug pat in
      if Typeop.is_marking_ambiguous typarams ty then begin
	Finfo.print (Synutil.finfo_of_typ pat);
	Format.eprintf "Warning: This parameter is marking-ambiguous.@."
      end;
      compile_optimize_and_register_pattern [(pat, body, cell)] ty)
    pat_cell_pairs;			(* passing body as dummy *)
  Timer.stop timer_header;
  let tenv = 
    List.fold_right
      (fun (pat, _) tenv -> env_of_pat tenv pat)
      pat_cell_pairs tenv in
  let resty = Desugtype.desug resty in
  let bodyty = check tenv body in
  subtype fi bodyty resty

