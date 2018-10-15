open Syn
open Finfo

(* label with attributes *)

let any_type = 
  TVar(bogus(),"Any")

let anyattr_type = 
  TVar(bogus(),"AnyAttrs")

let label_va ?(ns = Ns.empty) lab ?(attr = []) content =
  attr @ [MLab(ns, lab, content)]

(* other abbreviations *)

let true_va =
  label_va Sym.truel []
    
let false_va =
  label_va Sym.falsel []

let true_ty =
  TLab (bogus(), NQName("emptyprefix", Sym.truel), TEmpty(bogus()))
    
let false_ty =
  TLab (bogus(), NQName("emptyprefix", Sym.falsel), TEmpty(bogus()))

(* file info *)

let finfo_of_expr = function
  | EVar (fi, _)
  | EBase (fi, _)
  | EEmpty fi
  | ELab (fi, _, _, _)
  | EAnyLab (fi, _, _, _)
  | ECopyLab (fi, _, _)
  | ECat (fi, _, _)
  | EApp (fi, _, _)
  | ESeq (fi, _, _)
  | EFilter (fi, _, _, _)
  | ECast (fi, _, _, _, _, _)
  | ETry (fi, _, _, _)
  | ERaise (fi, _)
  | EAtt (fi, _, _, _) -> fi

let finfo_of_typ = function
    TVar (fi, _)
  | TBase (fi, _)
  | TSingle (fi, _)
  | TEmpty fi
  | TLab (fi, _, _)
  | TCat (fi, _, _)
  | TTyAs (fi, _, _)
  | TAs (fi, _, _)
  | TUnion (fi, _, _)
  | TUnionF (fi, _, _)
  | TClos (fi, _)
  | TClos1 (fi, _)
  | TNone fi
  | TAtt (fi, _, _)
  | TAttRem fi
  | TApp (fi, _, _)
  | TSubst (fi, _, _, _) 
  | TRule (fi, _, _, _) -> fi

(* operations on types *)

let union_types tys =
  match tys with
    [] -> TNone (bogus())
  | ty :: tys -> List.fold_left (fun ty1 ty2 -> TUnion(bogus(),ty1,ty2)) ty tys

let seq_types tys =
  match tys with
    [] -> TEmpty (bogus())
  | ty :: tys -> List.fold_left (fun ty1 ty2 ->	TCat(bogus(),ty1,ty2)) ty tys

(* variables appearing in patterns *)

let rec dom_of_typ = function
  | TAs (_, x, r1) ->
      Nonduplist.merge (=) [x] (dom_of_typ r1)
  | TEmpty _ | TVar _ | TBase _ | TSingle _ | TAttRem _ 
  | TNone _ ->
      []
  | TCat (_, r1, r2) 
  | TUnion (_, r1, r2) 
  | TUnionF(_, r1, r2) 
  | TSubst (_, r1, _, r2) ->
      Nonduplist.merge (=) (dom_of_typ r1) (dom_of_typ r2)
  | TTyAs (_, _, r1) 
  | TLab (_, _, r1) 
  | TAtt (_, _, r1) 
  | TClos (_, r1) 
  | TClos1 (_, r1) ->
      dom_of_typ r1
  | TRule _ 
  | TApp _ ->
      assert false

(* filter properties *)

let rec filter_id_to_dom asm r =
  match r with
  | TUnion(_, r1, r2)  | TUnionF(_, r1, r2) | TCat(_, r1, r2) ->
      Sortedlist.merge (fun (i1, _) (i2, _) -> compare i1 i2)
	(filter_id_to_dom asm r1) (filter_id_to_dom asm r2)
  | TTyAs (_, _, r1) 
  | TClos(_, r1) 
  | TClos1(_, r1) 
  | TAtt (_, _, r1) 
  | TLab (_, _, r1) 
  | TSubst (_, r1, _, _) ->
      filter_id_to_dom asm r1
  | TRule(_, p, _, i) -> 
      [(i, dom_of_typ p)]
  | TVar(fi, x) ->
      if List.mem x asm then [] else
      filter_id_to_dom (x :: asm) (Ctx.lookup_tydef fi x)
  | TAs _ -> 
      assert false
  | TAttRem _ | TEmpty _ | TSingle (_, _) | TBase (_, _) | TNone _ ->
      []
  | TApp _ -> 
      assert false

let filter_id_to_dom r = filter_id_to_dom [] r

let rec filter_id_to_body asm r =
  match r with
  | TUnion(_, r1, r2) | TUnionF(_, r1, r2) | TCat(_, r1, r2) ->
      Sortedlist.merge (fun (i1, _) (i2, _) -> compare i1 i2)
	(filter_id_to_body asm r1) (filter_id_to_body asm r2)
  | TTyAs (_, _, r1) 
  | TClos(_, r1) 
  | TClos1(_, r1) 
  | TAtt (_, _, r1) 
  | TLab (_, _, r1) 
  | TSubst (_, r1, _, _) ->
      filter_id_to_body asm r1
  | TRule(_, _, e, i) -> 
      [(i, e)]
  | TVar(fi, x) ->
      if List.mem x asm then [] else
      filter_id_to_body (x :: asm) (Ctx.lookup_tydef fi x)
  | TAs _ -> 
      assert false
  | TAttRem _ | TEmpty _ | TSingle (_, _) | TBase (_, _) | TNone _ ->
      []
  | TApp _ -> 
      assert false

let filter_id_to_body r = filter_id_to_body [] r

let rec filter_id_to_finfo asm r =
  match r with
  | TUnion(_, r1, r2) | TUnionF(_, r1, r2) | TCat(_, r1, r2) ->
      Sortedlist.merge (fun (i1, _) (i2, _) -> compare i1 i2)
	(filter_id_to_finfo asm r1) (filter_id_to_finfo asm r2)
  | TClos(_, r1) 
  | TClos1(_, r1) 
  | TAtt (_, _, r1) 
  | TLab (_, _, r1) 
  | TSubst (_, r1, _, _) ->
      filter_id_to_finfo asm r1
  | TRule(fi, _, _, i) -> 
      [(i, fi)]
  | TVar(fi, x) ->
      if List.mem x asm then [] else
      filter_id_to_finfo (x :: asm) (Ctx.lookup_tydef fi x)
  | TTyAs _ 
  | TAs _ -> 
      assert false
  | TAttRem _ | TEmpty _ | TSingle (_, _) | TBase (_, _) | TNone _ ->
      []
  | TApp _ -> 
      assert false

let filter_id_to_finfo r = filter_id_to_finfo [] r

(* string internalization *)

let vartbl : (string, string) Hashtbl.t = Hashtbl.create 121

let intern str =
  try Hashtbl.find vartbl str 
  with Not_found ->
    Hashtbl.add vartbl str str;
    str

(* printers *)

open List
open Format
open Base

(* variables *)

let print_var ff x = fprintf ff "x%d" x

(* types *)

let rec print_nset ff = function
  | NQName ("", s) ->
      fprintf ff "%a" Sym.print s
  | NQName (p, s) ->
      fprintf ff "%s:%a" p Sym.print s
  | NNSName p ->
      fprintf ff "%s:~" p
  | NAnyName ->
      fprintf ff "~"
  | NOr (ns1, ns2) ->
      fprintf ff "%a|%a" print_nset ns1 print_nset ns2
  | NDiff (ns1, ns2) ->
      fprintf ff "%a\\%a" print_nset ns1 print_nset ns2

let rec print_ty ff = function 
    orTy -> 
      fprintf ff "@[%a@]" print_orTy orTy

and print_orTy ff = function
    TUnion(_, catTy, orTy) -> 
      fprintf ff "%a@ |@ %a" print_catTy catTy print_orTy orTy
  | catTy -> 
      fprintf ff "@[%a@]" print_catTy catTy

and print_catTy ff = function
    TCat(_, atomTy, catTy) ->
      fprintf ff "%a,@ %a" print_atomTy atomTy print_catTy catTy
  | atomTy ->
      fprintf ff "@[%a@]" print_atomTy atomTy

and print_atomTy ff = function
  | TVar (_, s) ->
      fprintf ff "%s" s
  | TBase (_, basety) ->
      fprintf ff "%s" (string_of_basety basety)
  | TSingle (_, baseval) ->
      fprintf ff "%s" (string_of_baseval baseval)
  | TClos (_, atomTy) ->
      fprintf ff "@[%a@]*" print_atomTy atomTy
  | TClos1 (_, atomTy) ->
      fprintf ff "@[%a@]+" print_atomTy atomTy
  | TNone _ ->
      fprintf ff "^" 
  | TLab(_, l, ty) ->
      fprintf ff "@[%a[@[%a@]]@]" print_nset l print_empTy ty; 
  | TAtt(_, l, ty) ->
      fprintf ff "@[@@%a[@[%a@]]@]" print_nset l print_empTy ty; 
  | TSubst(_, r1, x, r2) ->
      fprintf ff "@[@[%a@]{%s -> %a}@]" print_ty r1 x print_ty r2
  | TTyAs(_, x, r1) ->
      fprintf ff "@[tval %s as %a@]" x print_ty r1
  | TAs _
  | TRule _ 
  | TApp _ ->
      assert false
  | ty ->
      fprintf ff "(@[%a@])" print_empTy ty

and print_empTy ff = function
  | TEmpty _ ->
      fprintf ff ""
  | ty ->
      fprintf ff "@[%a@]" print_ty ty

(* type definitions *)

let print_tydefs ff tydefs =
  Hashtbl.iter (fun s (_, ty) -> 
    fprintf ff "@[type %s =@;<1 2>%a@]@." s print_ty ty)
    tydefs

(* values *)

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
  | MBase baseval ->
      fprintf ff "@[%s@]" (string_of_baseval baseval)
  | MLab (ns, s, va1) -> 
      fprintf ff "@[%a:%a[@[%a@]]@]" 
	Sym.print ns Sym.print s print_elem_seq va1
  | MAtt (ns, s, va1) -> 
      fprintf ff "@[@@%a:%a[@[%a@]]@]" 
	Sym.print ns Sym.print s print_elem_seq va1
  | MWs s ->
      fprintf ff "@[\"%s\"@]" s

(* contexts *)

let print_tydefs ff tydefs =
  Hashtbl.iter (fun name (_, ty) ->
    fprintf ff "type %s = @[<2>%a@]@]@." name print_ty ty)
    tydefs

