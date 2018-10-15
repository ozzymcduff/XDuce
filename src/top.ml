open Syn
open List
open Format
open Ctx

let timer_check = Timer.create "top-check"
let timer_eval = Timer.create "top-eval"
let timer_patdefs = Timer.create "top-patdefs"

let top =
    { top_tydefs = [];
      top_fundefs = [];
      top_valdefs = [];
      top_bltins = [];
      top_caltype = [];
      top_nsdefs = [];
    }

(* type well-formedness check *)

let check_tydefs () =		
  if !Pref.showphase then printf "Checking type definitions@.";
  Desugtype.wf_type ()

(* typecheck fundefs *)

let check_fundefs tenv fundefs =		
  iter (fun ((fi, name, _, _, _, _) as fundef) ->
    if !Pref.showphase then
      printf "Checking %s@." name;
    Timer.start timer_check;
    Check.check_fundef tenv fundef;
    Timer.stop timer_check)
    fundefs

(* typecheck valdefs *)

let check_valdefs tenv valdefs =
  List.fold_left
    (fun tenv (fi,pat,cell,body) ->
      if !Pref.showphase then
	printf "Checking value def at %s@." (Finfo.finfo_to_string fi);
      Timer.start timer_check;
      let bodyty = Check.check tenv body in
      let xs = Synutil.dom_of_typ pat in
      let patty = Desugtype.desug pat in
      Check.check_exhaustive fi bodyty [(pat, body, cell)];
      Check.compile_optimize_and_register_pattern [(pat, body, cell)] patty;
      let tenv = Check.infer_pat fi xs tenv bodyty patty in
      Timer.stop timer_check;
      tenv)
    tenv valdefs 

(* test type operations *)

let process_caltype c =
  if !Pref.showphase then
    printf "Processing caltypes@.";
  match c with
  | ("disp", [ty1]) ->
      let ht1 = Desugtype.desug ty1 in
      printf "result: %a@."
	Htype.print ht1
  | ("isect", [ty1; ty2]) ->
      let ht1 = Desugtype.desug ty1 in
      let ht2 = Desugtype.desug ty2 in
      printf "%a & %a@."
	Htype.print ht1 
	Htype.print ht2;
      let ht3 = Typeop.isect (fun (xs2, _) (_, ys1) -> (xs2, ys1)) ht1 ht2 in
      printf "result: %a@."
	Htype.print ht3
  | ("diff", [ty1; ty2]) ->
      let ht1 = Desugtype.desug ty1 in
      let ht2 = Desugtype.desug ty2 in
      printf "%a \\ %a@."
	Htype.print ht1 
	Htype.print ht2;
      let ht3 = Typeop.diff [] ht1 ht2 in
      printf "result: %a@."
	Htype.print ht3;
      ()
  | ("sub", [ty1; ty2]) ->
      let ht1 = Desugtype.desug ty1 in
      let ht2 = Desugtype.desug ty2 in
      printf "%a <: %a@."
	Htype.print ht1 
	Htype.print ht2;
      let b = Typeop.subtype ht1 ht2 in
      printf "result: %b@." b
  | ("inf", [ty1; ty2]) ->
      let ht1 = Desugtype.desug ty1 in
      let ht2 = Desugtype.desug ty2 in
      printf "%a |- %a@."
	Htype.print ht1 
	Htype.print ht2;
      let xs = Synutil.dom_of_typ ty2 in
      let res = Typeop.infer_pat xs ht1 ht2 in
      printf "result: @.";
      List.iter
	(fun (x, ht) ->
	  printf "  %s : %a@."
	    x Htype.print ht)
	res
  | _ ->
      assert false


(* type checking *)

let type_check top =
  (* type check valdefs *)
  let tenv = Env.empty in
  let tenv = check_valdefs tenv top.top_valdefs in
  (* type check fundefs *)
  let _ = check_fundefs tenv top.top_fundefs in
  ()

(* evaluate valdefs *)

let eval_valdef valdef =
  let (fi,pat,cell,body) = valdef in
  if !Pref.showphase then
    printf "Evaluating value def at %s@." (Finfo.finfo_to_string fi);
  Timer.start timer_eval;
  let venv = Env.empty in
  let va = Eval.eval venv body in
  let venv = 
    Eval.eval_application fi venv [(pat, cell)] [va] in
  Timer.stop timer_eval;
  Env.iter (fun x va -> Ctx.add_valdef x va) venv

(* evaluation *)

let evaluate valdefs =
  List.iter eval_valdef valdefs

(* process the whole top-levels *)

let add_predefined ctx =
  let i = Finfo.bogus () in
  let string = TBase(i, Base.BTString) in
  let int = TBase(i, Base.BTInt) in
  let float = TBase(i, Base.BTFloat) in
  let base = TUnion(i, string, TUnion (i, int, float)) in
  let lab = TLab(i, NAnyName, TVar (i, "Any")) in
  let att = TAtt(i, NAnyName, TClos(i, string)) in
  let lab_base = TUnion(i, lab, base) in
  let lab_att_base = TUnion(i, TUnion(i, lab, att), base) in
  let anyattrs = TClos(i, att) in
  Ctx.add_tydef "Any" (i, TClos(i, lab_att_base));
  Ctx.add_tydef "AnyElm" (i, lab_base);
  Ctx.add_tydef "AnyElms" (i, TClos(i, lab_base));
  Ctx.add_tydef "AnyAttrs" (i, anyattrs);
  Ctx.add_tydef "None" (i, TNone i);
  Ctx.add_tydef "AnyAttrContent" (i, TClos(i, string));
  Ctx.add_nsdef "emptyprefix" (i, Ns.empty);    
  Ctx.add_nsdef "" (i, Ns.empty)    

let process_top (top : top) =
  add_predefined ();
  List.iter 
    (fun (fi, name, tparams, pairs, resty, body) -> 
      add_fundef name (fi, tparams, pairs, resty, body))
    top.top_fundefs;
  List.iter
    (fun (fi, name, typarams, argty, resty, f) -> add_bltin name (fi, typarams, argty, resty, f)) 
    top.top_bltins;
  List.iter (fun (fi, name, ty) -> Ctx.add_tydef name (fi, ty)) top.top_tydefs;
  List.iter 
    (fun (fi, prefix, uri) -> 
      Ctx.add_nsdef prefix (fi, Ns.of_uri uri)) 
    top.top_nsdefs;
  (* check well-formedness *)
  check_tydefs ();
  (* test type operations *)
  List.iter process_caltype top.top_caltype;
  (* type checking *)
  type_check top;
  (* evaluation *)
  if not(!Pref.noeval) then begin
    ignore(evaluate top.top_valdefs);
  end;
  ()



