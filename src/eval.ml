open Syn
open Base
open Format

exception CastFailed of Finfo.finfo * ty * Typath.t 
exception Evaluation of Finfo.finfo * expr * string
exception EvaluationFunc of Finfo.finfo * string
exception Bltin_error of Finfo.finfo * string * string
exception UserExc of va

(* evaluation *)

let trace_level = ref 0

let print_vas ch vas =
  Printing.print_list (fun () -> fprintf ch ", @ ") (Synutil.print_va ch) vas

let wrap_trace f fun_name args =
  if !Pref.trace || !Pref.tracemore then begin
    let indent = String.make (!trace_level) ' ' in
    if !Pref.trace then begin
      printf "%s[%d] call to %s@." indent (!trace_level) fun_name;
    end else if !Pref.tracemore then begin
      printf "%s[%d] call to %s with %a@." indent (!trace_level) fun_name print_vas args;
    end;
    incr trace_level;
    let res = f() in
    decr trace_level;
    if !Pref.trace then begin
      printf "%s[%d] return from %s@." indent (!trace_level) fun_name;
    end else if !Pref.tracemore then begin
      printf "%s[%d] return from %s with %a@." indent (!trace_level) fun_name Synutil.print_va res;
    end;
    res
  end else
    f()

let rec eval env expr =
  match expr with
  | EVar(fi, var_name) -> 
      (try Env.find var_name env with
        Not_found -> 
	  try Ctx.lookup_valdef fi var_name with
	    Ctx.Unbound _ ->
              raise (Ctx.Unbound (fi, "variable", var_name)))
  | EBase(_, base_val) ->
      [MBase base_val]
  | EEmpty _ ->
      []
  | ELab (fi, p, lab, expr1) ->
      let ns = Ctx.lookup_nsdef fi p in
      let va1 = eval env expr1 in
      [MLab (ns, lab, va1)]
  | EAtt (fi, p, lab, expr1) ->
      let ns = Ctx.lookup_nsdef fi p in
      let va1 = eval env expr1 in
      [MAtt (ns, lab, va1)]
  | EAnyLab (fi, expr1, expr2, expr3) ->
      let va1 = eval env expr1 in
      let va2 = eval env expr2 in
      let va3 = eval env expr3 in
      (match va1, va2 with
        [MBase (BVString p)], [MBase (BVString l)] -> 
	  let ns = Ctx.lookup_nsdef fi p in
	  [MLab (ns, Sym.label l, va3)]
      | _ -> raise (Evaluation (fi, expr, "first and second arguments must be strings")))
  | ECopyLab (fi, expr1, expr2) ->
      let va1 = eval env expr1 in
      let va2 = eval env expr2 in
      (match va1 with
        [MLab (ns, l, _)] -> [MLab (ns, l, va2)]
      | _ -> raise (Evaluation (fi, expr, "first argument must be a label")))
  | ECat (fi, expr1, expr2) ->
      let va1 = eval env expr1 in
      let va2 = eval env expr2 in
      va1 @ va2
  | EApp (fi, fun_name, exprs) ->
      let vas = List.map (eval env) exprs in
      if Ctx.is_bltin fun_name then
        let _, _, _, f = Ctx.lookup_bltin fi fun_name in
        try f vas
	with Bltin.Bltin_error_intern mes ->
	  raise (Bltin_error (fi, fun_name, mes))
      else begin
        let _, pat_cell_pairs, _, body = Ctx.lookup_fundef fi fun_name in
        if !Pref.tracepat then
          printf "applying %s to %a:@." fun_name print_vas vas;
        wrap_trace (fun () -> 
          let env = eval_application fi Env.empty pat_cell_pairs vas in
          eval env body)
          fun_name vas
      end
  | ESeq(fi, expr1, expr2) ->
      let _ = eval env expr1 in
      eval env expr2
  | EFilter(fi, expr1, filter, cell) ->
      let va1 = eval env expr1 in
      eval_filter fi env va1 filter cell 
  | ECast(fi, ty, expr1, coerce, cell, elsecl) ->
      let va = eval env expr1 in
      let x = Hashtbl.find Check.ptbl !cell in
      (match Patmatch.validate x va with
      | `Succeed _ -> va
      | `Fail w -> raise (CastFailed(fi, ty, w)))
  | ETry(fi, expr1, x, expr2) ->
      (try
        eval env expr1 
      with UserExc va ->
        eval (Env.add x va env) expr2)
  | ERaise(fi, expr1) ->
      let va = eval env expr1 in
      raise (UserExc(va))
      
and eval_application fi env pat_cell_pairs args =
  match pat_cell_pairs, args with
    [], [] -> 
      env
  | ((pat, cell) :: rest_pairs), (arg :: rest_args) ->
      (match match_pattern fi env (pat, cell) arg with
	Some env -> eval_application fi env rest_pairs rest_args 
      |	None -> 
	  Finfo.print fi;
	  eprintf "fatal error: param pattern match failure@.";
	  eprintf "input value: %a@." Synutil.print_va arg;
	  raise (EvaluationFunc (fi, "eval_func>>param pattern mismatch")))
  | _ ->
      raise (EvaluationFunc (fi, "eval_func>>num of args mismatch"))

and match_pattern fi env (pat, cell) arg =
  let x = Hashtbl.find Check.ptbl !cell in
  let vars = Synutil.dom_of_typ pat in
  begin
    match Patmatch.patmatch vars x arg with
    | `Succeed res -> 
	Some (List.fold_right
		(fun (var, va) env -> Env.add var va env) 
		res env)
    | `Fail -> 
	None
  end

and eval_filter fi env va filter cell =
  let x, id_to_dom, id_to_body = Hashtbl.find Check.rtbl !cell in
  match 
    Patmatch.eval_filter id_to_dom x va
      (fun b i ->
	eval 
	  (List.fold_right (fun (var, va) env -> Env.add var va env) b env)
	  (List.assq i id_to_body))
  with
  | `Succeed va -> va
  | `Fail -> 
      Finfo.print fi;
      eprintf "fatal error: filter failure@.";
      eprintf "input value: %a@." Synutil.print_va va;
      raise (EvaluationFunc (fi, "eval_filter>>match failure"))
