open Bltin;;
open Syn;;
open Sym;;
open Base;;


add_bltin "iplus" (bin_int_op (fun i1 i2 -> i1+i2));;
add_bltin "iminus" (bin_int_op (fun i1 i2 -> i1-i2));;
add_bltin "imul" (bin_int_op (fun i1 i2 -> i1*i2));;
add_bltin "idiv" (bin_int_op (fun i1 i2 -> i1/i2));;
add_bltin "imod" (bin_int_op (fun i1 i2 -> i1 mod i2));;
add_bltin "rplus" (bin_float_op (fun r1 r2 -> r1+.r2));;
add_bltin "rminus" (bin_float_op (fun r1 r2 -> r1-.r2));;
add_bltin "rmul" (bin_float_op (fun r1 r2 -> r1*.r2));;
add_bltin "rdiv" (bin_float_op (fun r1 r2 -> r1/.r2));;

let bin_comp c = function
    [v1; v2] -> boolval (c v1 v2)
  | _ -> raise Wrong_base_app;;

add_bltin "lt" (bin_comp (<));;
add_bltin "gt" (bin_comp (>));;
add_bltin "lteq" (bin_comp (<=));;
add_bltin "gteq" (bin_comp (>=));;

add_bltin "eq" (bin_comp (=));;

add_bltin "float_of_int" (function
    [[MBase(BVInt i)]] -> [MBase(BVFloat (float_of_int i))]
  | _ -> raise Wrong_base_app);;

add_bltin "string_of_int" (function
    [[MBase(BVInt i)]] -> [MBase(BVString (string_of_int i))]
  | _ -> raise Wrong_base_app);;

add_bltin "string_of_float" (function
    [[MBase(BVFloat f)]] -> [MBase(BVString (string_of_float f))]
  | _ -> raise Wrong_base_app);;

add_bltin "int_of_string" (function	
    [[MBase(BVString s)]] -> [MBase(BVInt (int_of_string s))]
					(* partial impl: not catching exceptions! *)
  | _ -> raise Wrong_base_app);;

add_bltin "float_of_string" (function
    [[MBase(BVString s)]] -> [MBase(BVFloat (float_of_string s))]
  | _ -> raise Wrong_base_app);;

add_bltin "label_of" (function
    [MLab(ns, lab, _)]::_ -> [MBase(BVString (name ns ^ ":" ^ name lab))]
  | _ -> raise Wrong_base_app);;

add_bltin "string_cat" (function
    [[MBase(BVString s1)]; [MBase(BVString s2)]] ->
      [MBase(BVString (s1 ^ s2))]
  | _ -> raise Wrong_base_app);;

add_bltin "string_compare" (function
    [[MBase(BVString s1)]; [MBase(BVString s2)]] ->
      [MBase(BVInt (compare s1 s2))]
  | _ -> raise Wrong_base_app);;

add_bltin "print" (function
    [v] -> Format.printf "%a@." Synutil.print_va v; []
  | _ -> raise Wrong_base_app);;

add_bltin "display" (function
    [[MBase(BVString s)]] ->
      Format.printf "%s@." s; []
  | _ -> raise Wrong_base_app);;

add_bltin "fileout_string" (function
    [[MBase(BVString filename)]; [MBase(BVString str)]] ->
      let ch = open_out filename in
      output_string ch str;
      close_out ch;
      []
  | _ -> raise Wrong_base_app);;

add_bltin "fprint_string" (function
    [[MBase(BVString filename)]; [MBase(BVString str)]] ->
      let modes = [Open_wronly; Open_creat; Open_append; Open_text] in
      let ch = open_out_gen modes 0o666 filename in
      output_string ch str;
      close_out ch;
      []
  | _ -> raise Wrong_base_app);;

add_bltin "argv" (function
    [[]] ->
      List.map (fun s -> MBase(BVString s)) !Pref.args
  | _ -> raise Wrong_base_app);;

add_bltin "system" (function
    [es] ->
      let com = 
	List.fold_right (fun e r ->
	  match e with
	    MBase(BVString s) -> s ^ " " ^ r
	  | _ -> raise Wrong_base_app)
	  es "" in
      [MBase(BVInt (Sys.command com))]
  | _ -> raise Wrong_base_app);;

add_bltin "getenv" (function
    [[MBase(BVString s)]] ->
      (try [MBase(BVString (Sys.getenv s))] with
	Not_found -> [])
  | _ -> raise Wrong_base_app);;

(*
add_bltin "cgi_args" (function
    [[]] ->
	Cgi.parse_arguments Cgi.default_config;
	Listutil.mapcat (fun (name,arg) ->
	  Synutil.label_va
	    (Sym.label name) 
	    [MBase(BVString (Cgi.arg_value arg))])
	(List.sort (fun (name,_) (name',_) -> compare name name')
	   (Cgi.arguments()))
  | _ -> raise Wrong_base_app);;
*)

add_bltin "string_length" (function
    [[MBase(BVString s)]] -> [MBase(BVInt (String.length s))]
  | _ -> raise Wrong_base_app);;


add_bltin "print_string_oneline" (function
    [[MBase(BVString s)]] -> print_string s; flush stdout; []
  | _ -> raise Wrong_base_app);;

let read_file fn =
  let ip = open_in fn in
  let len = in_channel_length ip in
  let str = String.make len ' ' in
  really_input ip str 0 len;
  close_in ip;
  str;;

add_bltin "read_file" (function
    [[MBase(BVString s)]] -> [MBase (BVString (read_file s))]
  | _ -> raise Wrong_base_app);;

add_bltin "fprint_string" (function
    [[MBase(BVString filename)]; [MBase(BVString str)]] ->
      let modes = [Open_wronly; Open_creat; Open_append; Open_text] in
      let ch = open_out_gen modes 0o666 filename in
      output_string ch str;
      close_out ch;
      []
  | _ -> raise Wrong_base_app);;

let get_time () =
  let tm = Unix.gmtime(Unix.time()) in
  Synutil.label_va (Sym.label "sec") [MBase(BVInt tm.Unix.tm_sec)] @
  Synutil.label_va (Sym.label "min") [MBase(BVInt tm.Unix.tm_min)] @
  Synutil.label_va (Sym.label "hour") [MBase(BVInt tm.Unix.tm_hour)] @
  Synutil.label_va (Sym.label "mday") [MBase(BVInt tm.Unix.tm_mday)] @
  Synutil.label_va (Sym.label "mon") [MBase(BVInt tm.Unix.tm_mon)] @
  Synutil.label_va (Sym.label "year") [MBase(BVInt tm.Unix.tm_year)] @
  Synutil.label_va (Sym.label "wday") [MBase(BVInt tm.Unix.tm_wday)] @
  Synutil.label_va (Sym.label "yday") [MBase(BVInt tm.Unix.tm_yday)] @
  Synutil.label_va (Sym.label "isdst") (boolval tm.Unix.tm_isdst);;

add_bltin "get_time" (function
    [[]] -> get_time()
  | _ -> raise Wrong_base_app);;

add_bltin "get_float_time" (function
    [[]] -> [MBase(BVFloat (Unix.time()))]
  | _ -> raise Wrong_base_app);;


Random.self_init();;

add_bltin "random_int" (function
    [[MBase(BVInt i)]] -> [MBase(BVInt (Random.int i))]
  | _ -> raise Wrong_base_app);;

add_bltin "random_float" (function
    [[MBase(BVFloat i)]] -> [MBase(BVFloat (Random.float i))]
  | _ -> raise Wrong_base_app);;


