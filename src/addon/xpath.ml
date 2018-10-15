open Bltin
open Syn
open Str
open List
open Base

(* ---------- normalize_space ---------- *)

let compose f g x = g (f x)

let normalize_space =
  let r1 = regexp "[\t\\|\n\\| ]+" in
  let r2 = regexp " $\\|^ " in
  compose (global_replace r1 " ") (global_replace r2 "")

let _ =
  add_bltin "normalize_space" (function
      [[MBase(BVString smain)]] ->
        [MBase (BVString (normalize_space smain))]
    | _ ->
        raise Wrong_base_app)

(* ---------- floor ---------- *)

let _ =
  add_bltin "floor" (function
      [[MBase (BVFloat x)]] -> [MBase (BVInt (int_of_float (floor x)))]
    | _ -> raise Wrong_base_app)

(* ---------- ceiling ---------- *)

let _ =
  add_bltin "ceiling" (function
      [[MBase (BVFloat x)]] -> [MBase (BVInt (int_of_float (ceil x)))]
    | _ -> raise Wrong_base_app)

(* ---------- substring ---------- *)

let substring s n m =
  let sz = String.length s in
  let n = max 0 (n-1) in
  if n >= sz then ""
  else String.sub s n (max 0 (min m (sz-n)))

let _ =
  add_bltin "substring" (function
      [[MBase (BVString s)]; [MBase (BVInt n)]; [MBase (BVInt m)]] ->
        [MBase (BVString (substring s n m))]
    | _ ->
        raise Wrong_base_app)

(* ---------- starts_with ---------- *)

let starts_with s1 s2 =
  let n = String.length s2 in
  n <= String.length s1 && Str.string_before s1 n = s2

let _ =
  add_bltin "starts_with" (function
      [[MBase (BVString s1)]; [MBase (BVString s2)]] ->
        if starts_with s1 s2 then Synutil.true_va else Synutil.false_va
    | _ ->
        raise Wrong_base_app)

(* ---------- substring_before ---------- *)

let substring_before s1 s2 =
  try
    let n = Str.search_forward (Str.regexp s2) s1 0 in
    Str.string_before s1 n
  with Not_found -> ""

let _ =
  add_bltin "substring_before" (function
      [[MBase (BVString s1)]; [MBase (BVString s2)]] ->
        [MBase (BVString (substring_before s1 s2))]
    | _ ->
        raise Wrong_base_app)

(* ---------- substring_after ---------- *)

let substring_after s1 s2 =
  try
    let n = Str.search_forward (Str.regexp s2) s1 0 + String.length s2 in
    Str.string_after s1 n
  with Not_found -> ""

let _ =
  add_bltin "substring_after" (function
      [[MBase (BVString s1)]; [MBase (BVString s2)]] ->
        [MBase (BVString (substring_after s1 s2))]
    | _ ->
        raise Wrong_base_app)

(* ---------- contains ---------- *)

let contains s1 s2 =
  try ignore(Str.search_forward (Str.regexp s2) s1 0); true
  with Not_found -> false

let _ =
  add_bltin "contains" (function
      [[MBase (BVString s1)]; [MBase (BVString s2)]] ->
        if contains s1 s2 then Synutil.true_va else Synutil.false_va
    | _ ->
        raise Wrong_base_app)

(* ---------- translate ---------- *)

let preinc r =
  let res = !r in
  incr r;
  res

let translate s1 s2 s3 =
  let n = String.length s1 in
  let n2 = String.length s3 in
  let outstr = String.make n ' ' in
  let outptr = ref 0 in
  for i = 0 to n-1 do
    let ch = s1.[i] in
    try
      let k = String.index s2 ch in
      if k<n2 then outstr.[preinc outptr] <- s3.[k]
    with Not_found ->
      outstr.[preinc outptr] <- ch
  done;
  string_before outstr !outptr

let _ =
  add_bltin "translate" (function
      [[MBase (BVString s1)]; [MBase (BVString s2)]; [MBase (BVString s3)]] ->
        [MBase (BVString (translate s1 s2 s3))]
    | _ ->
        raise Wrong_base_app)

