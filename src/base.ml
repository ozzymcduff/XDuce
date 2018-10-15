(* base types and values *)

type basety =
    BTString
  | BTInt
  | BTFloat

type baseval =
    BVString of string
  | BVInt of int
  | BVFloat of float

(* base types and values *)

let basety_of_string = function
    "String" -> Some BTString
  | "Int" -> Some BTInt
  | "Float" -> Some BTFloat
  | _ -> None

let string_of_basety = function
    BTString -> "String"
  | BTInt -> "Int"
  | BTFloat -> "Float"
    
let string_of_baseval = function
    BVString s -> "\"" ^ s ^ "\""
  | BVInt i -> string_of_int i
  | BVFloat f -> string_of_float f

let is_of_basety bval bty = 
  match bval, bty with
    BVString _, BTString -> true
  | BVInt _, BTInt -> true
  | BVFloat _, BTFloat -> true
  | _ -> false

let basety_of_baseval = function
    BVString _ -> BTString
  | BVInt _ -> BTInt
  | BVFloat _ -> BTFloat


