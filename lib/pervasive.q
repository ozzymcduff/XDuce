(*-------------------- General ------------------*)

type Bool = emptyprefix:False[] | emptyprefix:True[]
type Empty = ()


extern iplus : (Int)(Int) -> Int
extern iminus : (Int)(Int) -> Int
extern imul : (Int)(Int) -> Int
extern idiv : (Int)(Int) -> Int
extern imod : (Int)(Int) -> Int
extern rplus : (Float)(Float) -> Float
extern rminus : (Float)(Float) -> Float
extern rmul : (Float)(Float) -> Float
extern rdiv : (Float)(Float) -> Float
extern float_of_int : Int -> Float
extern label_of : (~[Any]) -> String
extern string_of_int : Int -> String
extern string_of_float : Float -> String
extern int_of_string : String -> Int
extern float_of_string : String -> Float
extern string_cat : (String)(String) -> String
extern string_compare : (String)(String) -> Int 
extern string_length : (String) -> Int
extern eq : (Any)(Any) -> Bool
extern lt : (Any)(Any) -> Bool
extern gt : (Any)(Any) -> Bool
extern lteq : (Any)(Any) -> Bool
extern gteq : (Any)(Any) -> Bool

extern print : Any -> Empty
extern print_string_oneline : String -> Empty
extern display : String -> Empty
extern fileout_string : (String)(String) -> Empty
extern fprint_string : (String)(String) -> Empty
extern argv : () -> String*
extern system : (String+) -> Int
extern getenv : (String) -> String?

extern random_int : (Int) -> Int
extern random_float : (Float) -> Float

fun error (val arg as Any) : None =
  raise(emptyprefix:error[arg])

fun dumb (val arg as None) : Any =
  ()

fun string_of_bool (val b as Bool) : String =
  match b with
    emptyprefix:True[] -> "true"
  | emptyprefix:False[] -> "false"

fun bool_of_string (val s as String) : Bool =
  match s with
    "true" -> emptyprefix:True[]
  | "false" -> emptyprefix:False[]
  | Any -> raise("Not a boolean string: " ^ s)

fun not (val x as Bool) : Bool =
  match x with
     emptyprefix:False[] -> emptyprefix:True[]
   | Any -> emptyprefix:False[]

fun band (val x as Bool)(val y as Bool) : Bool =
  match x,y with
     emptyprefix:True[],emptyprefix:True[] -> emptyprefix:True[]
   | Any -> emptyprefix:False[]

fun bor  (val x as Bool)(val y as Bool) : Bool =
  match x,y with
     emptyprefix:False[],emptyprefix:False[] -> emptyprefix:False[]
   | Any -> emptyprefix:True[]

extern read_file: String -> String

