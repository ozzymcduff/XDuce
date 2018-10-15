(*main,part*)
extern contains : (String)(String) -> Bool

(*main,regexp*)
extern matches : (String)(String) -> Bool
extern match_exact : (String)(String) -> Bool
extern get_match : (String)(String) -> String?
extern global_replace : (String)(String)(String) -> String

extern ltrim : String -> String

extern is_float : String -> Bool

(* s, delimregexp *)
extern split : (String)(String) -> String*

(*main,regexp -> list*)
extern get_group_matches : (String)(String) -> String*

extern get_matches : (String)(String) -> String*
extern count_digits : String -> Int

