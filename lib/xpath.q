import "xml.q"

extern normalize_space: String -> String
extern floor: Float -> Int
extern ceiling: Float -> Int
extern substring: (String)(Int)(Int) -> String
extern starts_with: (String)(String) -> Bool
extern substring_before: (String)(String) -> String
extern substring_after: (String)(String) -> String
extern contains: (String)(String) -> Bool
extern translate: (String)(String)(String) -> String
