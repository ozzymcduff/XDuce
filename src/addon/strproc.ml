open Bltin
open Syn
open Sym
open List
open Str
open Base
open String;;

let match_exact pat str =
  string_match (regexp pat) str 0 && (length str = match_end ())

let ltrim str =
  if string_match (regexp "\n+") str 0 then
    string_after str (match_end ())
  else str

let get_match pat str =
  try
    let _ = search_forward (regexp pat) str 0 in
    [MBase (BVString (matched_string str))]
  with Not_found ->
    []

let global_replace pat = global_replace (regexp pat)

let _ =
  (******added by Volker!******)
  add_bltin "contains" (function
      [[MBase(BVString smain)]; [MBase(BVString ssmall)]] -> boolval (string_match (regexp ("^.*" ^ ssmall ^ ".*$")) smain 0)
    | _ -> raise Wrong_base_app);

  add_bltin "match_exact" (function
      [[MBase(BVString smain)]; [MBase(BVString regExp)]] -> boolval (match_exact regExp smain)
    | _ -> raise Wrong_base_app);

  add_bltin "get_match" (function
      [[MBase(BVString regExp)]; [MBase(BVString smain)]] -> get_match regExp smain
    | _ -> raise Wrong_base_app);

  add_bltin "global_replace" (function
      [[MBase(BVString regExp)]; [MBase(BVString repl)]; [MBase(BVString smain)]] -> [MBase(BVString (global_replace regExp repl smain))]
    | _ -> raise Wrong_base_app);

  add_bltin "ltrim" (function
      [[MBase(BVString smain)]] -> [MBase(BVString (ltrim smain))]
    | _ -> raise Wrong_base_app);

  add_bltin "matches" (function
      [[MBase(BVString smain)]; [MBase(BVString regExp)]] -> boolval (string_match (regexp (regExp)) smain 0)
    | _ -> raise Wrong_base_app);

  add_bltin "is_float" (function
      [[MBase(BVString number)]] -> boolval (if number = string_of_float(float_of_string(number)) then true else false)
    | _ -> raise Wrong_base_app);

  add_bltin "split" (function
      [[MBase(BVString s)] ; [MBase(BVString regExp)]] -> (map (function (s) -> MBase(BVString s)) (split (regexp regExp) s))
    | _ -> raise Wrong_base_app);

  add_bltin "get_group_matches" (function
      [[MBase(BVString smain)] ; [MBase(BVString regExp)]] -> 
        ignore(string_match (regexp regExp) smain 0);
        let list = 
          let rec f i r = 
            let m = 
              try Some (matched_group (i) smain) 
              with Not_found -> None in
            match m with
                Some m -> f (i+1) (m::r) 
              | None -> List.rev r in 
                f 1 []
        in List.map (fun s -> MBase(BVString s)) list
    | _ -> raise Wrong_base_app);

  add_bltin "get_matches" (function
      [[MBase(BVString smain)] ; [MBase(BVString regExp)]] -> 
        let list = 
          let rec f pos r = 
            let m = 
              try
                ignore (search_forward (regexp regExp) smain pos);
                let mbeg = match_beginning () in
                let mend = match_end () in
                Some (mbeg,mend)
              with Not_found -> None in
            match m with
                Some (b,e) -> (f e ((String.sub smain b (e-b))::r))
              | None -> List.rev r in 
                f 0 []
        in List.map (fun s -> MBase(BVString s)) list
    | _ -> raise Wrong_base_app);

  add_bltin "count_digits" (function
      [[MBase(BVString smain)]] -> 
        let j = ref 0 in
        for i = 0 to (String.length smain)-1 do
          if (string_match (regexp "[0-9]") (String.sub smain i 1) 0) then
            j := !j+1;
        done ;
        [MBase(BVInt !j)]
    | _ -> raise Wrong_base_app);




