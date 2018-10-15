open List
open Format

let print_list sep print l =
  match l with
    [] -> ()
  | v::r -> print v; List.iter (fun v -> sep (); print v) r

let print_set ff print s =
  fprintf ff "{@[";
  print_list (fun () -> fprintf ff ",@ ") (fun x -> print ff x) s;
  fprintf ff "@]}"
    
let print_tuple ff print t =
  fprintf ff "(@[";
  print_list (fun () -> fprintf ff ",@ ") (fun x -> print ff x) t;
  fprintf ff "@])"

