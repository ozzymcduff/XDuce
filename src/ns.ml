let ctr = Counter.make ()

let uri_to_symbol : (string, Sym.symbol) Hashtbl.t = 
  Hashtbl.create 121

let symbol_to_uri : (Sym.symbol, string) Hashtbl.t = 
  Hashtbl.create 121

let of_uri uri = 
  try Hashtbl.find uri_to_symbol uri
  with Not_found ->
    let i = Counter.next ctr in
    let l = Sym.label ("ns" ^ (string_of_int i)) in
    Hashtbl.add uri_to_symbol uri l;
    Hashtbl.add symbol_to_uri l uri;
    l

let uri ns =
  Hashtbl.find symbol_to_uri ns

let empty = of_uri ""

let print_table () =
  Hashtbl.iter
    (fun sym uri ->
      Format.printf "%a -> \"%s\"@."
	Sym.print sym uri)
    symbol_to_uri

