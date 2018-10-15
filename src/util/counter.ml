type counter = { name : string; mutable count : int }

let counters = ref []

let make() =
  { name = ""; count = 0 }

let create n = 
  let c = { name = n; count = 0 } in
  counters := c::!counters;
  c

let incr c = 
  c.count <- c.count + 1

let get c = 
  c.count

let next c = 
  let v = get c in 
  incr c; 
  v

let dump () =
  let cs = 
    Sort.list (fun c1 c2 -> c1.name < c2.name) !counters in
  List.iter (fun c ->
    Format.eprintf "counter \"%s\": %d@." c.name c.count)
    cs

let counter1 = create "counter1"
let counter2 = create "counter2"
let counter3 = create "counter3"


