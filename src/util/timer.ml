(* ------------------ timers ------------------ *)

type timer = { name : string; 
	       mutable time : float; 
	       mutable last_start : float }

let timers = ref []

let make() =
  { name = ""; 
    time = 0.0;
    last_start = 0.0 }

let create name = 
  let timer = { name = name; 
		time = 0.0;
		last_start = 0.0 } in
  timers := timer :: !timers;
  timer

let start timer =
  if timer.last_start <> 0.0 then failwith ("Timer " ^ timer.name ^ " started before stopped")
  else timer.last_start <- Unix.gettimeofday()

let stop timer =
  if timer.last_start = 0.0 then failwith ("Timer " ^ timer.name ^ " stopped before stopped")
  else begin
    timer.time <- timer.time +. ((Unix.gettimeofday()) -. timer.last_start);
    timer.last_start <- 0.0
  end

let reset timer =
  timer.time <- 0.0

let get timer = timer.time

let wrap timer f =
  start timer;
  let res = f() in
  stop timer;
  res

let dump () =
  let timers = Sort.list (fun timer1 timer2 -> timer1.name < timer2.name) !timers in
  List.iter (fun timer ->
    Format.eprintf "timer \"%s\": %f@." timer.name timer.time)
    timers

