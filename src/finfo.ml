open Format

(* file info *)

type finfo = 
    { file_name : string;
      start_pos : int;
      end_pos : int }

let input_file_name = ref ""

let make_finfo start_pos end_pos =
  { file_name = !input_file_name; 
    start_pos = start_pos; 
    end_pos = end_pos }

let bogus () =
  { file_name = !input_file_name; 
    start_pos = -1; 
    end_pos = -1 }

let loc_in_file file_name pos =
  let inch = open_in file_name in
  let lineno = ref 1 in
  let linepos = ref 0 in
  for i=0 to pos do
    let ch = input_char inch in
    if ch = '\012' or ch = '\n' then begin
      incr lineno;
      linepos := 0
    end
    else incr linepos
  done;
  close_in inch;
  !lineno,(!linepos-1)

let finfo_to_string 
    { file_name = fname; start_pos = start_pos; end_pos = end_pos } =
  if fname = "" then
    sprintf "characters %d-%d" start_pos end_pos
  else 
    let lineno,linepos = loc_in_file fname start_pos in
    sprintf "File \"%s\", line %d, characters %d-%d" 
      fname lineno linepos (linepos + end_pos - start_pos)

let print finfo =
  eprintf "@[%s:@]@." (finfo_to_string finfo)

