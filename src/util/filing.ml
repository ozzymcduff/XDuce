open List

let search_file paths fname =
  try
    Unix.access fname [Unix.F_OK];
    fname
  with Unix.Unix_error _ ->
    try 
      let dirname =
	find (fun path -> 
	  try 
	    Unix.access (path ^ "/" ^ fname) [Unix.F_OK];
	    true
	  with Unix.Unix_error _ -> false)
	  paths in
      dirname ^ "/" ^ fname 
    with Not_found ->
      failwith (fname ^ ": no such file")

