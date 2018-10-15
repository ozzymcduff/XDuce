(* CGI interface *)

type Cgi_args = ~[String]*

extern cgi_args : () -> Cgi_args
