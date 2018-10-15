open Syn
open Ctx

exception Ill_formed of Finfo.finfo * string * ty
exception Ill_formed_pattern of Finfo.finfo * ty

val wf_type : unit -> unit

exception Non_linear_pattern of Finfo.finfo * ty

val check_pattern_linear : ty -> unit
val check_filter_linear : ty -> unit

