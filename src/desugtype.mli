open Finfo
open Syn

exception Ill_formed_pattern of finfo * string
exception Ill_formed_type of finfo * string
val desug : ty -> Htype.ht
val wf_type : unit -> unit
val check_pattern_linear : ty -> unit
val check_filter_linear : ty -> unit

