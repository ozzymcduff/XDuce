import "strproc.q"

type Time = sec[Int], min[Int], hour[Int], mday[Int], mon[Int], 
            year[Int], wday[Int], yday[Int], isdst[Bool]

extern get_time : () -> Time

extern get_float_time : () -> Float
