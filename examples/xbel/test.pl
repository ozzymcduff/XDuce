#!/usr/bin/perl

alarm 5;

$cmd = "wget " . $ARGV[0] . " --spider";
system ($cmd);

