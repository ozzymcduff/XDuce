(*
 * bibtex2html - A BibTeX to HTML translator
 * Copyright (C) 1997-2000 Jean-Christophe Filli�tre and Claude March�
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(* $Id: latex_accents.mli,v 1.1.1.1 2001/07/23 02:37:48 hahosoya Exp $ *)

(* replace LaTeX control sequences for special characters. *)

val normalize : string -> string

