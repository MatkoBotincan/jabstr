(**********************************************************************
  jabstr  Copyright (C) 2010, 2011  Matko Botincan

  This software is distributed under a GPL license, see LICENSE.
 **********************************************************************)

open Psyntax
open Apron
open Mpqf
open Format


let num_abs pform =
  pform

let var_x = Var.of_string "x";;
  
(* Plugin registration *)
let _ =
  Plugin_callback.add_abs_int (ref num_abs)
