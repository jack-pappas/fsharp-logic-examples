(* ========================================================================= *)
(* Tweak F# default state ready for theorem proving code.                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

fsi.SetWidth <- 72;;                                   (* Reduce margins     *)
include Format;;                                       (* Open formatting    *)
include Num;;                                          (* Open bignums       *)

let print_num n = print_string(string_of_num n);;      (* Avoid range limit  *)
#if INTERACTIVE
fsi.AddPrinter print_num;;                             (* when printing nums *)
#endif
