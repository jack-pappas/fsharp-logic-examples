(* ========================================================================= *)
(* Tweak F# default state ready for theorem proving code.                    *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

#I @"C:\Users\Jack\Desktop\fs-hol-light\Reasoning.Automated.Harrison.Handbook\bin\Debug"
#r @"Reasoning.Automated.Harrison.Handbook.dll"

// TODO : Reference the OCaml compatibility DLL so we can use the Format and Num modules.

fsi.PrintWidth <- 72;;                                 (* Reduce margins     *)
//open Format;;                                       (* Open formatting    *)
//open Num;;                                          (* Open bignums       *)

// TODO : Fix this -- the 'print_string' function is from the Format module,
// which hasn't been completely ported yet.
//let print_num n = print_string(string_of_num n);;      (* Avoid range limit  *)
//fsi.AddPrinter print_num;;                             (* when printing nums *)

