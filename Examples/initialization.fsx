(* ========================================================================= *)
(* Tweak F# default state ready for theorem proving code.                    *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

#I @"C:\Users\Jack\Desktop\fsharp-logic-examples\Reasoning.Automated.Harrison.Handbook\bin\Debug"
#r @"Reasoning.Automated.Harrison.Handbook.dll"
#r @"FSharpx.Compatibility.Ocaml.dll"
#r @"FSharp.PowerPack.dll"

// TODO : Reference the OCaml compatibility DLL so we can use the Format and Num modules.

fsi.PrintWidth <- 72;;                                   (* Reduce margins     *)
//open Format;;                                          (* Open formatting    *)
open FSharpx.Compatibility.OCaml;;                       (* Open bignums       *)
open FSharpx.Compatibility.OCaml.Num;;

let print_num (n : Num) = n.ToString ();;                (* Avoid range limit  *)
fsi.AddPrinter print_num;;                               (* when printing nums *)

