// ========================================================================= //
// Copyright (c) 2012 Jack Pappas, Anh-Dung Phan                             //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

(* ========================================================================= *)
(* Tweak F# default state ready for theorem proving code.                    *)
(* ========================================================================= *)

#I @".\..\Reasoning.Automated.Harrison.Handbook\bin\Debug"
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

/// Run a function with custom stack size in byte
let runWithStackFrame stackSize fn =
    let result = ref Unchecked.defaultof<'T> // ref cell to hold return value
    let thread = System.Threading.Thread((fun () -> result := fn()), stackSize)
    thread.Start()
    thread.Join() // thread finishes
    !result