// ========================================================================= //
// Copyright (c) 2012 Jack Pappas, Anh-Dung Phan                             //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

(* ========================================================================= *)
(* Tweak F# default state ready for theorem proving code.                    *)
(* ========================================================================= *)

#I @".\..\FSharpx.Books.AutomatedReasoning\bin\Debug"
#r @"FSharpx.Books.AutomatedReasoning.dll"
#r @"FSharpx.Compatibility.Ocaml.dll"
#r @"FSharp.PowerPack.dll"

fsi.PrintWidth <- 72;;                                   (* Reduce margins     *)
//open Format;;                                          (* Open formatting    *)
open FSharpx.Compatibility.OCaml;;                       (* Open bignums       *)
open FSharpx.Compatibility.OCaml.Num;;

fsi.AddPrinter (fun (n : Num) -> n.ToString ());;        (* Avoid range limit  *)
                                                         (* when printing nums *)

let [<Literal>] STACK_LIMIT = 16777216;; // 16MB

/// Run a function with custom stack size in byte
let runWithStackFrame stackSize fn =
    let result = ref Unchecked.defaultof<'T> // ref cell to hold return value
    let thread = System.Threading.Thread((fun () -> result := fn()), stackSize)
    thread.Start()
    thread.Join() // thread finishes
    !result;;

let inline runWith16MBStack fn =
    runWithStackFrame STACK_LIMIT fn;;

