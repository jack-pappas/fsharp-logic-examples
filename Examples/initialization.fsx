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

let STACK_LIMIT = 16777216 // 16MB

/// Run a function with custom stack size in byte
let runWithStackFrame stackSize fn =
    let result = ref Unchecked.defaultof<'T> // ref cell to hold return value
    let thread = System.Threading.Thread((fun () -> result := fn()), stackSize)
    thread.Start()
    thread.Join() // thread finishes
    !result

let inline runWith16MBStack fn = runWithStackFrame STACK_LIMIT fn

(* TEMP :   These operators were removed from the 'lib' module.
            Eventually, they should be replaced in the example code
            by their standard F# equivalents. *)
// pg. 618
// OCaml: val ( -- ) : int -> int -> int list = <fun>
// F#:    val ( -- ) : int -> int -> int list
let inline (--) m n = [m .. n];;    // Usages of this should be changed to [x .. y]

// pg.618
// OCaml: val ( --- ) : num -> num -> num list = <fun>
// F#:    val ( --- ) : num -> num -> num list
let inline (---) (m : num) (n : num) = [m .. n];;   // Usages of this should be changed to [x .. y]

// pg. 618
// OCaml: val ( ** ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b = <fun>
// F#:    val ( >>|> ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
/// Composes two functions, then applies a value to the resulting function.
let inline ( >>|> ) f g x = f <| g x;;      // Usages of this should be changed to <<

// ------------------------------------------------------------------------- //
// Find list member that maximizes or minimizes a function.                  //
// ------------------------------------------------------------------------- //

// pg. 620
// OCaml: val maximize : ('a -> 'b) -> 'a list -> 'a = <fun>
// F#:    val maximize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
let inline maximize f l =
    List.maxBy f l
    
// pg. 620
// OCaml: val minimize : ('a -> 'b) -> 'a list -> 'a = <fun>
// F#:    val minimize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
let inline minimize f l =
    List.minBy f l

