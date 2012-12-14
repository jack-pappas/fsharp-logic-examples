// ========================================================================= //
// Copyright (c) 2012 Jack Pappas, Anh-Dung Phan                             //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// Tweak F# default state for theorem proving code.                          //
// ========================================================================= //

#I @".\..\FSharpx.Books.AutomatedReasoning\bin\Debug"
#r @"FSharpx.Books.AutomatedReasoning.dll"
#r @"FSharp.Compatibility.OCaml.dll"

// Reduce margins
fsi.PrintWidth <- 72;;

// Open bignums
open FSharp.Compatibility.OCaml;;
#nowarn "62";;
open FSharp.Compatibility.OCaml.Num;;

// Print the full value of a Num instead of truncating it.
fsi.AddPrinter (fun (n : Num) -> n.ToString ());;
