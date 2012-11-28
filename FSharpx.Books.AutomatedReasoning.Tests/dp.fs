// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.dp

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples
open FSharpx.Books.AutomatedReasoning.defcnf
open FSharpx.Books.AutomatedReasoning.dp
open NUnit.Framework
open FsUnit

(* NOTE : Below tests take a few seconds to complete! *)

// pg. 84
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// dp.p002
// Harrison #05 - prime
[<Test>]
let ``dptaut``() =
    dptaut(prime 11)
    |> should be True

// pg. 85
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// dp.p003
// Harrison #05 - prime
[<Test>]
let ``dplltaut``() =
    dplltaut(prime 11)
    |> should be True

// pg. 89
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// dp.p004
// Harrison #05 - prime
[<Test>]
let ``dplitaut``() =
    dplitaut(prime 13) // Use 13 instead of 101 for fast response
    |> should be True

// dp.p005
// Harrison #05 - prime
[<Test>]
let ``dplbtaut``() =
    dplbtaut(prime 13)  // Use 13 instead of 101 for fast response
    |> should be True

