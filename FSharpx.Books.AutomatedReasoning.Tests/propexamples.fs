// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.propexamples

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples
open NUnit.Framework
open FsUnit

(* Below tests take a few seconds to complete! *)

// pg. 63
// ------------------------------------------------------------------------- //
// Some currently tractable examples.                                        //
// ------------------------------------------------------------------------- //

// propexamples.p002
[<TestCase(3, 3, 5, Result = false)>]

// propexamples.p003
[<TestCase(3, 3, 6, Result = true)>]
let ``ramsey``(s, t, n) =
    tautology(ramsey s t n)

// pg. 72
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// propexamples.p005
[<TestCase(7, Result = true)>]
// propexamples.p006
[<TestCase(9, Result = false)>]
// propexamples.p007
// Harrison #05 - prime
[<TestCase(11, Result = true)>]
let ``prime`` p =
    tautology(prime p)