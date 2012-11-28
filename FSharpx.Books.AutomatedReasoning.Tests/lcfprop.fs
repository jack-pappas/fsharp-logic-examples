// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.lcfprop

open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop
open NUnit.Framework
open FsUnit

// pg. 488
// ------------------------------------------------------------------------- //
// The examples in the text.                                                 //
// ------------------------------------------------------------------------- //

// lcfprop.p001
// Pelletier #16
[<TestCase(@"(p ==> q) \/ (q ==> p)", @"(p ==> q) \/ (q ==> p)")>]

// lcfprop.p002
// Harrison #02 - Equations within equations
[<TestCase(@"p /\ q <=> ((p <=> q) <=> p \/ q)", @"p /\ q <=> ((p <=> q) <=> p \/ q)")>]

// lcfprop.p003
// Pelletier #12
[<TestCase(@"((p <=> q) <=> r) <=> (p <=> (q <=> r))", @"((p <=> q) <=> r) <=> (p <=> (q <=> r))")>]
let ``lcftaut`` (input, expected) =
    lcftaut (parse input)
    |> should equal (parse expected)
