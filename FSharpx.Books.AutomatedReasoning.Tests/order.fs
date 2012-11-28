// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.order

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.order

open NUnit.Framework
open FsUnit

let s = parset "f(x,x,x)"
let t = parset "g(x,y)"

// order.p001
[<Test>]
let ``termsize 1``() =
    termsize s > termsize t
    |> should be True

// ------------------------------------------------------------------------- //
// This fails the rewrite properties.                                        //
// ------------------------------------------------------------------------- //

let i = "y" |=> parset "f(x,x,x)"

// order.p002
[<Test>]
let ``termsize 2``() =
    termsize (tsubst i s) > termsize (tsubst i t)
    |> should be False

    