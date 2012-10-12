// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.paramodulation

open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.paramodulation

open NUnit.Framework
open FsUnit

[<Test>]
let ``paramodulation``() =
    paramodulation (parse @"(forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
                            ==> forall x. f(x) = x")
    |> should equal [true]