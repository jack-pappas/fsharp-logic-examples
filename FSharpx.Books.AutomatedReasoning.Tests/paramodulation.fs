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


let private paramodulationValues : (string * bool list)[] = [| 
    (
        // idx 0
        // paramodulation.p001
        @"(forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
            ==> forall x. f(x) = x",
        [true]
    );
    |]

[<Test>]
[<TestCase(0, TestName = "paramodulation.p001")>]
let ``paramodulation tests`` idx = 
    let (formula, _) = paramodulationValues.[idx]
    let (_, result) = paramodulationValues.[idx]
    paramodulation (parse formula)
    |> should equal result
