// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.cong

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.stal
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.cong

open NUnit.Framework
open FsUnit

let private ccvalidValues : (string * bool)[] = [|
    (
        // idx 0
        // cong.p001
        @"f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c 
            ==> f(c) = c \/ f(g(c)) = g(f(c))",
        true
    )
    (
        // idx 1
        // cong.p002
        @"f(f(f(f(c)))) = c /\ f(f(c)) = c 
            ==> f(c) = c",
        false
    )
    (
        // idx 2
        // cong.p003
        @"f(a,b) = a 
            ==> f(f(a,b), b) = a",
        true
    )
    |]

[<TestCase(0, TestName = "cong.p001")>]
[<TestCase(1, TestName = "cong.p002")>]
[<TestCase(2, TestName = "cong.p003")>]

[<Test>]
let ``ccvalid tests`` idx =
    let (formula, _) = ccvalidValues.[idx]
    let (_, result) = ccvalidValues.[idx]
    ccvalid (parse formula)
    |> should equal result
