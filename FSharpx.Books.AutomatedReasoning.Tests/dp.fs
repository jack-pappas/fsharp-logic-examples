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

let private dptautValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // dp.p002
        (prime 11),
        true
    );
    |]

[<TestCase(0, TestName = "dp.p002")>]

[<Test>]
let ``dptaut tests`` idx = 
    let (prop_formula, _) = dptautValues.[idx]
    let (_, result) = dptautValues.[idx]
    dptaut prop_formula
    |> should equal result

let private dplltautValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // dp.p003
        (prime 11),
        true
    );
    |]

[<TestCase(0, TestName = "dp.p003")>]

[<Test>]
let ``dplltaut tests`` idx = 
    let (prop_formula, _) = dplltautValues.[idx]
    let (_, result) = dplltautValues.[idx]
    dplltaut prop_formula
    |> should equal result

let private dplitautValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // dp.p004
        (prime 101),
        true
    );
    (
        // idx 1
        // dp.p006
        (prime 11),
        true
    );
    |]

[<TestCase(0, TestName = "dp.p004", Category = "LongRunning")>]
[<TestCase(1, TestName = "dp.p006")>]

[<Test>]
let ``dplitaut tests`` idx = 
    let (prop_formula, _) = dplitautValues.[idx]
    let (_, result) = dplitautValues.[idx]
    dplitaut prop_formula
    |> should equal result
    
let private dplbtautValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // dp.p005
        (prime 101),
        true
    );
    (
        // idx 1
        // dp.p007
        (prime 11),
        true
    );
    |]

[<TestCase(0, TestName = "dp.p004", Category = "LongRunning")>]
[<TestCase(1, TestName = "dp.p006")>]

[<Test>]
let ``dplbtaut tests`` idx = 
    let (prop_formula, _) = dplbtautValues.[idx]
    let (_, result) = dplbtautValues.[idx]
    dplbtaut prop_formula
    |> should equal result
