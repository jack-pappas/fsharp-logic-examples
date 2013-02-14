// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.bdd

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples
open FSharpx.Books.AutomatedReasoning.bdd
 
open NUnit.Framework
open FsUnit

let private bddtautValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // bdd.p001
        (mk_adder_test 4 2),
        true
    );
    |]

[<Test>]
[<TestCase(0, TestName = "bdd.p001")>]
let ``bddtaut tests`` idx = 
    let (formula, _) = bddtautValues.[idx]
    let (_, result) = bddtautValues.[idx]
    bddtaut formula
    |> should equal result

let private ebddtautValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // bdd.p002
        (prime 101),
        true
    );
    (
        // idx 1
        // bdd.p003
        (mk_adder_test 9 5),
        true
    );
    |]

[<Test>]
[<TestCase(0, TestName = "bdd.p002")>]
[<TestCase(1, TestName = "bdd.p003")>]
let ``ebddtaut tests`` idx = 
    let (formula, _) = ebddtautValues.[idx]
    let (_, result) = ebddtautValues.[idx]
    ebddtaut formula
    |> should equal result
