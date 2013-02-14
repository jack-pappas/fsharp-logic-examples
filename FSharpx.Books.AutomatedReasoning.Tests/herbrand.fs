// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.herbrand

open FSharpx.Books.AutomatedReasoning.initialization
open FSharpx.Books.AutomatedReasoning.lib    
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.dp
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.herbrand

open NUnit.Framework
open FsUnit

let private gilmoreValues : (StackSize * string * int)[] = [| 
    
    (
        // idx 0
        // herbrand.p001
        Standard,
        @"exists x. forall y. P(x) ==> P(y)",
        2
    );
    (
        // idx 1
        // herbrand.p003
        // Pelletier #24
        Standard,
        @" ~(exists x. U(x) /\ Q(x)) 
        /\ (forall x. P(x) ==> Q(x) \/ R(x)) 
        /\ ~(exists x. P(x) ==> (exists x. Q(x))) 
        /\ (forall x. Q(x) 
        /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))",
        1
    );
    (
        // idx 2
        // herbrand.p004
        // Pelletier #45
        Large,
        @"(forall x. P(x) 
        /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) 
        /\ ~(exists y. L(y) /\ R(y)) 
        /\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) 
        /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))",
        5
    );
    (
        // idx 3
        // herbrand.p005
        // Pelletier #20
        Standard,
        @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
        -99
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "herbrand.p001")>]
[<TestCase(1, TestName = "herbrand.p003")>]
[<TestCase(2, TestName = "herbrand.p004")>]
[<TestCase(3, TestName = "herbrand.p005", Category = "LongRunning")>]
let ``gilmore tests`` (idx) =
    let (stackSize, _,  _) = gilmoreValues.[idx]
    let (_, formula, _) = gilmoreValues.[idx]
    let (_, _, result) = gilmoreValues.[idx]
    match stackSize with
    | Standard -> 
        gilmore (parse formula)
    | Large ->
        runWithEnlargedStack (fun () -> gilmore (parse formula))
    |> should equal result

let private davisputnamValues : (string * int)[] = [| 
    (
        // idx 0
        // herbrand.p006
        // Pelletier #20
        @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
        19
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "herbrand.p001")>]
let ``davisputnam tests`` (idx) =
    let (formula, _) = davisputnamValues.[idx]
    let (_, result) = davisputnamValues.[idx]
    davisputnam (parse formula)
    |> should equal result

let private davisputnam002Values : (string * int)[] = [| 
    (
        // idx 0
        // herbrand.p007
        // Pelletier #36
        @"(forall x. exists y. P(x,y)) 
        /\ (forall x. exists y. G(x,y)) 
        /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
        ==> (forall x. exists y. H(x,y))",
        3
    );
    (
        // idx 1
        // herbrand.p008
        // Pelletier #29
        @"(exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
        5
    );
    |]

[<Test>]    
[<TestCase(0, TestName = "herbrand.p007")>]
[<TestCase(1, TestName = "herbrand.p008", Category = "LongRunning")>]
let ``davisputnam002 tests`` (idx) =
    let (formula, _) = davisputnam002Values.[idx]
    let (_, result) = davisputnam002Values.[idx]
    davisputnam002 (parse formula)
    |> should equal result
