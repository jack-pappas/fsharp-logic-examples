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
        |> should equal result
    | Large ->
        runWithEnlargedStack (fun () -> gilmore (parse formula))
        |> should equal result

// pg. 161
// ------------------------------------------------------------------------- //
// First example and a little tracing.                                       //
// ------------------------------------------------------------------------- //
    
// herbrand.p001
// Harrison #07
//[<Test>]
//let ``gilmore simple``() =
//    "exists x. forall y. P(x) ==> P(y)"
//    |> parse
//    |> gilmore
//    |> should equal 2

// pg. 161
// ------------------------------------------------------------------------- //
// Quick example.                                                            //
// ------------------------------------------------------------------------- //

// herbrand.p003
// Pelletier #24
//[<Test>]
//let ``gilmore quick``() =
//    @"~(exists x. U(x) /\ Q(x)) 
//        /\ (forall x. P(x) ==> Q(x) \/ R(x)) 
//        /\ ~(exists x. P(x) ==> (exists x. Q(x))) 
//        /\ (forall x. Q(x) 
//        /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))"
//    |> parse
//    |> gilmore
//    |> should equal 1


// herbrand.p006
// Pelletier #20
[<Test>]
let ``davis putnam``() =
    @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"
    |> parse
    |> davisputnam
    |> should equal 19

// herbrand.p007
// Pelletier #36
[<TestCase(@"(forall x. exists y. P(x,y)) 
        /\ (forall x. exists y. G(x,y)) 
        /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
        ==> (forall x. exists y. H(x,y))", Result = 3)>]
// herbrand.p008
// Pelletier #29
[<TestCase(@"(exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
        Result = 5, Category = "LongRunning")>]
let ``davis putnam'`` f =
    parse f
    |> davisputnam'
