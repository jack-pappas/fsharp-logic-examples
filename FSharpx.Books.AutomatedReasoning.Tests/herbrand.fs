// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.herbrand

open FSharpx.Books.AutomatedReasoning.lib    
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.dp
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.herbrand

open NUnit.Framework
open FsUnit

// pg. 161
// ------------------------------------------------------------------------- //
// First example and a little tracing.                                       //
// ------------------------------------------------------------------------- //
    
[<Test>]
let ``gilmore simple``() =
    "exists x. forall y. P(x) ==> P(y)"
    |> parse
    |> gilmore
    |> should equal 2

// pg. 161
// ------------------------------------------------------------------------- //
// Quick example.                                                            //
// ------------------------------------------------------------------------- //

[<Test>]
let ``gilmore quick``() =
    @"~(exists x. U(x) /\ Q(x)) 
        /\ (forall x. P(x) ==> Q(x) \/ R(x)) 
        /\ ~(exists x. P(x) ==> (exists x. Q(x))) 
        /\ (forall x. Q(x) 
        /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))"
    |> parse
    |> gilmore
    |> should equal 1

[<Test>]
let ``davis putnam``() =
    @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"
    |> parse
    |> davisputnam
    |> should equal 19

[<TestCase(@"(forall x. exists y. P(x,y)) 
        /\ (forall x. exists y. G(x,y)) 
        /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
        ==> (forall x. exists y. H(x,y))", Result = 3)>]
[<TestCase(@"(exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
        Result = 5, Category = "LongRunning")>]
let ``davis putnam'`` f =
    parse f
    |> davisputnam'
