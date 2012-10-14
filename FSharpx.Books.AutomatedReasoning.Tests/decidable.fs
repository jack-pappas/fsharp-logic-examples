// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.decidable

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.herbrand
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.resolution
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.decidable

open NUnit.Framework
open FsUnit

[<Test>]
let ``aedecide``() =
    aedecide (parse @"(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\  (forall x y. P(x,y) ==> P(y,x)) /\ (forall x y. P(x,y) \/ Q(x,y)) ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))")
    |> should be True

[<Test>]
let ``wang``() =
    wang (parse @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
                    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")
    |> should be True

[<TestCase(@"(forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)", Result = true)>]
[<TestCase(@"(forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)", Result = false)>]
let ``decide_fmp`` f =
    decide_fmp (parse f)

[<Test>]
let ``decide_monadic``() =
    decide_monadic (parse @"((exists x. forall y. P(x) <=> P(y)) <=>
                        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
                        ((exists x. forall y. Q(x) <=> Q(y)) <=>
                        ((exists x. P(x)) <=> (forall y. P(y))))")
    |> should be True
