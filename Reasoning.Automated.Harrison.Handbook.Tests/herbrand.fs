// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.herbrand

open Reasoning.Automated.Harrison.Handbook.lib    
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.dp
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand

open NUnit.Framework
open FsUnit

// pg. 161
// ------------------------------------------------------------------------- //
// First example and a little tracing.                                       //
// ------------------------------------------------------------------------- //
    
[<Test>]
let ``test gilmore simple``() =
    gilmore (parse "exists x. forall y. P(x) ==> P(y)")
    |> should equal 2

// pg. 161
// ------------------------------------------------------------------------- //
// Quick example.                                                            //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test gilmore quick``() =
    gilmore (parse "~(exists x. U(x) /\ Q(x)) 
        /\ (forall x. P(x) ==> Q(x) \/ R(x)) 
        /\ ~(exists x. P(x) ==> (exists x. Q(x))) 
        /\ (forall x. Q(x) 
        /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))")
    |> should equal 1

[<Test>]
let ``test davisputnam``() =
    davisputnam (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")
    |> should equal 19

[<Test>]
let ``test davisputnam'``() =
    davisputnam' (parse "(forall x. exists y. P(x,y)) 
        /\ (forall x. exists y. G(x,y)) 
        /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
        ==> (forall x. exists y. H(x,y))")
    |> should equal 3

[<Test; Category("LongRunning")>]
let ``test davisputnam' slow``() =
    davisputnam' (parse "(exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))")
    |> should equal 5