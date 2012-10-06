// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.meson

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson

open NUnit.Framework
open FsUnit

// pg. 215
// ------------------------------------------------------------------------- //
// Example of naivety of tableau prover.                                     //
// ------------------------------------------------------------------------- //

// pg. 218
// ------------------------------------------------------------------------- //
// The interesting example where tableaux connections make the proof longer. //
// Unfortuntely this gets hammered by normalization first...                 //
// ------------------------------------------------------------------------- //

[<TestCase("forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))", Result=2)>]
[<TestCase("forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))", Result=0)>]
[<TestCase("~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
            (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
            (~s \/ ~v) /\ (~s \/ ~w) ==> false", Result=0)>]
let ``tab`` f =
    tab (parse f)

// pg. 220
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``meson002 all``() =
    meson002 (parse "exists x. exists y. forall z. 
                        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
                        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))")
    |> should equal [8] // There is also an equal in meson module

[<TestCase("p ==> q <=> ~q ==> ~p")>]    
[<TestCase("~ ~p <=> p")>]
[<TestCase("~(p ==> q) ==> q ==> p")>]
[<TestCase("~p ==> q <=> ~q ==> p")>]
[<TestCase("(p \/ q ==> p \/ r) ==> p \/ (q ==> r)")>]
[<TestCase("p \/ ~p")>]
[<TestCase("p \/ ~ ~ ~p")>]
[<TestCase("((p ==> q) ==> p) ==> p")>]    
[<TestCase("(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)")>]
[<TestCase("(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)")>]
[<TestCase("p <=> p")>]
[<TestCase("((p <=> q) <=> r) <=> (p <=> (q <=> r))")>]
[<TestCase("p \/ q /\ r <=> (p \/ q) /\ (p \/ r)")>]
[<TestCase("(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)")>]
[<TestCase("p ==> q <=> ~p \/ q")>]
[<TestCase("(p ==> q) \/ (q ==> p)")>]
[<TestCase("p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)")>]
let ``meson002 returns empty`` f =
    meson002 (parse f)
    |> should equal []
