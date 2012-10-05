// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.equal

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.equal

open NUnit.Framework
open FsUnit

// pg. 241
// ------------------------------------------------------------------------- //
// A simple example (see EWD1266a and the application to Morley's theorem).  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test meson002 1``() =
    equalitize (parse "
        (forall x. f(x) ==> g(x)) /\ 
        (exists x. f(x)) /\ 
        (forall x y. g(x) /\ g(y) ==> x = y) 
        ==> forall y. g(y) ==> f(y)")
    |> meson002
    |> should equal [6]

[<Test>]
let ``test meson002 2``() =
    equalitize (parse "forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c")
    |> meson002
    |> should equal [8]

[<Test>]
let ``test meson002 3``() =
    (parse "
    axiom(f(f(f(f(f(c))))),c) /\ 
    axiom(c,f(f(f(f(f(c)))))) /\ 
    axiom(f(f(f(c))),c) /\ 
    axiom(c,f(f(f(c)))) /\ 
    (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
    (forall s t. cong(s,t) ==> cchain(s,t)) /\ 
    (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
    (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\ 
    (forall s t. cchain(s,t) ==> s = t) /\ 
    (forall s t. achain(s,t) ==> s = t) /\ 
    (forall t. t = t) /\ 
    (forall x y. x = y ==> cong(f(x),f(y))) 
    ==> f(c) = c")
    |> meson002
    |> should equal [17]
