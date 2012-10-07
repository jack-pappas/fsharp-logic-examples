// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.real

open NUnit.Framework
open FsUnit
open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.completion
open Reasoning.Automated.Harrison.Handbook.qelim
open Reasoning.Automated.Harrison.Handbook.cooper
open Reasoning.Automated.Harrison.Handbook.complex
open Reasoning.Automated.Harrison.Handbook.real


(* ------------------------------------------------------------------------- *)
(* First examples.                                                           *)
(* ------------------------------------------------------------------------- *)
(*
let private example_results_1 : formula<fol>[] = [|
    False;
    True;
    False;
    False;
    True;
    // TODO (#5) : Output is truncated by ocamltop
    False;
    True;
    |]

[<TestCase(@"exists x. x^4 + x^2 + 1 = 0", 0)>]
[<TestCase(@"exists x. x^3 - x^2 + x - 1 = 0", 1)>]
[<TestCase(@"exists x y. x^3 - x^2 + x - 1 = 0 /\
                         y^3 - y^2 + y - 1 = 0 /\ ~(x = y)", 2)>]
[<TestCase(@"exists x. x^2 - 3 * x + 2 = 0 /\ 2 * x - 3 = 0", 3)>]
[<TestCase(@"forall a f k. (forall e. k < e ==> f < a * e) ==> f <= a * k", 4)>]
[<TestCase(@"exists x. a * x^2 + b * x + c = 0", 5)>]
[<TestCase(@"forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           b^2 >= 4 * a * c", 6)>]
[<TestCase(@"forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           a = 0 /\ (b = 0 ==> c = 0) \/
                           ~(a = 0) /\ b^2 >= 4 * a * c", 7)>]
let ``examples 1`` (f, idx) =
    parse f
    |> real_qelim
    |> should equal example_results_1.[idx]
*)

(* ------------------------------------------------------------------------- *)
(* Termination ordering for group theory completion.                         *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 2``() =
    @"1 < 2 /\ (forall x. 1 < x ==> 1 < x^2) /\
             (forall x y. 1 < x /\ 1 < y ==> 1 < x * (1 + 2 * y))"
    |> parse
    |> real_qelim
    |> should equal True


// TODO : Add the other test in this section; ocamltop truncates the
// output so we can't determine the expected result.


(* ------------------------------------------------------------------------- *)
(* A case where using DNF is an improvement.                                 *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 3``() =
    @"forall d.
     (exists c. forall a b. (a = d /\ b = c) \/ (a = c /\ b = 1)
                            ==> a^2 = b)
     <=> d^4 = 1"
    |> parse
    |> real_qelim'
    |> should equal True


