// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.qelim

open NUnit.Framework
open FsUnit

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.decidable
open Reasoning.Automated.Harrison.Handbook.qelim

// pg. 335
//  ------------------------------------------------------------------------- // 
//  Examples.                                                                 // 
//  ------------------------------------------------------------------------- // 

[<TestCase("forall x y. exists z. z < x /\ z < y", "true")>]
[<TestCase("exists z. z < x /\ z < y", "true")>]
[<TestCase("exists z. x < z /\ z < y", "x < y")>]
[<TestCase("(forall x. x < a ==> x < b)", "~(b < a \/ b < a)")>]
[<TestCase("forall a b. (forall x. x < a ==> x < b) <=> a <= b", "true")>]
[<TestCase("forall a b. (forall x. x < a <=> x < b) <=> a = b", "true")>]
[<TestCase("exists x y z. forall u.
					x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)", "false")>]
let ``test quelim_dlo`` (input, expected) =
    quelim_dlo (parse input)
    |> should equal (parse expected)

