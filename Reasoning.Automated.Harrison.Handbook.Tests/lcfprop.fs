// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.lcfprop

open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
open NUnit.Framework
open FsUnit

// pg. 488
// ------------------------------------------------------------------------- //
// The examples in the text.                                                 //
// ------------------------------------------------------------------------- //

[<TestCase(@"(p ==> q) \/ (q ==> p)", @"(p ==> q) \/ (q ==> p)")>]
[<TestCase(@"p /\ q <=> ((p <=> q) <=> p \/ q)", @"p /\ q <=> ((p <=> q) <=> p \/ q)")>]
[<TestCase(@"((p <=> q) <=> r) <=> (p <=> (q <=> r))", @"((p <=> q) <=> r) <=> (p <=> (q <=> r))")>]
let ``lcftaut`` (input, expected) =
    lcftaut (parse input)
    |> should equal (parse expected)
