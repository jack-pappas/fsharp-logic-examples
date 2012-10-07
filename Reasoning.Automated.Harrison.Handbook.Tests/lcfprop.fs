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

[<TestCase(@"(p ==> q) \/ (q ==> p)", Result="|- (p ==> q) \/ (q ==> p)")>]
[<TestCase(@"p /\ q <=> ((p <=> q) <=> p \/ q)", Result="|- p /\ q <=> (p <=> q) <=> p \/ q")>]
[<TestCase(@"((p <=> q) <=> r) <=> (p <=> (q <=> r))", Result="|- ((p <=> q) <=> r) <=> p <=> q <=> r")>]
let ``lcftaut`` f =
    lcftaut (parse f)
    |> sprint_thm
