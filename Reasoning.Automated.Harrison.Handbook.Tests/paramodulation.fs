// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.paramodulation

open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.paramodulation

open NUnit.Framework
open FsUnit

[<Test>]
let ``paramodulation``() =
    paramodulation (parse @"(forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
                            ==> forall x. f(x) = x")
    |> should equal [true]