// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.bdd

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples
open Reasoning.Automated.Harrison.Handbook.bdd
 
open NUnit.Framework
open FsUnit

// pg. 105
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test bddtaut``() =
    bddtaut (mk_adder_test 4 2)
    |> should be True

// pg. 107
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test ebddtaut with prime``() =
    ebddtaut (prime 101)
    |> should be True

[<Test>]
let ``test ebddtaut with mk_adder_test``() =
    ebddtaut (mk_adder_test 9 5)
    |> should be True


