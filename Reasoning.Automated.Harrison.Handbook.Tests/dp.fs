// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.dp

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples
open Reasoning.Automated.Harrison.Handbook.defcnf
open Reasoning.Automated.Harrison.Handbook.dp
open NUnit.Framework
open FsUnit

(* NOTE : Below tests take a few seconds to complete! *)

// pg. 84
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``dptaut``() =
    dptaut(prime 11)
    |> should be True

// pg. 85
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``dplltaut``() =
    dplltaut(prime 11)
    |> should be True

// pg. 89
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``dplitaut``() =
    dplitaut(prime 13) // Use 13 instead of 101 for fast response
    |> should be True

[<Test>]
let ``dplbtaut``() =
    dplbtaut(prime 13)  // Use 13 instead of 101 for fast response
    |> should be True

