// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.stal

open NUnit.Framework
open FsUnit
open Reasoning.Automated.Harrison.Handbook.lib    
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples
open Reasoning.Automated.Harrison.Handbook.defcnf
open Reasoning.Automated.Harrison.Handbook.dp
open Reasoning.Automated.Harrison.Handbook.stal
open FSharpx.Compatibility.OCaml
open Num

// pg. 94
// ------------------------------------------------------------------------- //
// An example.                                                               //
// ------------------------------------------------------------------------- //

[<Test>]
let ``triggers``() =
    triggers (parse_prop_formula "p <=> (q /\ r)")
    |> should equal [
        ((Atom (P "p"), True), [(Atom (P "q"), True); (Atom (P "r"), True)]); 
        ((Atom (P "q"), True), [(Atom (P "r"), Atom (P "p"))]); 
        ((Atom (P "q"), Not True), [(Atom (P "p"), Not True)]); 
        ((Atom (P "q"), Not (Atom (P "p"))), [(Atom (P "p"), Not True); (Atom (P "r"), Atom (P "p"))]); 
        ((Atom (P "r"), True), [(Atom (P "q"), Atom (P "p"))]); 
        ((Atom (P "r"), Atom (P "q")), [(Atom (P "q"), Atom (P "p"))]); 
        ((Atom (P "r"), Not True), [(Atom (P "p"), Not True)]); 
        ((Atom (P "r"), Not (Atom (P "p"))), [(Atom (P "p"), Not True); (Atom (P "q"), Atom (P "p"))]); 
        ((Atom (P "r"), Not (Atom (P "q"))), [(Atom (P "p"), Not True)])]

// pg. 99
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``stalmarck``() =
    stalmarck (mk_adder_test 2 1) // use small example (2, 1) instead of (6, 3)
    |> should be FsUnit.True