// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
//open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples
open Reasoning.Automated.Harrison.Handbook.defcnf
open Reasoning.Automated.Harrison.Handbook.dp
open Reasoning.Automated.Harrison.Handbook.stal

// pg. 94
// ------------------------------------------------------------------------- //
// An example.                                                               //
// ------------------------------------------------------------------------- //

// val it :
//   ((prop Reasoning.Automated.Harrison.Handbook.formulas.formula *
//     prop Reasoning.Automated.Harrison.Handbook.formulas.formula) *
//    (prop Reasoning.Automated.Harrison.Handbook.formulas.formula *
//     prop Reasoning.Automated.Harrison.Handbook.formulas.formula) list) list =
//   [((Atom (P "p"), True), [(Atom (P "q"), True); (Atom (P "r"), True)]);
//    ((Atom (P "q"), True), [(Atom (P "r"), Atom (P "p"))]);
//    ((Atom (P "q"), Not True), [(Atom (P "p"), Not True)]);
//    ((Atom (P "q"), Not (Atom (P "p"))),
//     [(Atom (P "p"), Not True); (Atom (P "r"), Atom (P "p"))]);
//    ((Atom (P "r"), True), [(Atom (P "q"), Atom (P "p"))]);
//    ((Atom (P "r"), Atom (P "q")), [(Atom (P "q"), Atom (P "p"))]);
//    ((Atom (P "r"), Not True), [(Atom (P "p"), Not True)]);
//    ((Atom (P "r"), Not (Atom (P "p"))),
//     [(Atom (P "p"), Not True); (Atom (P "q"), Atom (P "p"))]);
//    ((Atom (P "r"), Not (Atom (P "q"))), [(Atom (P "p"), Not True)])]
// TODO: Convert output to << >> format
triggers (parse_prop_formula "p <=> (q /\ r)");;

// pg. 99
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// "*** Starting 0-saturation"
// "*** Starting 1-saturation"
// "*** Starting 2-saturation"
// CPU time (user): 90.265625
// val it : bool = true
time stalmarck (mk_adder_test 6 3);;


