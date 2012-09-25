// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
open Reasoning.Automated.Harrison.Handbook.bdd

// pg. 105
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

bddtaut (mk_adder_test 4 2);;

// pg. 107
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

ebddtaut (prime 101);;

ebddtaut (mk_adder_test 9 5);;