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
open Reasoning.Automated.Harrison.Handbook.defcnf
open Reasoning.Automated.Harrison.Handbook.dp

// pg. 84
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// val it : bool = true
tautology(prime 11);;

// val it : bool = true
dptaut(prime 11);;

// pg. 85
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : bool = true
dplltaut(prime 11);;

// pg. 89
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// Note: This takes a long time. So long that I canceled it after 15 minutes.
// TODO: Run this at night and time it.
dplitaut(prime 101);;

// val it : bool = true
dplbtaut(prime 101);;