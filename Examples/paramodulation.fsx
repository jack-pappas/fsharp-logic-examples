// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

//open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
//open Reasoning.Automated.Harrison.Handbook.formulas
//open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
//open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
open Reasoning.Automated.Harrison.Handbook.paramodulation
 
// pg. 302
// ------------------------------------------------------------------------- //
// Test.                                                                     //
// ------------------------------------------------------------------------- //

// 0 used; 4 unused.
// 1 used; 3 unused.
// 2 used; 4 unused.
// 3 used; 8 unused.
// 4 used; 11 unused.
// 5 used; 13 unused.
// 6 used; 21 unused.
// 7 used; 40 unused.
// 8 used; 64 unused.
// 9 used; 83 unused.
// 10 used; 108 unused.
// 11 used; 125 unused.
// val it : bool list = [true]
paramodulation
 (parse "(forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
   ==> forall x. f(x) = x");;
