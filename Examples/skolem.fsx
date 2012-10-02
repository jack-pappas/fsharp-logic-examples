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
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.skolem

// pg. 140
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

print_fol_formula (simplify004 (parse "(forall x y. P(x) \/ (P(y) /\ false)) ==> exists z. Q"));;

// pg. 141
// ------------------------------------------------------------------------- //
// Example of NNF function in action.                                        //
// ------------------------------------------------------------------------- //

print_fol_formula (nnf (parse "(forall x. P(x)) ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))"));;

// pg. 144
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

print_fol_formula (pnf (parse "(forall x. P(x) \/ R(y)) ==> exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z))"));;

// pg. 150
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

print_fol_formula (skolemize (parse "exists y. x < y ==> forall u. exists v. x * u < y * v"));;

print_fol_formula (skolemize
 (parse "forall x. P(x)
             ==> (exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z)))"));;