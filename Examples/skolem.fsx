// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.skolem

fsi.AddPrinter sprint_fol_formula

// pg. 140
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

(simplify (parse @"(forall x y. P(x) \/ (P(y) /\ false)) ==> exists z. Q"));;

// pg. 141
// ------------------------------------------------------------------------- //
// Example of NNF function in action.                                        //
// ------------------------------------------------------------------------- //

(nnf (parse @"(forall x. P(x)) ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))"));;

// pg. 144
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

(pnf (parse @"(forall x. P(x) \/ R(y)) ==> exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z))"));;

// pg. 150
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

(skolemize (parse @"exists y. x < y ==> forall u. exists v. x * u < y * v"));;

(skolemize
 (parse @"forall x. P(x)
             ==> (exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z)))"));;