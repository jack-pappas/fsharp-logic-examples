// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand

// pg. 161
// ------------------------------------------------------------------------- //
// First example and a little tracing.                                       //
// ------------------------------------------------------------------------- //

gilmore (parse "exists x. forall y. P(x) ==> P(y)");;

let sfm = skolemize(Not (parse "exists x. forall y. P(x) ==> P(y)"));;
print_fol_formula sfm;;

// pg. 161
// ------------------------------------------------------------------------- //
// Quick example.                                                            //
// ------------------------------------------------------------------------- //

let p24 = gilmore (parse "~(exists x. U(x) /\ Q(x)) 
/\ (forall x. P(x) ==> Q(x) \/ R(x)) 
/\ ~(exists x. P(x) ==> (exists x. Q(x))) 
/\ (forall x. Q(x) 
/\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))");;

// pg. 162
// ------------------------------------------------------------------------- //
// Slightly less easy example.                                               //
// ------------------------------------------------------------------------- //

// Run the example with 10MB stack size.
let p45 = Initialization.runWithStackFrame 10000000 (fun () -> gilmore (parse "(forall x. P(x) 
                            /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) 
                            /\ ~(exists y. L(y) /\ R(y)) 
                            /\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) 
                            /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))"));;

// pg. 162
// ------------------------------------------------------------------------- //
// Apparently intractable example.                                           //
// ------------------------------------------------------------------------- //

//let p20 = gilmore (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
//                           ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// pg. 163
// ------------------------------------------------------------------------- //
// Show how much better than the Gilmore procedure this can be.              //
// ------------------------------------------------------------------------- //

let p20dp = davisputnam (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p36 = davisputnam' (parse "(forall x. exists y. P(x,y)) 
/\ (forall x. exists y. G(x,y)) 
/\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
==> (forall x. exists y. H(x,y))");;

let p29 = davisputnam' (parse "(exists x. P(x)) /\ (exists x. G(x)) ==>
((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
(forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;
