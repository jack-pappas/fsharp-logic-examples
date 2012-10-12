// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.prolog
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.skolem

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