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
open FSharpx.Books.AutomatedReasoning.resolution
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.completion
open FSharpx.Books.AutomatedReasoning.paramodulation
 
// pg. 302
// ------------------------------------------------------------------------- //
// Test.                                                                     //
// ------------------------------------------------------------------------- //

// paramodulation.p001
paramodulation 
    (parse @"
    (forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
    ==> forall x. f(x) = x");;
