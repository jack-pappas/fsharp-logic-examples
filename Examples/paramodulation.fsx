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
open Reasoning.Automated.Harrison.Handbook.resolution
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.completion
open Reasoning.Automated.Harrison.Handbook.paramodulation
 
// pg. 302
// ------------------------------------------------------------------------- //
// Test.                                                                     //
// ------------------------------------------------------------------------- //

paramodulation 
    (parse @"
    (forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
    ==> forall x. f(x) = x");;
