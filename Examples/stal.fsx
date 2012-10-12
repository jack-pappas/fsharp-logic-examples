// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples
open FSharpx.Books.AutomatedReasoning.defcnf
open FSharpx.Books.AutomatedReasoning.dp
open FSharpx.Books.AutomatedReasoning.stal

open FSharpx.Compatibility.OCaml
open Num

// pg. 94
// ------------------------------------------------------------------------- //
// An example.                                                               //
// ------------------------------------------------------------------------- //

triggers (parse_prop_formula @"p <=> (q /\ r)");;

// pg. 99
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

time stalmarck (mk_adder_test 6 3);;