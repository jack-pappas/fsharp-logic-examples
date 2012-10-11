// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.defcnf

open LanguagePrimitives
open FSharpx.Compatibility.OCaml.Num


fsi.AddPrinter sprint_prop_formula

// pg. 74
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

cnf (parse_prop_formula @"p <=> (q <=> r)");;

// pg. 77
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

defcnfOrig (parse_prop_formula @"(p \/ (q /\ ~r)) /\ s");;

// pg. 78
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

defcnf (parse_prop_formula @"(p \/ (q /\ ~r)) /\ s");;
