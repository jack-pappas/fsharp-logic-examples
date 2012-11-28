// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.defcnf

fsi.AddPrinter sprint_prop_formula

// pg. 74
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// defcnf.p001
cnf (parse_prop_formula @"p <=> (q <=> r)");;

// pg. 77
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// defcnf.p002
defcnfOrig (parse_prop_formula @"(p \/ (q /\ ~r)) /\ s");;

// pg. 78
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// defcnf.p003
defcnf (parse_prop_formula @"(p \/ (q /\ ~r)) /\ s");;
