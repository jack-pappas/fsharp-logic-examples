// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.skolems

fsi.AddPrinter sprint_fol_formula

// TODO: skolems is missing unit test.

// pg. 226

// skolems.p001
skolemizes [
        parse @"exists x y. x + y = 2";
        parse @"forall x. exists y. x + 1 = y"; ];;