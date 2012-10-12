// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.order

fsi.AddPrinter sprint_term

// ------------------------------------------------------------------------- //
// This fails the rewrite properties.                                        //
// ------------------------------------------------------------------------- //

let s = parset @"f(x,x,x)";;

let t = parset @"g(x,y)";;

termsize s > termsize t;;

let i = "y" |=> parset @"f(x,x,x)";;

termsize (tsubst i s) > termsize (tsubst i t);;
