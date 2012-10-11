// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.unif

fsi.AddPrinter sprint_term

// pg. 171
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

unify_and_apply [(parset @"f(x,g(y))"),(parset @"f(f(z),w)")];;

unify_and_apply [(parset @"f(x,y)"),(parset @"f(y,x)")];;

unify_and_apply [(parset @"f(x,g(y))"),(parset @"f(y,x)")];;

unify_and_apply [(parset @"x_0"),(parset @"f(x_1,x_1)");
                 (parset @"x_1"),(parset @"f(x_2,x_2)");
                 (parset @"x_2"),(parset @"f(x_3,x_3)")];;
