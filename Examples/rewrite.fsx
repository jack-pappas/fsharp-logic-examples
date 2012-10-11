// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.resolution
open Reasoning.Automated.Harrison.Handbook.rewrite

fsi.AddPrinter sprint_term

// pg. 263
// ------------------------------------------------------------------------- //
// Example: 3 * 2 + 4 in successor notation.                                 //
// ------------------------------------------------------------------------- //

rewrite 
    [
    parse @"0 + x = x";
    parse @"S(x) + y = S(x + y)";
    parse @"0 * x = 0";
    parse @"S(x) * y = y + x * y"; 
    ]
    (parset @"S(S(S(0))) * S(S(0)) + S(S(S(S(0))))");;
