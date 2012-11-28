// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop

fsi.AddPrinter sprint_thm
        
// pg. 488
// ------------------------------------------------------------------------- //
// The examples in the text.                                                 //
// ------------------------------------------------------------------------- //

// lcfprop.p001
// Pelletier #16
lcftaut (parse @"(p ==> q) \/ (q ==> p)") ;;

// lcfprop.p002
// Harrison #02 - Equations within equations
lcftaut (parse @"p /\ q <=> ((p <=> q) <=> p \/ q)");;

// lcfprop.p003
// Pelletier #12
lcftaut (parse @"((p <=> q) <=> r) <=> (p <=> (q <=> r))");;
