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

lcftaut (parse @"(p ==> q) \/ (q ==> p)") ;;

lcftaut (parse @"p /\ q <=> ((p <=> q) <=> p \/ q)");;

lcftaut (parse @"((p <=> q) <=> r) <=> (p <=> (q <=> r))");;
