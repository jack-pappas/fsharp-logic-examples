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

// val it : FSharpx.Books.AutomatedReasoning.lcf.ProverOperators.thm =
//   Or
//     (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),
//      Imp (Atom (R ("q",[])),Atom (R ("p",[]))))
lcftaut (parse @"(p ==> q) \/ (q ==> p)") ;;

// val it : FSharpx.Books.AutomatedReasoning.lcf.ProverOperators.thm =
//   Iff
//     (And (Atom (R ("p",[])),Atom (R ("q",[]))),
//      Iff
//        (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),
//         Or (Atom (R ("p",[])),Atom (R ("q",[])))))
lcftaut (parse @"p /\ q <=> ((p <=> q) <=> p \/ q)");;

// val it : FSharpx.Books.AutomatedReasoning.lcf.ProverOperators.thm =
//   Iff
//     (Iff (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),Atom (R ("r",[]))),
//      Iff (Atom (R ("p",[])),Iff (Atom (R ("q",[])),Atom (R ("r",[])))))
lcftaut (parse @"((p <=> q) <=> r) <=> (p <=> (q <=> r))");;
