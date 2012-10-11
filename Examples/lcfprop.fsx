// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop

fsi.AddPrinter sprint_thm
        
// pg. 488
// ------------------------------------------------------------------------- //
// The examples in the text.                                                 //
// ------------------------------------------------------------------------- //

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Or
//     (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),
//      Imp (Atom (R ("q",[])),Atom (R ("p",[]))))
lcftaut (parse @"(p ==> q) \/ (q ==> p)") |> sprint_thm;;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Iff
//     (And (Atom (R ("p",[])),Atom (R ("q",[]))),
//      Iff
//        (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),
//         Or (Atom (R ("p",[])),Atom (R ("q",[])))))
lcftaut (parse @"p /\ q <=> ((p <=> q) <=> p \/ q)") |> sprint_thm;;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Iff
//     (Iff (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),Atom (R ("r",[]))),
//      Iff (Atom (R ("p",[])),Iff (Atom (R ("q",[])),Atom (R ("r",[])))))
lcftaut (parse @"((p <=> q) <=> r) <=> (p <=> (q <=> r))") |> sprint_thm;;