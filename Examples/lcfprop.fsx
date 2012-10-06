// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

//open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
//open Reasoning.Automated.Harrison.Handbook.formulas
//open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
//open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
//open Reasoning.Automated.Harrison.Handbook.paramodulation
//open Reasoning.Automated.Harrison.Handbook.decidable
//open Reasoning.Automated.Harrison.Handbook.qelim
//open Reasoning.Automated.Harrison.Handbook.cooper
//open Reasoning.Automated.Harrison.Handbook.complex
//open Reasoning.Automated.Harrison.Handbook.real
//open Reasoning.Automated.Harrison.Handbook.grobner
//open Reasoning.Automated.Harrison.Handbook.geom
//open Reasoning.Automated.Harrison.Handbook.interpolation
//open Reasoning.Automated.Harrison.Handbook.combining
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
        
// pg. 488
// ------------------------------------------------------------------------- //
// The examples in the text.                                                 //
// ------------------------------------------------------------------------- //

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Or
//     (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),
//      Imp (Atom (R ("q",[])),Atom (R ("p",[]))))
lcftaut (parse "(p ==> q) \/ (q ==> p)");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Iff
//     (And (Atom (R ("p",[])),Atom (R ("q",[]))),
//      Iff
//        (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),
//         Or (Atom (R ("p",[])),Atom (R ("q",[])))))
lcftaut (parse "p /\ q <=> ((p <=> q) <=> p \/ q)");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Iff
//     (Iff (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),Atom (R ("r",[]))),
//      Iff (Atom (R ("p",[])),Iff (Atom (R ("q",[])),Atom (R ("r",[])))))
lcftaut (parse "((p <=> q) <=> r) <=> (p <=> (q <=> r))");;