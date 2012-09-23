// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
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
open Reasoning.Automated.Harrison.Handbook.unif

// pg. 171
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// val it : (term * term) list =
//   [(Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]),
//     Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]))]
unify_and_apply [(parset "f(x,g(y))"),(parset "f(f(z),w)")];;

// val it : (term * term) list =
//   [(Fn ("f",[Var "y"; Var "y"]), 
//     Fn ("f",[Var "y"; Var "y"]))]
unify_and_apply [(parset "f(x,y)"),(parset "f(y,x)")];;

// System.Exception: cyclic
unify_and_apply [(parset "f(x,g(y))"),(parset "f(y,x)")];;

// val it : (term * term) list =
//   [(Fn
//       ("f",
//        [Fn
//           ("f",
//            [Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]);
//         Fn
//           ("f",
//            [Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])])]),
//     Fn
//       ("f",
//        [Fn
//           ("f",
//            [Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]);
//         Fn
//           ("f",
//            [Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])])]));
//    (Fn
//       ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]),
//     Fn
//       ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]));
//    (Fn ("f",[Var "x_3"; Var "x_3"]), Fn ("f",[Var "x_3"; Var "x_3"]))]
unify_and_apply [(parset "x_0"),(parset "f(x_1,x_1)");
                 (parset "x_1"),(parset "f(x_2,x_2)");
                 (parset "x_2"),(parset "f(x_3,x_3)")];;
