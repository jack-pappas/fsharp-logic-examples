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
//open Reasoning.Automated.Harrison.Handbook.unif
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.skolems

// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",[Fn ("old_+",[Fn ("c_x",[]); Fn ("c_y",[])]); Fn ("old_2",[])]));
//    Forall
//      ("x",
//       Atom
//         (R ("=",
//             [Fn ("old_+",[Var "x"; Fn ("old_1",[])]); Fn ("f_y",[Var "x"])])))]
skolemizes [(parse "exists x y. x + y = 2");
            (parse "forall x. exists y. x + 1 = y")];;