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
//open Reasoning.Automated.Harrison.Handbook.skolems
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
open Reasoning.Automated.Harrison.Handbook.order

// ------------------------------------------------------------------------- //
// This fails the rewrite properties.                                        //
// ------------------------------------------------------------------------- //

// val s : Reasoning.Automated.Harrison.Handbook.folMod.term =
//   Fn ("f",[Var "x"; Var "x"; Var "x"])
let s = parset "f(x,x,x)";;

// val t : term = Fn ("g",[Var "x"; Var "y"])
let t = parset "g(x,y)";;

// val it : bool = true
termsize s > termsize t;;

// val i : func<string,term> =
//   Leaf (-842352681,[("y", Fn ("f",[Var "x"; Var "x"; Var "x"]))])
let i = ("y" |=> parset "f(x,x,x)");;

// val it : bool = false
termsize (tsubst i s) > termsize (tsubst i t);;
