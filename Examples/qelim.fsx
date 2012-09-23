// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
//open Reasoning.Automated.Harrison.Handbook.paramodulation
open Reasoning.Automated.Harrison.Handbook.decidable
open Reasoning.Automated.Harrison.Handbook.qelim

// pg. 335
//  ------------------------------------------------------------------------- // 
//  Examples.                                                                 // 
//  ------------------------------------------------------------------------- // 

// val it : fol formula = True
quelim_dlo (parse "forall x y. exists z. z < x /\ z < y");;

// val it : fol formula = True
quelim_dlo (parse "exists z. z < x /\ z < y");;

// val it : fol formula = Atom (R ("<",[Var "x"; Var "y"]))
quelim_dlo (parse "exists z. x < z /\ z < y");;

// val it : fol formula =
//   Not
//     (Or (Atom (R ("<",[Var "b"; Var "a"])),Atom (R ("<",[Var "b"; Var "a"]))))
quelim_dlo (parse "(forall x. x < a ==> x < b)");;

// val it : fol formula = True
quelim_dlo (parse "forall a b. (forall x. x < a ==> x < b) <=> a <= b");;

// val it : fol formula = True
quelim_dlo (parse "forall a b. (forall x. x < a <=> x < b) <=> a = b");;

// val it : fol formula = False
quelim_dlo (parse "exists x y z. forall u.
                 x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)");;

//  ------------------------------------------------------------------------- // 
//  More tests (not in the text).                                             // 
//  ------------------------------------------------------------------------- // 

// CPU time (user): 0.000000
// val it : fol formula = True
time quelim_dlo (parse "forall x. exists y. x < y");;

time quelim_dlo (parse "forall x y z. x < y /\ y < z ==> x < z");;

time quelim_dlo (parse "forall x y. x < y \/ (x = y) \/ y < x");;

time quelim_dlo (parse "exists x y. x < y /\ y < x");;

time quelim_dlo (parse "forall x y. exists z. z < x /\ x < y");;

time quelim_dlo (parse "exists z. z < x /\ x < y");;

time quelim_dlo (parse "forall x y. exists z. z < x /\ z < y");;

time quelim_dlo (parse "forall x y. x < y ==> exists z. x < z /\ z < y");;

time quelim_dlo
  (parse "forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)");;

time quelim_dlo (parse "exists x. x = x");;

time quelim_dlo (parse "exists x. x = x /\ x = y");;

time quelim_dlo (parse "exists z. x < z /\ z < y");;

time quelim_dlo (parse "exists z. x <= z /\ z <= y");;

time quelim_dlo (parse "exists z. x < z /\ z <= y");;

time quelim_dlo (parse "forall x y z. exists u. u < x /\ u < y /\ u < z");;

time quelim_dlo (parse "forall y. x < y /\ y < z ==> w < z");;

time quelim_dlo (parse "forall x y. x < y");;

time quelim_dlo (parse "exists z. z < x /\ x < y");;

time quelim_dlo (parse "forall a b. (forall x. x < a ==> x < b) <=> a <= b");;

time quelim_dlo (parse "forall x. x < a ==> x < b");;

time quelim_dlo (parse "forall x. x < a ==> x <= b");;

time quelim_dlo (parse "forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)");;

time quelim_dlo (parse "forall x y. x <= y \/ x > y");;

time quelim_dlo (parse "forall x y. x <= y \/ x < y");;
