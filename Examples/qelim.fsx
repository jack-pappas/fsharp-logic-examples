// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.decidable
open Reasoning.Automated.Harrison.Handbook.qelim

fsi.AddPrinter sprint_fol_formula

// pg. 335
//  ------------------------------------------------------------------------- // 
//  Examples.                                                                 // 
//  ------------------------------------------------------------------------- // 

quelim_dlo (parse @"
    forall x y. exists z. z < x /\ z < y") 
    ;;

quelim_dlo (parse @"
    exists z. z < x /\ z < y")
    ;;

quelim_dlo (parse @"
    exists z. x < z /\ z < y")
    ;;

quelim_dlo (parse @"
    (forall x. x < a ==> x < b)")
    ;;

quelim_dlo (parse @"
    forall a b. (forall x. x < a ==> x < b) <=> a <= b")
    ;;

quelim_dlo (parse @"
    forall a b. (forall x. x < a <=> x < b) <=> a = b")
    ;;

quelim_dlo (parse @"
    exists x y z. forall u.
        x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)")
    ;;

//  ------------------------------------------------------------------------- // 
//  More tests (not in the text).                                             // 
//  ------------------------------------------------------------------------- // 

time quelim_dlo (parse @"
    forall x. exists y. x < y")
    ;;

time quelim_dlo (parse @"
    forall x y z. x < y /\ y < z ==> x < z")
    ;;

time quelim_dlo (parse @"
    forall x y. x < y \/ (x = y) \/ y < x")
    ;;

time quelim_dlo (parse @"
    exists x y. x < y /\ y < x")
    ;;

time quelim_dlo (parse @"
    forall x y. exists z. z < x /\ x < y")
    ;;

time quelim_dlo (parse @"
    exists z. z < x /\ x < y")
    ;;

time quelim_dlo (parse @"
    forall x y. exists z. z < x /\ z < y")
    ;;

time quelim_dlo (parse @"
    forall x y. x < y ==> exists z. x < z /\ z < y")
    ;;

time quelim_dlo (parse @"
    forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)")
    ;;

time quelim_dlo (parse @"
    exists x. x = x")
    ;;

time quelim_dlo (parse @"
    exists x. x = x /\ x = y")
    ;;

time quelim_dlo (parse @"
    exists z. x < z /\ z < y")
    ;;

time quelim_dlo (parse @"
    exists z. x <= z /\ z <= y")
    ;;

time quelim_dlo (parse @"
    exists z. x < z /\ z <= y")
    ;;

time quelim_dlo (parse @"
    forall x y z. exists u. u < x /\ u < y /\ u < z")
    ;;

time quelim_dlo (parse @"
    forall y. x < y /\ y < z ==> w < z")
    ;;

time quelim_dlo (parse @"
    forall x y. x < y")
    ;;

time quelim_dlo (parse @"
    exists z. z < x /\ x < y")
    ;;

time quelim_dlo (parse @"
    forall a b. (forall x. x < a ==> x < b) <=> a <= b")
    ;;

time quelim_dlo (parse @"
    forall x. x < a ==> x < b")
    ;;

time quelim_dlo (parse @"
    forall x. x < a ==> x <= b")
    ;;

time quelim_dlo (parse @"
    forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)")
    ;;

time quelim_dlo (parse @"
    forall x y. x <= y \/ x > y")
    ;;

time quelim_dlo (parse @"
    forall x y. x <= y \/ x < y")
    ;;
