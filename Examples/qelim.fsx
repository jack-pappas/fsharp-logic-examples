// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.decidable
open FSharpx.Books.AutomatedReasoning.qelim

fsi.AddPrinter sprint_fol_formula

// pg. 335
//  ------------------------------------------------------------------------- // 
//  Examples.                                                                 // 
//  ------------------------------------------------------------------------- // 

// qelim.p001
quelim_dlo (parse @"
    forall x y. exists z. z < x /\ z < y") 
    ;;

// qelim.p002
quelim_dlo (parse @"
    exists z. z < x /\ z < y")
    ;;

// qelim.p003
quelim_dlo (parse @"
    exists z. x < z /\ z < y")
    ;;

// qelim.p004
quelim_dlo (parse @"
    (forall x. x < a ==> x < b)")
    ;;

// qelim.p005
quelim_dlo (parse @"
    forall a b. (forall x. x < a ==> x < b) <=> a <= b")
    ;;

// qelim.p006
quelim_dlo (parse @"
    forall a b. (forall x. x < a <=> x < b) <=> a = b")
    ;;

// qelim.p007
quelim_dlo (parse @"
    exists x y z. forall u.
        x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)")
    ;;

//  ------------------------------------------------------------------------- // 
//  More tests (not in the text).                                             // 
//  ------------------------------------------------------------------------- // 

// qelim.p008
time quelim_dlo (parse @"
    forall x. exists y. x < y")
    ;;

// qelim.p009
time quelim_dlo (parse @"
    forall x y z. x < y /\ y < z ==> x < z")
    ;;

// qelim.p010
time quelim_dlo (parse @"
    forall x y. x < y \/ (x = y) \/ y < x")
    ;;

// qelim.p011
time quelim_dlo (parse @"
    exists x y. x < y /\ y < x")
    ;;

// qelim.p012
time quelim_dlo (parse @"
    forall x y. exists z. z < x /\ x < y")
    ;;
    
// qelim.p013
time quelim_dlo (parse @"
    exists z. z < x /\ x < y")
    ;;
    
// qelim.p014
time quelim_dlo (parse @"
    forall x y. exists z. z < x /\ z < y")
    ;;
    
// qelim.p015
time quelim_dlo (parse @"
    forall x y. x < y ==> exists z. x < z /\ z < y")
    ;;
    
// qelim.p016
time quelim_dlo (parse @"
    forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)")
    ;;
    
// qelim.p017
time quelim_dlo (parse @"
    exists x. x = x")
    ;;
    
// qelim.p018
time quelim_dlo (parse @"
    exists x. x = x /\ x = y")
    ;;
    
// qelim.p019
time quelim_dlo (parse @"
    exists z. x < z /\ z < y")
    ;;
    
// qelim.p020
time quelim_dlo (parse @"
    exists z. x <= z /\ z <= y")
    ;;
    
// qelim.p021
time quelim_dlo (parse @"
    exists z. x < z /\ z <= y")
    ;;
    
// qelim.p022
time quelim_dlo (parse @"
    forall x y z. exists u. u < x /\ u < y /\ u < z")
    ;;
    
// qelim.p023
time quelim_dlo (parse @"
    forall y. x < y /\ y < z ==> w < z")
    ;;
    
// qelim.p024
time quelim_dlo (parse @"
    forall x y. x < y")
    ;;
    
// qelim.p025
time quelim_dlo (parse @"
    exists z. z < x /\ x < y")
    ;;
    
// qelim.p026
time quelim_dlo (parse @"
    forall a b. (forall x. x < a ==> x < b) <=> a <= b")
    ;;
    
// qelim.p027
time quelim_dlo (parse @"
    forall x. x < a ==> x < b")
    ;;
    
// qelim.p028
time quelim_dlo (parse @"
    forall x. x < a ==> x <= b")
    ;;
    
// qelim.p029
time quelim_dlo (parse @"
    forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)")
    ;;
    
// qelim.p030
time quelim_dlo (parse @"
    forall x y. x <= y \/ x > y")
    ;;
    
// qelim.p031
time quelim_dlo (parse @"
    forall x y. x <= y \/ x < y")
    ;;
