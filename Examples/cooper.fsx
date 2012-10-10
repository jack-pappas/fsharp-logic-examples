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
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
//open Reasoning.Automated.Harrison.Handbook.paramodulation
//open Reasoning.Automated.Harrison.Handbook.decidable
open Reasoning.Automated.Harrison.Handbook.qelim
open Reasoning.Automated.Harrison.Handbook.cooper

// pg.349
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// coo.p001
integer_qelim
    (parse @"forall x y. ~(2 * x + 1 = 2 * y)")
    |> print_fol_formula;;

// coo.p002
integer_qelim 
    (parse @"forall x. exists y. 2 * y <= x /\ x < 2 * (y + 1)")
    |> print_fol_formula;;

// coo.p003
integer_qelim 
    (parse @"exists x y. 4 * x - 6 * y = 1")
    |> print_fol_formula;;

// coo.p004
integer_qelim 
    (parse @"forall x. ~divides(2,x) /\ divides(3,x-1) <=>
        divides(12,x-1) \/ divides(12,x-7)")
    |> print_fol_formula;;

// coo.p005
integer_qelim 
    (parse @"forall x. b < x ==> a <= x")
    |> print_fol_formula;;

// coo.p006
natural_qelim 
    (parse @"forall d. exists x y. 3 * x + 5 * y = d")
    |> print_fol_formula;;

// coo.p007
integer_qelim 
    (parse @"forall d. exists x y. 3 * x + 5 * y = d")
    |> print_fol_formula;;

// coo.p008
natural_qelim 
    (parse @"forall d. d >= 8 ==> exists x y. 3 * x + 5 * y = d")
    |> print_fol_formula;;

// coo.p009
natural_qelim 
    (parse @"forall d. exists x y. 3 * x - 5 * y = d")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Other tests, not in the main text.                                        //
// ------------------------------------------------------------------------- //

// coo.p010
integer_qelim 
    (parse @"exists x y. x > 0 /\ y >= 0 /\ 3 * x - 5 * y = 1")
    |> print_fol_formula;;

// coo.p011
integer_qelim 
    (parse @"exists x y z. 4 * x - 6 * y = 1")
    |> print_fol_formula;;

// coo.p012
integer_qelim 
    (parse @"forall x. a < 3 * x ==> b < 3 * x")
    |> print_fol_formula;;

// coo.p013
time integer_qelim 
    (parse @"forall x y. x <= y ==> 2 * x + 1 < 2 * y")
    |> print_fol_formula;;

// coo.p014
time integer_qelim 
    (parse @"(exists d. y = 65 * d) ==> (exists d. y = 5 * d)")
    |> print_fol_formula;;

// coo.p015
time integer_qelim 
    (parse @"forall y. (exists d. y = 65 * d) ==> (exists d. y = 5 * d)")
    |> print_fol_formula;;

// coo.p016
time integer_qelim 
    (parse @"forall x y. ~(2 * x + 1 = 2 * y)")
    |> print_fol_formula;;

// coo.p017
time integer_qelim 
    (parse @"forall x y z. (2 * x + 1 = 2 * y) ==> x + y + z > 129")
    |> print_fol_formula;;

// coo.p018
time integer_qelim 
    (parse @"forall x. a < x ==> b < x")
    |> print_fol_formula;;

// coo.p019
time integer_qelim 
    (parse @"forall x. a <= x ==> b < x")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Formula examples from Cooper's paper.                                     //
// ------------------------------------------------------------------------- //

// coo.p020
time integer_qelim 
    (parse @"forall a b. exists x. a < 20 * x /\ 20 * x < b")
    |> print_fol_formula;;

// coo.p021
time integer_qelim 
    (parse @"exists x. a < 20 * x /\ 20 * x < b")
    |> print_fol_formula;;

// coo.p022
time integer_qelim 
    (parse @"forall b. exists x. a < 20 * x /\ 20 * x < b")
    |> print_fol_formula;;

// coo.p023
time integer_qelim 
    (parse @"forall a. exists b. a < 4 * b + 3 * a \/ (~(a < b) /\ a > b + 1)")
    |> print_fol_formula;;

// coo.p024
time integer_qelim 
    (parse @"exists y. forall x. x + 5 * y > 1 /\ 13 * x - y > 1 /\ x + 2 < 0")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// More of my own.                                                           //
// ------------------------------------------------------------------------- //

// coo.p025
time integer_qelim 
    (parse @"forall x y. x >= 0 /\ y >= 0 ==> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2")
    |> print_fol_formula;;

// coo.p026
time integer_qelim 
    (parse @"exists x y. 5 * x + 3 * y = 1")
    |> print_fol_formula;;

// coo.p027
time integer_qelim 
    (parse @"exists x y. 5 * x + 10 * y = 1")
    |> print_fol_formula;;

// coo.p028
time integer_qelim 
    (parse @"exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 6 * y = 1")
    |> print_fol_formula;;

// coo.p029
time integer_qelim 
    (parse @"exists w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1")
    |> print_fol_formula;;

// coo.p030
time integer_qelim 
    (parse @"exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 3 * y = 1")
    |> print_fol_formula;;

// coo.p031
time integer_qelim 
    (parse @"exists x y. x >= 0 /\ y >= 0 /\ 3 * x - 5 * y = 1")
    |> print_fol_formula;;

// coo.p032
time integer_qelim 
    (parse @"exists x y. x >= 0 /\ y >= 0 /\ 6 * x - 3 * y = 1")
    |> print_fol_formula;;

// coo.p033
time integer_qelim 
    (parse @"forall x y. ~(x = 0) ==> 5 * y < 6 * x \/ 5 * y > 6 * x")
    |> print_fol_formula;;

// coo.p034
time integer_qelim 
    (parse @"forall x y. ~divides(5,x) /\ ~divides(6,y) ==> ~(6 * x = 5 * y)")
    |> print_fol_formula;;

// coo.p035
time integer_qelim 
    (parse @"forall x y. ~divides(5,x) ==> ~(6 * x = 5 * y)")
    |> print_fol_formula;;

// coo.p036
time integer_qelim 
    (parse @"forall x y. ~(6 * x = 5 * y)")
    |> print_fol_formula;;

// coo.p037
time integer_qelim 
    (parse @"forall x y. 6 * x = 5 * y ==> exists d. y = 3 * d")
    |> print_fol_formula;;

// coo.p038
time integer_qelim 
    (parse @"6 * x = 5 * y ==> exists d. y = 3 * d")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Positive variant of the Bezout theorem (see the exercise).                //
// ------------------------------------------------------------------------- //

// coo.p039
time integer_qelim 
    (parse @"forall z. z > 7 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z")
    |> print_fol_formula;;

// coo.p040
time integer_qelim 
    (parse @"forall z. z > 2 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z")
    |> print_fol_formula;;

// coo.p041
time integer_qelim 
    (parse @"forall z. z <= 7 ==> ((exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z) <=> ~(exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = 7 - z))")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Basic result about congruences.                                           //
// ------------------------------------------------------------------------- //

// coo.p042
time integer_qelim 
    (parse @"forall x. ~divides(2,x) /\ divides(3,x-1) <=> divides(12,x-1) \/ divides(12,x-7)")
    |> print_fol_formula;;

// coo.p043
time integer_qelim 
    (parse @"forall x. ~(exists m. x = 2 * m) /\ (exists m. x = 3 * m + 1) <=> (exists m. x = 12 * m + 1) \/ (exists m. x = 12 * m + 7)")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Something else.                                                           //
// ------------------------------------------------------------------------- //

// coo.p044
time integer_qelim
    (parse @"forall x.
        ~(divides(2,x))
        ==> divides(4,x-1) \/
            divides(8,x-1) \/
            divides(8,x-3) \/
            divides(6,x-1) \/
            divides(14,x-1) \/
            divides(14,x-9) \/
            divides(14,x-11) \/
            divides(24,x-5) \/
            divides(24,x-11)")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Testing fix for an earlier version with negative result from formlcm.     //
// ------------------------------------------------------------------------- //

// coo.p045
(integer_qelim << generalize)
    (parse @"a + 2 = b /\ v_3 = b - a + 1 /\ v_2 = b - 2 /\ v_1 = 3 ==> false")
    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Inspired by the Collatz conjecture.                                       //
// ------------------------------------------------------------------------- //

// coo.p046
integer_qelim
    (parse @"exists a b. ~(a = 1) /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)")
    |> print_fol_formula;;

// coo.p047
integer_qelim
    (parse @"exists a b. a > 1 /\ b > 1 /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)")
    |> print_fol_formula;;

// coo.p048
integer_qelim
    (parse @"exists a b. a > 1 /\ b > 1 /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ ((2 * a = b) \/ (2 * a = 3 * b + 1))")
    |> print_fol_formula;;

let fm001 = 
    dnf (parse @"((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ ((2 * c = b) \/ (2 * c = 3 * b + 1)) /\ ((2 * d = c) \/ (2 * d = 3 * c + 1)) /\ ((2 * e = d) \/ (2 * e = 3 * d + 1)) /\ ((2 * f = e) \/ (2 * f = 3 * e + 1)) /\ (f = a)");;

let fms = 
    List.map (List.foldBack (fun x p -> Exists(x,And(Atom(R(">",[Var x; Fn("1",[])])),p))) ["b"; "c"; "d"; "e"; "f"]) (disjuncts fm001);;

let fm002 = 
    List.nth fms 15;;

// coo.p049
// long running
//integer_qelim fm002
//    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Bob Constable's "stamp problem".                                          //
// ------------------------------------------------------------------------- //

// coo.p050
integer_qelim
    (parse @"forall x. x >= 8 ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v")
    |> print_fol_formula;;

// coo.p051
integer_qelim
    (parse @"exists l.  forall x. x >= l
         ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v")
    |> print_fol_formula;;

// coo.p052
integer_qelim
    (parse @"exists l.
        forall x. x >= l
            ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 7 * v")
    |> print_fol_formula;;

//*********** These seem to take a while --- the second may not be feasible
//            although the first is not so bad.

// coo.p053
integer_qelim
    (parse @"exists l.
        forall x. x >= l
            ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 8 * v")
    |> print_fol_formula;;

// coo.p054
// long running
//integer_qelim
//    (parse @"exists l.
//        forall x. x >= l
//            ==> exists u v. u >= 0 /\ v >= 0 /\ x = 7 * u + 8 * v")
//    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Example from reciprocal mult: (2622 * x)")16 = x/100 within a range.      //
// ------------------------------------------------------------------------- //

// coo.p055
// long running
//integer_qelim
//    (parse @"forall x q1 q2 r1 r2.
//        x < 4699 /\ 
//        2622 * x = 65536 * q1 + r1 /\ 0 <= q1 /\ 0 <= r1 /\ r1 < 65536 /\ 
//        x = 100 * q2 + r2 /\ 0 <= q2 /\ 0 <= r2 /\ r2 < 100
//        ==> q1 = q2")
//    |> print_fol_formula;;

// ------------------------------------------------------------------------- //
// Yet more.                                                                 //
// ------------------------------------------------------------------------- //

// coo.p056
integer_qelim
    (parse @"forall x y.
        (exists d. x + y = 2 * d) <=>
        ((exists d. x = 2 * d) <=> (exists d. y = 2 * d))")
    |> print_fol_formula;;

// coo.p057
// long running
//*** Landau trick! Is it too slow?
//integer_qelim
//    (parse @"forall n.
//     0 < n /\ n < 2400
//        ==> n <= 2 /\ 2 <= 2 * n \/
//            n <= 3 /\ 3 <= 2 * n \/
//            n <= 5 /\ 5 <= 2 * n \/
//            n <= 7 /\ 7 <= 2 * n \/
//            n <= 13 /\ 13 <= 2 * n \/
//            n <= 23 /\ 23 <= 2 * n \/
//            n <= 43 /\ 43 <= 2 * n \/
//            n <= 83 /\ 83 <= 2 * n \/
//            n <= 163 /\ 163 <= 2 * n \/
//            n <= 317 /\ 317 <= 2 * n \/
//            n <= 631 /\ 631 <= 2 * n \/
//            n <= 1259 /\ 1259 <= 2 * n \/
//            n <= 2503 /\ 2503 <= 2 * n")
//    |> print_fol_formula;;
