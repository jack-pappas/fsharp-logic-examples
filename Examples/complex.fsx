// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
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
open Reasoning.Automated.Harrison.Handbook.complex

//  pg. 355
//  ------------------------------------------------------------------------- //
//  Sanity check.                                                             //
//  ------------------------------------------------------------------------- //

polyatom ["w"; "x"; "y"; "z"] (parse
    @"((w + x)^4 + (w + y)^4 + (w + z)^4 + (x + y)^4 + (x + z)^4 + (y + z)^4 + (w - x)^4 + (w - y)^4 + (w - z)^4 + (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 = (w^2 + x^2 + y^2 + z^2)^2");;

//  pg. 366
//  ------------------------------------------------------------------------- //
//  Examples.                                                                 //
//  ------------------------------------------------------------------------- //

complex_qelim (parse
    @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0");;

complex_qelim (parse
    @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0");;

complex_qelim (parse
    @"forall c.
        (forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0)
        <=> c = 1");;

complex_qelim (parse
    @"forall a b c x y.
        a * x^2 + b * x + c = 0 /\ a * y^2 + b * y + c = 0 /\ ~(x = y)
        ==> a * x * y = c /\ a * (x + y) + b = 0");;

//  ------------------------------------------------------------------------- //
//  More tests, not in the main text.                                         //
//  ------------------------------------------------------------------------- //

let polytest tm =
    time (polynate (fvt tm)) tm;;

let lagrange_4 = polytest (parset
    @"(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
        ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
    ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2)  +
        (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2)  +
        (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2)  +
        (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))");;

let lagrange_8 = polytest (parset @"((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
        (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
        ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
        (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
        (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
        (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
        (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
        (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
        (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
        (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)");;

let liouville = polytest (parset
    @"6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
        (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
        ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
        (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))");;

let fleck = polytest (parset
    @"60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
    (((x1 + x2 + x3)^6 + (x1 + x2 - x3)^6 +
        (x1 - x2 + x3)^6 + (x1 - x2 - x3)^6 +
        (x1 + x2 + x4)^6 + (x1 + x2 - x4)^6 +
        (x1 - x2 + x4)^6 + (x1 - x2 - x4)^6 +
        (x1 + x3 + x4)^6 + (x1 + x3 - x4)^6 +
        (x1 - x3 + x4)^6 + (x1 - x3 - x4)^6 +
        (x2 + x3 + x4)^6 + (x2 + x3 - x4)^6 +
        (x2 - x3 + x4)^6 + (x2 - x3 - x4)^6) +
        2 * ((x1 + x2)^6 + (x1 - x2)^6 +
            (x1 + x3)^6 + (x1 - x3)^6 +
            (x1 + x4)^6 + (x1 - x4)^6 +
            (x2 + x3)^6 + (x2 - x3)^6 +
            (x2 + x4)^6 + (x2 - x4)^6 +
            (x3 + x4)^6 + (x3 - x4)^6) +
        36 * (x1^6 + x2^6 + x3^6 + x4^6))");;

let hurwitz = polytest (parset
    @"5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
    (6 * ((x1 + x2 + x3 + x4)^8 +
            (x1 + x2 + x3 - x4)^8 +
            (x1 + x2 - x3 + x4)^8 +
            (x1 + x2 - x3 - x4)^8 +
            (x1 - x2 + x3 + x4)^8 +
            (x1 - x2 + x3 - x4)^8 +
            (x1 - x2 - x3 + x4)^8 +
            (x1 - x2 - x3 - x4)^8) +
        ((2 * x1 + x2 + x3)^8 +
        (2 * x1 + x2 - x3)^8 +
        (2 * x1 - x2 + x3)^8 +
        (2 * x1 - x2 - x3)^8 +
        (2 * x1 + x2 + x4)^8 +
        (2 * x1 + x2 - x4)^8 +
        (2 * x1 - x2 + x4)^8 +
        (2 * x1 - x2 - x4)^8 +
        (2 * x1 + x3 + x4)^8 +
        (2 * x1 + x3 - x4)^8 +
        (2 * x1 - x3 + x4)^8 +
        (2 * x1 - x3 - x4)^8 +
        (2 * x2 + x3 + x4)^8 +
        (2 * x2 + x3 - x4)^8 +
        (2 * x2 - x3 + x4)^8 +
        (2 * x2 - x3 - x4)^8 +
        (x1 + 2 * x2 + x3)^8 +
        (x1 + 2 * x2 - x3)^8 +
        (x1 - 2 * x2 + x3)^8 +
        (x1 - 2 * x2 - x3)^8 +
        (x1 + 2 * x2 + x4)^8 +
        (x1 + 2 * x2 - x4)^8 +
        (x1 - 2 * x2 + x4)^8 +
        (x1 - 2 * x2 - x4)^8 +
        (x1 + 2 * x3 + x4)^8 +
        (x1 + 2 * x3 - x4)^8 +
        (x1 - 2 * x3 + x4)^8 +
        (x1 - 2 * x3 - x4)^8 +
        (x2 + 2 * x3 + x4)^8 +
        (x2 + 2 * x3 - x4)^8 +
        (x2 - 2 * x3 + x4)^8 +
        (x2 - 2 * x3 - x4)^8 +
        (x1 + x2 + 2 * x3)^8 +
        (x1 + x2 - 2 * x3)^8 +
        (x1 - x2 + 2 * x3)^8 +
        (x1 - x2 - 2 * x3)^8 +
        (x1 + x2 + 2 * x4)^8 +
        (x1 + x2 - 2 * x4)^8 +
        (x1 - x2 + 2 * x4)^8 +
        (x1 - x2 - 2 * x4)^8 +
        (x1 + x3 + 2 * x4)^8 +
        (x1 + x3 - 2 * x4)^8 +
        (x1 - x3 + 2 * x4)^8 +
        (x1 - x3 - 2 * x4)^8 +
        (x2 + x3 + 2 * x4)^8 +
        (x2 + x3 - 2 * x4)^8 +
        (x2 - x3 + 2 * x4)^8 +
        (x2 - x3 - 2 * x4)^8) +
        60 * ((x1 + x2)^8 + (x1 - x2)^8 +
            (x1 + x3)^8 + (x1 - x3)^8 +
            (x1 + x4)^8 + (x1 - x4)^8 +
            (x2 + x3)^8 + (x2 - x3)^8 +
            (x2 + x4)^8 + (x2 - x4)^8 +
            (x3 + x4)^8 + (x3 - x4)^8) +
        6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))");;

let schur = polytest (parset
    @"22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
    (9 * ((2 * x1)^10 +
            (2 * x2)^10 +
            (2 * x3)^10 +
            (2 * x4)^10) +
        180 * ((x1 + x2)^10 + (x1 - x2)^10 +
            (x1 + x3)^10 + (x1 - x3)^10 +
            (x1 + x4)^10 + (x1 - x4)^10 +
            (x2 + x3)^10 + (x2 - x3)^10 +
            (x2 + x4)^10 + (x2 - x4)^10 +
            (x3 + x4)^10 + (x3 - x4)^10) +
        ((2 * x1 + x2 + x3)^10 +
        (2 * x1 + x2 - x3)^10 +
        (2 * x1 - x2 + x3)^10 +
        (2 * x1 - x2 - x3)^10 +
        (2 * x1 + x2 + x4)^10 +
        (2 * x1 + x2 - x4)^10 +
        (2 * x1 - x2 + x4)^10 +
        (2 * x1 - x2 - x4)^10 +
        (2 * x1 + x3 + x4)^10 +
        (2 * x1 + x3 - x4)^10 +
        (2 * x1 - x3 + x4)^10 +
        (2 * x1 - x3 - x4)^10 +
        (2 * x2 + x3 + x4)^10 +
        (2 * x2 + x3 - x4)^10 +
        (2 * x2 - x3 + x4)^10 +
        (2 * x2 - x3 - x4)^10 +
        (x1 + 2 * x2 + x3)^10 +
        (x1 + 2 * x2 - x3)^10 +
        (x1 - 2 * x2 + x3)^10 +
        (x1 - 2 * x2 - x3)^10 +
        (x1 + 2 * x2 + x4)^10 +
        (x1 + 2 * x2 - x4)^10 +
        (x1 - 2 * x2 + x4)^10 +
        (x1 - 2 * x2 - x4)^10 +
        (x1 + 2 * x3 + x4)^10 +
        (x1 + 2 * x3 - x4)^10 +
        (x1 - 2 * x3 + x4)^10 +
        (x1 - 2 * x3 - x4)^10 +
        (x2 + 2 * x3 + x4)^10 +
        (x2 + 2 * x3 - x4)^10 +
        (x2 - 2 * x3 + x4)^10 +
        (x2 - 2 * x3 - x4)^10 +
        (x1 + x2 + 2 * x3)^10 +
        (x1 + x2 - 2 * x3)^10 +
        (x1 - x2 + 2 * x3)^10 +
        (x1 - x2 - 2 * x3)^10 +
        (x1 + x2 + 2 * x4)^10 +
        (x1 + x2 - 2 * x4)^10 +
        (x1 - x2 + 2 * x4)^10 +
        (x1 - x2 - 2 * x4)^10 +
        (x1 + x3 + 2 * x4)^10 +
        (x1 + x3 - 2 * x4)^10 +
        (x1 - x3 + 2 * x4)^10 +
        (x1 - x3 - 2 * x4)^10 +
        (x2 + x3 + 2 * x4)^10 +
        (x2 + x3 - 2 * x4)^10 +
        (x2 - x3 + 2 * x4)^10 +
        (x2 - x3 - 2 * x4)^10) +
        9 * ((x1 + x2 + x3 + x4)^10 +
            (x1 + x2 + x3 - x4)^10 +
            (x1 + x2 - x3 + x4)^10 +
            (x1 + x2 - x3 - x4)^10 +
            (x1 - x2 + x3 + x4)^10 +
            (x1 - x2 + x3 - x4)^10 +
            (x1 - x2 - x3 + x4)^10 +
            (x1 - x2 - x3 - x4)^10))");;

let complex_qelim_all =
    time complex_qelim >>|> generalize;;

time complex_qelim (parse @"exists x. x + 2 = 3");;

time complex_qelim (parse @"exists x. x^2 + a = 3");;

time complex_qelim (parse @"exists x. x^2 + x + 1 = 0");;

time complex_qelim (parse @"exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0");;

time complex_qelim (parse @"exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0");;

time complex_qelim (parse @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0");;

time complex_qelim (parse @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0");;

time complex_qelim (parse @"exists a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)");;

time complex_qelim (parse @"exists x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)");;

time complex_qelim (parse @"forall x. x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0");;

time complex_qelim (parse @"forall a. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0");;

time complex_qelim (parse @"exists a b c x y.
        a * x^2 + b * x + c = 0 /\ 
        a * y^2 + b * y + c = 0 /\ 
        ~(x = y) /\ 
        ~(a * x * y = c)");;

// //** This works by a combination with grobner_decide but seems slow like this:
//
//    complex_qelim (parse
//        @"forall a b c x y.
//          ~(a = 0) /\ 
//          (forall z. a * z^2 + b * z + c = 0 <=> z = x) /\ x = y
//          ==> a * x * y = c /\ a * (x + y) + b = 0");;
//
//     *** and w/o the condition, it's false I think
//
//    complex_qelim (parse
//        @"forall a b c x y.
//          (forall z. a * z^2 + b * z + c = 0 <=> z = x \/ z = y)
//          ==> a * x * y = c /\ a * (x + y) + b = 0");;
//
//     *** because the following is!
//
//     **//
//
//    complex_qelim (parse
//        @"forall a b c x.
//            (forall z. a * z^2 + b * z + c = 0 <=> z = x)
//            ==> a * x * x = c /\ a * (x + x) + b = 0");;
//
// //** In fact we have this, tho' I don't know if that's interesting **//
//
//    complex_qelim (parse
//        @"forall x y.
//        (forall a b c. (a * x^2 + b * x + c = 0) /\ 
//                       (a * y^2 + b * y + c = 0)
//                       ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
//        <=> ~(x = y)");;
//
//    time complex_qelim (parse
//        @"forall y_1 y_2 y_3 y_4.
//         (y_1 = 2 * y_3) /\ 
//         (y_2 = 2 * y_4) /\ 
//         (y_1 * y_3 = y_2 * y_4)
//         ==> (y_1^2 = y_2^2)");;
//
//    time complex_qelim (parse
//        @"forall x y. x^2 = 2 /\ y^2 = 3
//             ==> (x * y)^2 = 6");;
//
//    time complex_qelim (parse
//        @"forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
//             ==> (x^4 + 1 = 0)");;
//
//    time complex_qelim (parse
//        @"forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
//             ==> (x^4 + 1 = 0)");;
//
//    time complex_qelim (parse
//        @"~(exists a x y. (a^2 = 2) /\ 
//                 (x^2 + a * x + 1 = 0) /\ 
//                 (y * (x^4 + 1) + 1 = 0))");;
//
//    time complex_qelim (parse @"forall x. exists y. x^2 = y^3");;
//
//    time complex_qelim (parse
//        @"forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
//                   2 * (b * x + b * z - a * y)");;
//
//    time complex_qelim (parse
//        @"forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)");;
//
//    time complex_qelim (parse
//        @"forall a b c x y. (a * x^2 + b * x + c = 0) /\ 
//                   (a * y^2 + b * y + c = 0) /\ 
//                   ~(x = y)
//                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
//
//    time complex_qelim (parse
//        @"~(forall a b c x y. (a * x^2 + b * x + c = 0) /\ 
//                     (a * y^2 + b * y + c = 0)
//                     ==> (a * x * y = c) /\ (a * (x + y) + b = 0))");;
//
//    time complex_qelim (parse
//        @"forall y_1 y_2 y_3 y_4.
//         (y_1 = 2 * y_3) /\ 
//         (y_2 = 2 * y_4) /\ 
//         (y_1 * y_3 = y_2 * y_4)
//         ==> (y_1^2 = y_2^2)");;
//
//    time complex_qelim (parse
//        @"forall a1 b1 c1 a2 b2 c2.
//            ~(a1 * b2 = a2 * b1)
//            ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)");;
//
//  ------------------------------------------------------------------------- //
//  This seems harder, so see how many quantifiers are feasible.              //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"(a * x^2 + b * x + c = 0) /\ 
//      (a * y^2 + b * y + c = 0) /\ 
//      (forall z. (a * z^2 + b * z + c = 0)
//           ==> (z = x) \/ (z = y))
//      ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
//
//    time complex_qelim (parse
//        @"forall y. (a * x^2 + b * x + c = 0) /\ 
//                (a * y^2 + b * y + c = 0) /\ 
//                (forall z. (a * z^2 + b * z + c = 0)
//                           ==> (z = x) \/ (z = y))
//                ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
//
// //*** feasible but lengthy?
//
//    time complex_qelim (parse
//        @"forall x y. (a * x^2 + b * x + c = 0) /\ 
//                  (a * y^2 + b * y + c = 0) /\ 
//                  (forall z. (a * z^2 + b * z + c = 0)
//                             ==> (z = x) \/ (z = y))
//                  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
//
//    time complex_qelim (parse
//        @"forall c x y. (a * x^2 + b * x + c = 0) /\ 
//                  (a * y^2 + b * y + c = 0) /\ 
//                  (forall z. (a * z^2 + b * z + c = 0)
//                             ==> (z = x) \/ (z = y))
//                  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
//
//     ***********//
//
// //******** This seems too hard
//
//    time complex_qelim (parse
//        @"forall a b c x y. (a * x^2 + b * x + c = 0) /\ 
//                   (a * y^2 + b * y + c = 0) /\ 
//                   (forall z. (a * z^2 + b * z + c = 0)
//                        ==> (z = x) \/ (z = y))
//                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
//
//     *************//
//
//    time complex_qelim (parse
//        @"~(forall x1 y1 x2 y2 x3 y3.
//          exists x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\ 
//                        (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2)");;
//
//    time complex_qelim (parse
//        @"forall a b c.
//          (exists x y. (a * x^2 + b * x + c = 0) /\ 
//                 (a * y^2 + b * y + c = 0) /\ 
//                 ~(x = y)) <=>
//          (a = 0) /\ (b = 0) /\ (c = 0) \/
//          ~(a = 0) /\ ~(b^2 = 4 * a * c)");;
//
//    time complex_qelim (parse
//        @"~(forall x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
//            (x1 - x0)^2 + (y1 - y0)^2 =
//            (x2 - x0)^2 + (y2 - y0)^2 /\ 
//            (x2 - x0)^2 + (y2 - y0)^2 =
//            (x3 - x0)^2 + (y3 - y0)^2 /\ 
//            (x1 - x0')^2 + (y1 - y0')^2 =
//            (x2 - x0')^2 + (y2 - y0')^2 /\ 
//            (x2 - x0')^2 + (y2 - y0')^2 =
//            (x3 - x0')^2 + (y3 - y0')^2
//            ==> x0 = x0' /\ y0 = y0')");;
//
//    time complex_qelim (parse
//        @"forall a b c.
//            a * x^2 + b * x + c = 0 /\ 
//            a * y^2 + b * y + c = 0 /\ 
//            ~(x = y)
//            ==> a * (x + y) + b = 0");;
//
//    time complex_qelim (parse
//        @"forall a b c.
//            (a * x^2 + b * x + c = 0) /\ 
//            (2 * a * y^2 + 2 * b * y + 2 * c = 0) /\ 
//            ~(x = y)
//            ==> (a * (x + y) + b = 0)");;
//
//    complex_qelim_all (parse
//        @"~(y_1 = 2 * y_3 /\ 
//        y_2 = 2 * y_4 /\ 
//        y_1 * y_3 = y_2 * y_4 /\ 
//        (y_1^2 - y_2^2) * z = 1)");;
//
//    time complex_qelim (parse
//        @"forall y_1 y_2 y_3 y_4.
//           (y_1 = 2 * y_3) /\ 
//           (y_2 = 2 * y_4) /\ 
//           (y_1 * y_3 = y_2 * y_4)
//           ==> (y_1^2 = y_2^2)");;
//
// //***********
//
//    complex_qelim_all (parse
//        @"~((c^2 = a^2 + b^2) /\ 
//         (c^2 = x0^2 + (y0 - b)^2) /\ 
//         (y0 * t1 = a + x0) /\ 
//         (y0 * t2 = a - x0) /\ 
//         ((1 - t1 * t2) * t = t1 + t2) /\ 
//         (u * (b * t - a) = 1) /\ 
//         (v1 * a + v2 * x0 + v3 * y0 = 1))");;
//
//    complex_qelim_all (parse
//        @"(c^2 = a^2 + b^2) /\ 
//       (c^2 = x0^2 + (y0 - b)^2) /\ 
//       (y0 * t1 = a + x0) /\ 
//       (y0 * t2 = a - x0) /\ 
//       ((1 - t1 * t2) * t = t1 + t2) /\ 
//       (~(a = 0) \/ ~(x0 = 0) \/ ~(y0 = 0))
//       ==> (b * t = a)");;
//
//    ********//
//
//    complex_qelim_all (parse
//        @"(x1 = u3) /\ 
//      (x1 * (u2 - u1) = x2 * u3) /\ 
//      (x4 * (x2 - u1) = x1 * (x3 - u1)) /\ 
//      (x3 * u3 = x4 * u2) /\ 
//      ~(u1 = 0) /\ 
//      ~(u3 = 0)
//      ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)");;
//
//    complex_qelim_all (parse
//        @"(u1 * x1 - u1 * u3 = 0) /\ 
//      (u3 * x2 - (u2 - u1) * x1 = 0) /\ 
//      (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\ 
//      (u3 * x4 - u2 * x3 = 0) /\ 
//      ~(u1 = 0) /\ 
//      ~(u3 = 0)
//      ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)");;
//
//    complex_qelim_all (parse
//        @"(y1 * y3 + x1 * x3 = 0) /\ 
//      (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) /\ 
//      ~(x3 = 0) /\ 
//      ~(y3 = 0)
//      ==> (y1 * (x2 - x3) = x1 * (y2 - y3))");;
//
// //*********
//
//    complex_qelim_all (parse
//        @"(2 * u2 * x2 + 2 * u3 * x1 - u3^2 - u2^2 = 0) /\ 
//      (2 * u1 * x2 - u1^2 = 0) /\ 
//      (-(x3^2) + 2 * x2 * x3 + 2 * u4 * x1 - u4^2 = 0) /\ 
//      (u3 * x5 + (-(u2) + u1) * x4 - u1 * u3 = 0) /\ 
//      ((u2 - u1) * x5 + u3 * x4 + (-(u2) + u1) * x3 - u3 * u4 = 0) /\ 
//      (u3 * x7 - u2 * x6 = 0) /\ 
//      (u2 * x7 + u3 * x6 - u2 * x3 - u3 * u4 = 0) /\ 
//      ~(4 * u1 * u3 = 0) /\ 
//      ~(2 * u1 = 0) /\ 
//      ~(-(u3^2) - u2^2 + 2 * u1 * u2 - u1^2 = 0) /\ 
//      ~(u3 = 0) /\ 
//      ~(-(u3^2) - u2^2 = 0) /\ 
//      ~(u2 = 0)
//      ==> (x4 * x7 + (-(x5) + x3) * x6 - x3 * x4 = 0)");;
//
//    time complex_qelim (parse
//        @"exists c.
//        (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\ 
//        (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\ 
//        (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))");;
//
//    time complex_qelim (parse
//        @"exists b c.
//        (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\ 
//        (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\ 
//        (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))");;
//
//    ********//
//
//    time complex_qelim (parse
//        @"forall y.
//             a * x^2 + b * x + c = 0 /\ 
//             a * y^2 + b * y + c = 0 /\ 
//             ~(x = y)
//             ==> a * x * y = c /\ a * (x + y) + b = 0");;
//
//    complex_qelim_all (parse
//        @"a * x^2 + b * x + c = 0 /\ 
//        a * y^2 + b * y + c = 0 /\ 
//        ~(x = y)
//        ==> a * x * y = c /\ a * (x + y) + b = 0");;
//
//  ------------------------------------------------------------------------- //
//  The Colmerauer example.                                                   //
//  ------------------------------------------------------------------------- //
//
// //******** This works, but is quite slow. And it's false! Presumably we
//               actually need to use ordering properties associated with absolute
//               values
//
//    let colmerauer = complex_qelim_all (parse
//        @"(x_1 + x_3  = (x_2) \/ x_1 + x_3  = -(x_2)) /\ 
//       (x_2 + x_4  = (x_3) \/ x_2 + x_4  = -(x_3)) /\ 
//       (x_3 + x_5  = (x_4) \/ x_3 + x_5  = -(x_4)) /\ 
//       (x_4 + x_6  = (x_5) \/ x_4 + x_6  = -(x_5)) /\ 
//       (x_5 + x_7  = (x_6) \/ x_5 + x_7  = -(x_6)) /\ 
//       (x_6 + x_8  = (x_7) \/ x_6 + x_8  = -(x_7)) /\ 
//       (x_7 + x_9  = (x_8) \/ x_7 + x_9  = -(x_8)) /\ 
//       (x_8 + x_10 = (x_9) \/ x_8 + x_10 = -(x_9)) /\ 
//       (x_9 + x_11 = (x_10) \/ x_9 + x_11 = -(x_10))
//       ==> x_1 = x_10 /\ x_2 = x_11");;
//
//     **********//
//
//  ------------------------------------------------------------------------- //
//  Checking resultants from Maple.                                        //
//  ------------------------------------------------------------------------- //
//
// //** interface(prettyprint=0);
//         resultant(a * x^2 + b * x + c, 2 * a * x + b,x);
//     **//
//
//    time complex_qelim (parse
//        @"forall a b c.
//       (exists x. a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0) \/ (a = 0) <=>
//       (4*a^2*c-b^2*a = 0)");;
//
//    time complex_qelim (parse
//        @"forall a b c d e.
//      (exists x. a * x^2 + b * x + c = 0 /\ d * x + e = 0) \/
//       a = 0 /\ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0");;
//
//    time complex_qelim (parse
//        @"forall a b c d e f.
//       (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
//       (a = 0) /\ (d = 0) <=>
//       d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0");;
//
// //*** No hope for this one I think
//
//    time complex_qelim (parse
//        @"forall a b c d e f g.
//      (exists x. a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0) \/
//      (a = 0) /\ (e = 0) <=>
//      e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
//      g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0");;
//
//     ***//
//
//  ------------------------------------------------------------------------- //
//  Some trigonometric addition formulas (checking stuff from Maple).         //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"forall x y. x^2 + y^2 = 1 ==> (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1");;
//
//  ------------------------------------------------------------------------- //
//  The examples from my thesis.                                              //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"forall s c. s^2 + c^2 = 1
//          ==> 2 * s - (2 * s * c * c - s^3) = 3 * s^3");;
//
//    time complex_qelim (parse
//        @"forall u v.
//      -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
//         (((7 * u^6) * v) * v - (u * u^7)) * 144 -
//         (((5 * u^4) * v) * v - (u * u^5)) * 168 -
//         (((3 * u^2) * v) * v - (u * u^3)) * 210 -
//         (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
//       (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
//       (u^2 + v^2 - 1)");;
//
//    time complex_qelim (parse
//        @"forall u v.
//            u^2 + v^2 = 1
//            ==> (((9 * u^8) * v) * v - (u * u^9)) * 128 +
//                (((7 * u^6) * v) * v - (u * u^7)) * 144 +
//                (((5 * u^4) * v) * v - (u * u^5)) * 168 +
//                (((3 * u^2) * v) * v - (u * u^3)) * 210 +
//                (v * v - (u * u)) * 315 + 1280 * u^10 = 315");;
//
//  ------------------------------------------------------------------------- //
//  Deliberately silly examples from Poizat's model theory book (6.6).        //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse @"exists z. x * z^87 + y * z^44 + 1 = 0");;
//
//    time complex_qelim (parse
//        @"forall u. exists v. x * (u + v^2)^2 + y * (u + v^2) + z = 0");;
//
//  ------------------------------------------------------------------------- //
//  Actually prove simple equivalences.                                       //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"forall x y. (exists z. x * z^87 + y * z^44 + 1 = 0)
//                      <=> ~(x = 0) \/ ~(y = 0)");;
//
//    time complex_qelim (parse
//        @"forall x y z. (forall u. exists v.
//                             x * (u + v^2)^2 + y * (u + v^2) + z = 0)
//                        <=> ~(x = 0) \/ ~(y = 0) \/ z = 0");;
//
//  ------------------------------------------------------------------------- //
//  Invertibility of 2x2 matrix in terms of nonzero determinant.              //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"exists w x y z. (a * w + b * y = 1) /\ 
//                          (a * x + b * z = 0) /\ 
//                          (c * w + d * y = 0) /\ 
//                          (c * x + d * z = 1)");;
//
//    time complex_qelim (parse
//        @"forall a b c d.
//            (exists w x y z. (a * w + b * y = 1) /\ 
//                             (a * x + b * z = 0) /\ 
//                             (c * w + d * y = 0) /\ 
//                             (c * x + d * z = 1))
//            <=> ~(a * d = b * c)");;
//
//  ------------------------------------------------------------------------- //
//  Inspired by Cardano's formula for a cubic. Not all complex cbrts work.    //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"forall m n x u t cu ct.
//       t - u = n /\ 27 * t * u = m^3 /\ 
//       ct^3 = t /\ cu^3 = u /\ 
//       x = ct - cu
//       ==> x^3 + m * x = n");;
//
//    time complex_qelim (parse
//        @"forall m n x u t.
//       t - u = n /\ 27 * t * u = m^3
//       ==> exists ct cu. ct^3 = t /\ cu^3 = u /\ 
//                         (x = ct - cu ==> x^3 + m * x = n)");;
//
//  ------------------------------------------------------------------------- //
//  SOS in rational functions for Motzkin polynomial (dehomogenized).         //
//  Of course these are just trivial normalization, nothing deep.             //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"forall x y z.
//        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//         x^2 * y^2 * (x^2 + y^2 + 1) * (x^2 + y^2 - 2)^2 + (x^2 - y^2)^2");;
//
//    time complex_qelim (parse
//        @"forall x y z.
//        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//        x^2 * y^2 * x^2  * (x^2 + y^2 - 2)^2 +
//        x^2 * y^2 * y^2 * (x^2 + y^2 - 2)^2 +
//        x^2 * y^2 * (x^2 + y^2 - 2)^2 +
//        (x^2 - y^2)^2");;
//
//    time complex_qelim (parse
//        @"forall x y z.
//        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//        x^4 * y^2 * (x^2 + y^2 - 2)^2 +
//        x^2 * y^4 * (x^2 + y^2 - 2)^2 +
//        x^2 * y^2 * (x^2 + y^2 - 2)^2 +
//        (x^2 - y^2)^2");;
//
//    time complex_qelim (parse
//        @"forall x y z.
//        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//        (x^2 * y * (x^2 + y^2 - 2))^2 +
//        (x * y^2 * (x^2 + y^2 - 2))^2 +
//        (x * y * (x^2 + y^2 - 2))^2 +
//        (x^2 - y^2)^2");;
//
//  ------------------------------------------------------------------------- //
//  A cute bilinear identity -- see ch14 of Rajwade's "Squares" for more.     //
//  ------------------------------------------------------------------------- //
//
//    polytest (parset
//        @"(x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_6^2 + x_7^2 + x_8^2 + x_9^2) *
//       (y_1^2 + y_2^2 + y_3^2 + y_4^2 + y_5^2 + y_6^2 + y_7^2 + y_8^2 +
//        y_9^2 + y_10^2 + y_11^2 + y_12^2 + y_13^2 + y_14^2 + y_15^2 + y_16^2) -
//       ((0 + x_1 * y_1 + x_2 * y_2 + x_3 * y_3 + x_4 * y_4 + x_5 * y_5 + x_6 * y_6 + x_7 * y_7 + x_8 * y_8 + x_9 * y_9)^2 +
//        (0 - x_2 * y_1 + x_1 * y_2 + x_4 * y_3 - x_3 * y_4 + x_6 * y_5 - x_5 * y_6 - x_8 * y_7 + x_7 * y_8 + x_9 * y_10)^2 +
//        (0 - x_3 * y_1 - x_4 * y_2 + x_1 * y_3 + x_2 * y_4 + x_7 * y_5 + x_8 * y_6 - x_5 * y_7 - x_6 * y_8 + x_9 * y_11)^2 +
//        (0 - x_4 * y_1 + x_3 * y_2 - x_2 * y_3 + x_1 * y_4 + x_8 * y_5 - x_7 * y_6 + x_6 * y_7 - x_5 * y_8 + x_9 * y_12)^2 +
//        (0 - x_5 * y_1 - x_6 * y_2 - x_7 * y_3 - x_8 * y_4 + x_1 * y_5 + x_2 * y_6 + x_3 * y_7 + x_4 * y_8 + x_9 * y_13)^2 +
//        (0 - x_6 * y_1 + x_5 * y_2 - x_8 * y_3 + x_7 * y_4 - x_2 * y_5 + x_1 * y_6 - x_4 * y_7 + x_3 * y_8 + x_9 * y_14)^2 +
//        (0 - x_7 * y_1 + x_8 * y_2 + x_5 * y_3 - x_6 * y_4 - x_3 * y_5 + x_4 * y_6 + x_1 * y_7 - x_2 * y_8 + x_9 * y_15)^2 +
//        (0 - x_8 * y_1 - x_7 * y_2 + x_6 * y_3 + x_5 * y_4 - x_4 * y_5 - x_3 * y_6 + x_2 * y_7 + x_1 * y_8 + x_9 * y_16)^2 +
//        (0 - x_9 * y_1 + x_1 * y_9 - x_2 * y_10 - x_3 * y_11 - x_4 * y_12 - x_5 * y_13 - x_6 * y_14 - x_7 * y_15 - x_8 * y_16)^2 +
//        (0 - x_9 * y_2 + x_2 * y_9 + x_1 * y_10 - x_4 * y_11 + x_3 * y_12 - x_6 * y_13 + x_5 * y_14 + x_8 * y_15 - x_7 * y_16)^2 +
//        (0 - x_9 * y_3 + x_3 * y_9 + x_4 * y_10 + x_1 * y_11 - x_2 * y_12 - x_7 * y_13 - x_8 * y_14 + x_5 * y_15 + x_6 * y_16)^2 +
//        (0 - x_9 * y_4 + x_4 * y_9 - x_3 * y_10 + x_2 * y_11 + x_1 * y_12 - x_8 * y_13 + x_7 * y_14 - x_6 * y_15 + x_5 * y_16)^2 +
//        (0 - x_9 * y_5 + x_5 * y_9 + x_6 * y_10 + x_7 * y_11 + x_8 * y_12 + x_1 * y_13 - x_2 * y_14 - x_3 * y_15 - x_4 * y_16)^2 +
//        (0 - x_9 * y_6 + x_6 * y_9 - x_5 * y_10 + x_8 * y_11 - x_7 * y_12 + x_2 * y_13 + x_1 * y_14 + x_4 * y_15 - x_3 * y_16)^2 +
//        (0 - x_9 * y_7 + x_7 * y_9 - x_8 * y_10 - x_5 * y_11 + x_6 * y_12 + x_3 * y_13 - x_4 * y_14 + x_1 * y_15 + x_2 * y_16)^2 +
//        (0 - x_9 * y_8 + x_8 * y_9 + x_7 * y_10 - x_6 * y_11 - x_5 * y_12 + x_4 * y_13 + x_3 * y_14 - x_2 * y_15 + x_1 * y_16)^2)");;
//
//  ------------------------------------------------------------------------- //
//  This is essentially the Cauchy-Riemann conditions for a differential.     //
//  ------------------------------------------------------------------------- //
//
//    time complex_qelim (parse
//        @"forall x y. (a * x + b * y = u * x - v * y) /\ 
//                    (c * x + d * y = u * y + v * x)
//                    ==> (a = d)");;
//
//    time complex_qelim (parse
//        @"forall a b c d.
//          (forall x y. (a * x + b * y = u * x - v * y) /\ 
//                       (c * x + d * y = u * y + v * x))
//                       ==> (a = d) /\ (b = -(c))");;
//
//    time complex_qelim (parse
//        @"forall a b c d.
//            (exists u v. forall x y. (a * x + b * y = u * x - v * y) /\ 
//                                     (c * x + d * y = u * y + v * x))
//            <=> (a = d) /\ (b = -(c))");;
//
//  ------------------------------------------------------------------------- //
//  Finding non-trivial perpendiculars to lines.                              //
//  ------------------------------------------------------------------------- //
//
//    complex_qelim (parse
//        @"forall x1 y1 x2 y2. exists a b.
//          ~(a = 0 /\ b = 0) /\ a * x1 + b * y1 = 0 /\ a * x2 + b * y2 = 0");;
//
