// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.complex
open FSharpx.Books.AutomatedReasoning.grobner

fsi.AddPrinter sprint_fol_formula

// pg. 413
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// grobner.p001
grobner_decide (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0");;

// grobner.p002
grobner_decide (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0");;

// grobner.p003
grobner_decide (parse @"
    (a * x^2 + b * x + c = 0) /\
    (a * y^2 + b * y + c = 0) /\
    ~(x = y)
    ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;

// ------------------------------------------------------------------------- //
// Compare with earlier procedure.                                           //
// ------------------------------------------------------------------------- //

let fm = (parse @"
    (a * x^2 + b * x + c = 0) /\
    (a * y^2 + b * y + c = 0) /\
    ~(x = y)
    ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;

// grobner.p004
time complex_qelim (generalize fm),time grobner_decide fm;;
        
// ------------------------------------------------------------------------- //
// More tests.                                                               //
// ------------------------------------------------------------------------- //

// grobner.p005
time grobner_decide  (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0");;

// grobner.p006
time grobner_decide  (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0");;

// grobner.p007
time grobner_decide (parse @"
    (a * x^2 + b * x + c = 0) /\
    (a * y^2 + b * y + c = 0) /\
    ~(x = y)
    ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;

// grobner.p008
time grobner_decide (parse @"
    (y_1 = 2 * y_3) /\
    (y_2 = 2 * y_4) /\
    (y_1 * y_3 = y_2 * y_4)
    ==> (y_1^2 = y_2^2)");;

// grobner.p009
time grobner_decide (parse @"
    (x1 = u3) /\
    (x1 * (u2 - u1) = x2 * u3) /\
    (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
    (x3 * u3 = x4 * u2) /\
    ~(u1 = 0) /\
    ~(u3 = 0)
    ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)");;

// grobner.p010
time grobner_decide (parse @"
    (u1 * x1 - u1 * u3 = 0) /\
    (u3 * x2 - (u2 - u1) * x1 = 0) /\
    (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
    (u3 * x4 - u2 * x3 = 0) /\
    ~(u1 = 0) /\
    ~(u3 = 0)
    ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)");;

//** Checking resultants (in one direction) **//

// grobner.p011
time grobner_decide (parse @"
    a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0 
    ==> 4*a^2*c-b^2*a = 0");;

// grobner.p012
time grobner_decide (parse @"
    a * x^2 + b * x + c = 0 /\ d * x + e = 0 
    ==> d^2*c-e*d*b+a*e^2 = 0");;

// grobner.p013
time grobner_decide (parse @"
    a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0
    ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0");;

// grobner.p014
//***** Seems a bit too lengthy?
// long running
time grobner_decide (parse @"
    a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0
    ==>
    e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
    g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0");;

// grobner.p015
//********* Works correctly, but it's lengthy
// long running
time grobner_decide (parse @"
    (x1 - x0)^2 + (y1 - y0)^2 =
    (x2 - x0)^2 + (y2 - y0)^2 /\
    (x2 - x0)^2 + (y2 - y0)^2 =
    (x3 - x0)^2 + (y3 - y0)^2 /\
    (x1 - x0')^2 + (y1 - y0')^2 =
    (x2 - x0')^2 + (y2 - y0')^2 /\
    (x2 - x0')^2 + (y2 - y0')^2 =
    (x3 - x0')^2 + (y3 - y0')^2
    ==> x0 = x0' /\ y0 = y0'");;

// grobner.p016
//**** Corrected with non-isotropy conditions; even lengthier
// long running
Initialization.runWithEnlargedStack (fun () -> 
    time grobner_decide (parse @"
        (x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2 /\
        ~((x1 - x0)^2 + (y1 - y0)^2 = 0) /\
        ~((x1 - x0')^2 + (y1 - y0')^2 = 0)
        ==> x0 = x0' /\ y0 = y0'"));;

// grobner.p017
//*** Maybe this is more efficient? (No?)
// long running
Initialization.runWithEnlargedStack (fun () -> 
    time grobner_decide (parse @"
        (x1 - x0)^2 + (y1 - y0)^2 = d /\
        (x2 - x0)^2 + (y2 - y0)^2 = d /\
        (x3 - x0)^2 + (y3 - y0)^2 = d /\
        (x1 - x0')^2 + (y1 - y0')^2 = e /\
        (x2 - x0')^2 + (y2 - y0')^2 = e /\
        (x3 - x0')^2 + (y3 - y0')^2 = e /\
        ~(d = 0) /\ ~(e = 0)
        ==> x0 = x0' /\ y0 = y0'"));;

// ------------------------------------------------------------------------- //
// Inversion of homographic function (from Gosper's CF notes).               //
// ------------------------------------------------------------------------- //

// grobner.p018
time grobner_decide (parse @"y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y");;

// ------------------------------------------------------------------------- //
// Manual "sums of squares" for 0 <= a /\ a <= b ==> a^3 <= b^3.             //
// ------------------------------------------------------------------------- //

// grobner.p019
time complex_qelim (parse @"
    forall a b c d e.
        a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
        ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
            0");;

// grobner.p020
time grobner_decide (parse @"
    a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
    ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
        0");;

// ------------------------------------------------------------------------- //
// Special case of a = 1, i.e. 1 <= b ==> 1 <= b^3                           //
// ------------------------------------------------------------------------- //

// grobner.p021
time complex_qelim (parse @"
    forall b d e.
        b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
        ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0");;

// grobner.p022
time grobner_decide (parse @"
    b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
    ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0");;

// ------------------------------------------------------------------------- //
// Converse, 0 <= a /\ a^3 <= b^3 ==> a <= b                                 //
//                                                                           //
// This derives b <= 0, but not a full solution.                             //
// ------------------------------------------------------------------------- //

// grobner.p023
time grobner_decide (parse @"
    a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
    ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0");;

// ------------------------------------------------------------------------- //
// Here are further steps towards a solution, step-by-step.                  //
// ------------------------------------------------------------------------- //

// grobner.p024
time grobner_decide (parse @"
    a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
    ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)");;

// grobner.p025
time grobner_decide (parse @"
    a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
    ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3");;

// grobner.p026
time grobner_decide (parse @"
    a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
    ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0");;

// ------------------------------------------------------------------------- //
// A simpler one is ~(x < y /\ y < x), i.e. x < y ==> x <= y.                //
//                                                                           //
// Yet even this isn't completed!                                            //
// ------------------------------------------------------------------------- //

// grobner.p027
time grobner_decide (parse @"(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0");;

// ------------------------------------------------------------------------- //
// Inspired by Cardano's formula for a cubic. This actually works worse than //
// with naive quantifier elimination (of course it's false...)               //
// ------------------------------------------------------------------------- //

// grobner.p028
// Real: 00:00:25.638, CPU: 00:00:25.546, GC gen0: 210, gen1: 2, gen2: 0
time grobner_decide (parse @"
    t - u = n /\ 27 * t * u = m^3 /\
    ct^3 = t /\ cu^3 = u /\
    x = ct - cu
    ==> x^3 + m * x = n");;
