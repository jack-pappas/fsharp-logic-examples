// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.grobner

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.complex
open FSharpx.Books.AutomatedReasoning.grobner
open NUnit.Framework
open FsUnit


(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

// grobner.p001
[<TestCase(@"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0", Result = true)>]

// grobner.p002
[<TestCase(@"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0", Result = false)>]

// grobner.p003
[<TestCase(@"(a * x^2 + b * x + c = 0) /\
   (a * y^2 + b * y + c = 0) /\
   ~(x = y)
   ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", Result = true)>]

let ``examples 1`` f =
    parse f
    |> grobner_decide

(* ------------------------------------------------------------------------- *)
(* Compare with earlier procedure.                                           *)
(* ------------------------------------------------------------------------- *)

// grobner.p004
let ``examples 2``() =
    let fm =
        @"(a * x^2 + b * x + c = 0) /\
        (a * y^2 + b * y + c = 0) /\
        ~(x = y)
        ==> (a * x * y = c) /\ (a * (x + y) + b = 0)"
        |> parse

    complex_qelim (generalize fm)
    |> should equal formula<fol>.True

    grobner_decide
    |> should be True

(* ------------------------------------------------------------------------- *)
(* More tests.                                                               *)
(* ------------------------------------------------------------------------- *)

// grobner.p005
[<TestCase(@"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0", Result = true)>]

// grobner.p006
[<TestCase(@"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0", Result = false)>]

// grobner.p007
[<TestCase(@"(a * x^2 + b * x + c = 0) /\
      (a * y^2 + b * y + c = 0) /\
      ~(x = y)
      ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", Result = true)>]

// grobner.p008
[<TestCase(@"(y_1 = 2 * y_3) /\
  (y_2 = 2 * y_4) /\
  (y_1 * y_3 = y_2 * y_4)
  ==> (y_1^2 = y_2^2)", Result = true)>]

// grobner.p009
[<TestCase(@"(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)", Result = true)>]

// grobner.p010
[<TestCase(@"(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)", Result = true)>]

// Checking resultants (in one direction) //
// grobner.p011
[<TestCase(@"a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0
 ==> 4*a^2*c-b^2*a = 0", Result = true)>]

// grobner.p012
[<TestCase(@"a * x^2 + b * x + c = 0 /\ d * x + e = 0
 ==> d^2*c-e*d*b+a*e^2 = 0", Result = true)>]

// grobner.p013
[<TestCase(@"a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0
 ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0", Result = true)>]

let ``examples 3`` f =
    parse f
    |> grobner_decide

(* ------------------------------------------------------------------------- *)
(* Inversion of homographic function (from Gosper's CF notes).               *)
(* ------------------------------------------------------------------------- *)

// grobner.p018
[<Test>]
let ``examples 4``() =
    @"y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y"
    |> parse
    |> grobner_decide
    |> should be True

(* ------------------------------------------------------------------------- *)
(* Manual "sums of squares" for 0 <= a /\ a <= b ==> a^3 <= b^3.             *)
(* ------------------------------------------------------------------------- *)

// grobner.p019
[<Test>]
let ``examples 5``() =
    @"forall a b c d e.
     a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
     ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 = 0"
    |> parse
    |> complex_qelim
    |> should equal formula<fol>.True

// grobner.p020
[<Test>]
let ``examples 6``() =
    @"a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
    ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 = 0"
    |> parse
    |> grobner_decide
    |> should be True

(* ------------------------------------------------------------------------- *)
(* Special case of a = 1, i.e. 1 <= b ==> 1 <= b^3                           *)
(* ------------------------------------------------------------------------- *)

// grobner.p021
[<Test>]
let ``examples 7``() =
    @"forall b d e.
     b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
     ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0"
    |> parse
    |> complex_qelim
    |> should equal formula<fol>.True

// grobner.p022
[<Test>]
let ``examples 8``() =
    @"b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
    ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0"
    |> parse
    |> grobner_decide
    |> should be True

(* ------------------------------------------------------------------------- *)
(* Converse, 0 <= a /\ a^3 <= b^3 ==> a <= b                                 *)
(*                                                                           *)
(* This derives b <= 0, but not a full solution.                             *)
(* ------------------------------------------------------------------------- *)

// grobner.p023
[<Test>]
let ``examples 9``() =
    @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
    ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0"
    |> parse
    |> grobner_decide
    |> should be True

(* ------------------------------------------------------------------------- *)
(* Here are further steps towards a solution, step-by-step.                  *)
(* ------------------------------------------------------------------------- *)

// grobner.p024
[<TestCase(@"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)", Result = true)>]

// grobner.p025
[<TestCase(@"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3", Result = true)>]

// grobner.p026
[<TestCase(@"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0", Result = true)>]

let ``examples 10`` f =
    parse f
    |> grobner_decide

(* ------------------------------------------------------------------------- *)
(* A simpler one is ~(x < y /\ y < x), i.e. x < y ==> x <= y.                *)
(*                                                                           *)
(* Yet even this isn't completed!                                            *)
(* ------------------------------------------------------------------------- *)

// grobner.p027
[<Test>]
let ``examples 11``() =
    @"(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0"
    |> parse
    |> grobner_decide
    |> should be True
