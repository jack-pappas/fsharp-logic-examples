// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.complex

open NUnit.Framework
open FsUnit
open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.cooper
open Reasoning.Automated.Harrison.Handbook.complex

(* ------------------------------------------------------------------------- *)
(* Sanity check.                                                             *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``sanity check``() =
    parse @"((w + x)^4 + (w + y)^4 + (w + z)^4 +
             (x + y)^4 + (x + z)^4 + (y + z)^4 +
             (w - x)^4 + (w - y)^4 + (w - z)^4 +
             (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
            (w^2 + x^2 + y^2 + z^2)^2"
    |> polyatom ["w"; "x"; "y"; "z"]
    |> should equal
    <| Atom (R ("=", [Fn ("0", []); Fn ("0", [])]))


(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let private example_results_1 : formula<fol>[] = [|
    True;
    Atom
     (R ("=",
       [Fn ("+",
         [Fn ("1", []);
          Fn ("*",
           [Var "c";
            Fn ("+",
             [Fn ("-4", []);
              Fn ("*",
               [Var "c";
                Fn ("+",
                 [Fn ("6", []);
                  Fn ("*",
                   [Var "c";
                    Fn ("+",
                     [Fn ("-4", []); Fn ("*", [Var "c"; Fn ("1", [])])])])])])])])]);
        Fn ("0", [])]));
    True;
    True;
    |]

[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0", 0)>]
[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0", 1)>]
[<TestCase(@"forall c. (forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0) <=> c = 1", 2)>]
[<TestCase(@"forall a b c x y.
              a * x^2 + b * x + c = 0 /\ a * y^2 + b * y + c = 0 /\ ~(x = y)
              ==> a * x * y = c /\ a * (x + y) + b = 0", 3)>]
let ``examples 1`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_1.[idx]


(* ------------------------------------------------------------------------- *)
(* More tests, not in the main text.                                         *)
(* ------------------------------------------------------------------------- *)

// Helper function
let private polytest tm =
    polynate (fvt tm) tm


[<Test>]
let ``lagrange_4``() =
    parset @"(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
     ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
    ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2) +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2) +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2) +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))"
    |> polytest
    |> should equal
    <| Fn ("0", [])

[<Test>]
let ``lagrange_8``() =
    parset @"((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
     (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
     ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
      (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
      (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
      (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
      (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
      (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
      (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
      (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)"
    |> polytest
    |> should equal
    <| Fn ("0", [])

[<Test>]
let ``liouville``() =
    parset @"6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
      (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
     ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
      (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))"
    |> polytest
    |> should equal
    <| Fn ("0", [])

[<Test>]
let ``fleck``() =
    parset @"60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
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
     36 * (x1^6 + x2^6 + x3^6 + x4^6))"
    |> polytest
    |> should equal
    <| Fn ("0", [])

[<Test>]
let ``hurwitz``() =
    parset @"5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
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
     6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))"
    |> polytest
    |> should equal
    <| Fn ("0", [])

[<Test>]
let ``schur``() =
    parset @"22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
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
          (x1 - x2 - x3 - x4)^10))"
    |> polytest
    |> should equal
    <| Fn ("0", [])

let private example_results_2 : formula<fol>[] = [|
    True;
    True;
    True;
    False;
    True;
    True;
    False;
    True;
    And
     (Or
       (Not
         (Atom
           (R ("=",
             [Fn ("+",
               [Fn ("9", []);
                Fn ("*",
                 [Var "a";
                  Fn ("+",
                   [Fn ("0", []);
                    Fn ("*",
                     [Var "a";
                      Fn ("+",
                       [Fn ("-10", []);
                        Fn ("*",
                         [Var "a";
                          Fn ("+",
                           [Fn ("0", []);
                            Fn ("*",
                             [Var "a";
                              Fn ("+",
                               [Fn ("5", []);
                                Fn ("*",
                                 [Var "a";
                                  Fn ("+",
                                   [Fn ("0", []);
                                    Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])]);
              Fn ("0", [])]))),
       Not
        (Atom
          (R ("=",
            [Fn ("+",
              [Fn ("0", []);
               Fn ("*",
                [Var "a";
                 Fn ("+",
                  [Fn ("12", []);
                   Fn ("*",
                    [Var "a";
                     Fn ("+",
                      [Fn ("0", []);
                       Fn ("*",
                        [Var "a";
                         Fn ("+",
                          [Fn ("-14", []);
                           Fn ("*",
                            [Var "a";
                             Fn ("+",
                              [Fn ("0", []);
                               Fn ("*",
                                [Var "a";
                                 Fn ("+",
                                  [Fn ("6", []);
                                   Fn ("*",
                                    [Var "a";
                                     Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])])])]);
             Fn ("0", [])])))),
     Atom
      (R ("=",
        [Fn ("+",
          [Fn ("-2", []);
           Fn ("*",
            [Var "a";
             Fn ("+", [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])])])]);
         Fn ("0", [])])));
    Not
     (Or
       (Not
         (Atom
           (R ("=",
             [Fn ("+",
               [Fn ("9", []);
                Fn ("*",
                 [Var "a";
                  Fn ("+",
                   [Fn ("0", []);
                    Fn ("*",
                     [Var "a";
                      Fn ("+",
                       [Fn ("-10", []);
                        Fn ("*",
                         [Var "a";
                          Fn ("+",
                           [Fn ("0", []);
                            Fn ("*",
                             [Var "a";
                              Fn ("+",
                               [Fn ("5", []);
                                Fn ("*",
                                 [Var "a";
                                  Fn ("+",
                                   [Fn ("0", []);
                                    Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])]);
              Fn ("0", [])]))),
       Not
        (Atom
          (R ("=",
            [Fn ("+",
              [Fn ("0", []);
               Fn ("*",
                [Var "a";
                 Fn ("+",
                  [Fn ("12", []);
                   Fn ("*",
                    [Var "a";
                     Fn ("+",
                      [Fn ("0", []);
                       Fn ("*",
                        [Var "a";
                         Fn ("+",
                          [Fn ("-14", []);
                           Fn ("*",
                            [Var "a";
                             Fn ("+",
                              [Fn ("0", []);
                               Fn ("*",
                                [Var "a";
                                 Fn ("+",
                                  [Fn ("6", []);
                                   Fn ("*",
                                    [Var "a";
                                     Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])])])]);
             Fn ("0", [])])))));
    Not
     (And
       (Or
         (And
           (Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
                Fn ("0", [])])),
           Atom
            (R ("=",
              [Fn ("+",
                [Fn ("1", []);
                 Fn ("*",
                  [Var "x";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
               Fn ("0", [])]))),
         And
          (Not
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
                 Fn ("0", [])]))),
          Atom
           (R ("=",
             [Fn ("+",
               [Fn ("1", []);
                Fn ("*",
                 [Var "x";
                  Fn ("+",
                   [Fn ("0", []);
                    Fn ("*",
                     [Var "x";
                      Fn ("+",
                       [Fn ("0", []);
                        Fn ("*",
                         [Var "x";
                          Fn ("+",
                           [Fn ("0", []);
                            Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])]);
              Fn ("0", [])])))),
       Not
        (Atom
          (R ("=",
            [Fn ("+",
              [Fn ("2", []);
               Fn ("*",
                [Var "x";
                 Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "x";
                     Fn ("+",
                      [Fn ("0", []);
                       Fn ("*",
                        [Var "x";
                         Fn ("+",
                          [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])]);
             Fn ("0", [])])))));
    False;
    False;
    True;
    True;
    True;
    True;
    True;
    True;
    True;
    True;
    True;
    True;
    True;
    True;
    True;
    |]

[<TestCase(@"exists x. x + 2 = 3", 0)>]
[<TestCase(@"exists x. x^2 + a = 3", 1)>]
[<TestCase(@"exists x. x^2 + x + 1 = 0", 2)>]
[<TestCase(@"exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0", 3)>]
[<TestCase(@"exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0", 4)>]
[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0", 5)>]
[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 6)>]
[<TestCase(@"exists a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)", 7)>]
[<TestCase(@"exists x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)", 8)>]
[<TestCase(@"forall x. x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 9)>]
[<TestCase(@"forall a. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 10)>]
[<TestCase(@"exists a b c x y.
                a * x^2 + b * x + c = 0 /\
                a * y^2 + b * y + c = 0 /\
                ~(x = y) /\
                ~(a * x * y = c)", 11)>]
[<TestCase(@"forall a b c x.
            (forall z. a * z^2 + b * z + c = 0 <=> z = x)
            ==> a * x * x = c /\ a * (x + x) + b = 0", 12)>]
[<TestCase(@"forall x y.
            (forall a b c. (a * x^2 + b * x + c = 0) /\
                   (a * y^2 + b * y + c = 0)
                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
                    <=> ~(x = y)", 13)>]
[<TestCase(@"forall y_1 y_2 y_3 y_4.
             (y_1 = 2 * y_3) /\
             (y_2 = 2 * y_4) /\
             (y_1 * y_3 = y_2 * y_4)
             ==> (y_1^2 = y_2^2)", 14)>]
[<TestCase(@"forall x y. x^2 = 2 /\ y^2 = 3
                ==> (x * y)^2 = 6", 15)>]
[<TestCase(@"forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
                ==> (x^4 + 1 = 0)", 16)>]
[<TestCase(@"forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
                ==> (x^4 + 1 = 0)", 17)>]
[<TestCase(@"~(exists a x y. (a^2 = 2) /\
             (x^2 + a * x + 1 = 0) /\
             (y * (x^4 + 1) + 1 = 0))", 18)>]
[<TestCase(@"forall x. exists y. x^2 = y^3", 19)>]
[<TestCase(@"forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
               2 * (b * x + b * z - a * y)", 20)>]
[<TestCase(@"forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)", 21)>]
[<TestCase(@"forall a b c x y. (a * x^2 + b * x + c = 0) /\
               (a * y^2 + b * y + c = 0) /\
               ~(x = y)
               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", 22)>]
[<TestCase(@"~(forall a b c x y. (a * x^2 + b * x + c = 0) /\
                 (a * y^2 + b * y + c = 0)
                 ==> (a * x * y = c) /\ (a * (x + y) + b = 0))", 23)>]
[<TestCase(@"forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)", 24)>]
[<TestCase(@"forall a1 b1 c1 a2 b2 c2.
            ~(a1 * b2 = a2 * b1)
            ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)", 25)>]
let ``examples 2`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_2.[idx]


(* ------------------------------------------------------------------------- *)
(* This seems harder, so see how many quantifiers are feasible.              *)
(* ------------------------------------------------------------------------- *)

let private example_results_3 : formula<fol>[] = [|
    Imp
     (And
       (Atom
         (R ("=",
           [Fn ("+",
             [Fn ("+",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                Fn ("*",
                 [Var "b";
                  Fn ("+",
                   [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
              Fn ("*",
               [Var "a";
                Fn ("+",
                 [Fn ("0", []);
                  Fn ("*",
                   [Var "x";
                    Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])]);
            Fn ("0", [])])),
       And
        (Atom
          (R ("=",
            [Fn ("+",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                 Fn ("*",
                  [Var "b";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])]);
               Fn ("*",
                [Var "a";
                 Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "y";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])])])]);
             Fn ("0", [])])),
        Not
         (Or
           (And
             (Atom
               (R ("=",
                 [Fn ("+",
                   [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                  Fn ("0", [])])),
             Or
              (And
                (Atom
                  (R ("=",
                    [Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                     Fn ("0", [])])),
                Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                    Fn ("0", [])]))),
              And
               (Not
                 (Atom
                   (R ("=",
                     [Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                      Fn ("0", [])]))),
               Not
                (Atom
                  (R ("=",
                    [Fn ("+",
                      [Fn ("+",
                        [Fn ("0", []);
                         Fn ("*",
                          [Var "c";
                           Fn ("+",
                            [Fn ("0", []);
                             Fn ("*", [Var "c"; Fn ("1", [])])])])]);
                       Fn ("*",
                        [Var "b";
                         Fn ("+",
                          [Fn ("+",
                            [Fn ("0", []);
                             Fn ("*",
                              [Var "c";
                               Fn ("+",
                                [Fn ("+",
                                  [Fn ("0", []);
                                   Fn ("*", [Var "y"; Fn ("1", [])])]);
                                 Fn ("*", [Var "x"; Fn ("1", [])])])])]);
                           Fn ("*",
                            [Var "b";
                             Fn ("+",
                              [Fn ("0", []);
                               Fn ("*",
                                [Var "x";
                                 Fn ("+",
                                  [Fn ("0", []);
                                   Fn ("*", [Var "y"; Fn ("1", [])])])])])])])])]);
                     Fn ("0", [])])))))),
           And
            (Not
              (Atom
                (R ("=",
                  [Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                   Fn ("0", [])]))),
            Or
             (Not
               (Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("+",
                       [Fn ("0", []);
                        Fn ("*",
                         [Var "b";
                          Fn ("+",
                           [Fn ("0", []);
                            Fn ("*",
                             [Var "b";
                              Fn ("+",
                               [Fn ("0", []);
                                Fn ("*", [Var "c"; Fn ("-1", [])])])])])])]);
                      Fn ("*",
                       [Var "a";
                        Fn ("+",
                         [Fn ("+",
                           [Fn ("+",
                             [Fn ("0", []);
                              Fn ("*",
                               [Var "c";
                                Fn ("+",
                                 [Fn ("0", []);
                                  Fn ("*", [Var "c"; Fn ("1", [])])])])]);
                            Fn ("*",
                             [Var "b";
                              Fn ("+",
                               [Fn ("0", []);
                                Fn ("*",
                                 [Var "c";
                                  Fn ("+",
                                   [Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*", [Var "y"; Fn ("-2", [])])]);
                                    Fn ("*", [Var "x"; Fn ("-2", [])])])])])])]);
                          Fn ("*",
                           [Var "a";
                            Fn ("+",
                             [Fn ("+",
                               [Fn ("0", []);
                                Fn ("*",
                                 [Var "c";
                                  Fn ("+",
                                   [Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*",
                                       [Var "y";
                                        Fn ("+",
                                         [Fn ("0", []);
                                          Fn ("*",
                                           [Var "y"; Fn ("-1", [])])])])]);
                                    Fn ("*",
                                     [Var "x";
                                      Fn ("+",
                                       [Fn ("+",
                                         [Fn ("0", []);
                                          Fn ("*",
                                           [Var "y"; Fn ("-4", [])])]);
                                        Fn ("*", [Var "x"; Fn ("-1", [])])])])])])]);
                              Fn ("*",
                               [Var "a";
                                Fn ("+",
                                 [Fn ("0", []);
                                  Fn ("*",
                                   [Var "x";
                                    Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*",
                                       [Var "x";
                                        Fn ("+",
                                         [Fn ("0", []);
                                          Fn ("*",
                                           [Var "y";
                                            Fn ("+",
                                             [Fn ("0", []);
                                              Fn ("*",
                                               [Var "y"; Fn ("1", [])])])])])])])])])])])])])])]);
                    Fn ("0", [])]))),
             Not
              (Atom
                (R ("=",
                  [Fn ("+",
                    [Fn ("+",
                      [Fn ("0", []);
                       Fn ("*",
                        [Var "b";
                         Fn ("+",
                          [Fn ("0", []);
                           Fn ("*",
                            [Var "b";
                             Fn ("+",
                              [Fn ("0", []);
                               Fn ("*", [Var "b"; Fn ("-1", [])])])])])])]);
                     Fn ("*",
                      [Var "a";
                       Fn ("+",
                        [Fn ("+",
                          [Fn ("0", []);
                           Fn ("*",
                            [Var "b";
                             Fn ("+",
                              [Fn ("+",
                                [Fn ("0", []);
                                 Fn ("*", [Var "c"; Fn ("2", [])])]);
                               Fn ("*",
                                [Var "b";
                                 Fn ("+",
                                  [Fn ("+",
                                    [Fn ("0", []);
                                     Fn ("*", [Var "y"; Fn ("-2", [])])]);
                                   Fn ("*", [Var "x"; Fn ("-2", [])])])])])])]);
                         Fn ("*",
                          [Var "a";
                           Fn ("+",
                            [Fn ("+",
                              [Fn ("+",
                                [Fn ("0", []);
                                 Fn ("*",
                                  [Var "c";
                                   Fn ("+",
                                    [Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*", [Var "y"; Fn ("2", [])])]);
                                     Fn ("*", [Var "x"; Fn ("2", [])])])])]);
                               Fn ("*",
                                [Var "b";
                                 Fn ("+",
                                  [Fn ("+",
                                    [Fn ("0", []);
                                     Fn ("*",
                                      [Var "y";
                                       Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*", [Var "y"; Fn ("-1", [])])])])]);
                                   Fn ("*",
                                    [Var "x";
                                     Fn ("+",
                                      [Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*", [Var "y"; Fn ("-4", [])])]);
                                       Fn ("*", [Var "x"; Fn ("-1", [])])])])])])]);
                             Fn ("*",
                              [Var "a";
                               Fn ("+",
                                [Fn ("0", []);
                                 Fn ("*",
                                  [Var "x";
                                   Fn ("+",
                                    [Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*",
                                        [Var "y";
                                         Fn ("+",
                                          [Fn ("0", []);
                                           Fn ("*",
                                            [Var "y"; Fn ("-2", [])])])])]);
                                     Fn ("*",
                                      [Var "x";
                                       Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*", [Var "y"; Fn ("-2", [])])])])])])])])])])])])]);
                   Fn ("0", [])]))))))))),
     And
      (Atom
        (R ("=",
          [Fn ("+",
            [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("-1", [])])]);
             Fn ("*",
              [Var "a";
               Fn ("+",
                [Fn ("0", []);
                 Fn ("*",
                  [Var "x";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])])])]);
           Fn ("0", [])])),
      Atom
       (R ("=",
         [Fn ("+",
           [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
            Fn ("*",
             [Var "a";
              Fn ("+",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
                Fn ("*", [Var "x"; Fn ("1", [])])])])]);
          Fn ("0", [])]))));
    True;   // CPU time (user): 0.100007
    True;   // CPU time (user): 0.240015
    True;   // CPU time (user): 9.888617
    Not     // CPU time (user): 0.004
     (And
       (And
         (Atom
           (R ("=",
             [Fn ("+",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
                Fn ("*", [Var "x"; Fn ("-1", [])])]);
              Fn ("0", [])])),
         Or
          (Atom
            (R ("=",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "y";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])]);
                 Fn ("*",
                  [Var "x";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-1", [])])])])]);
               Fn ("0", [])])),
          Not
           (Atom
             (R ("=",
               [Fn ("+",
                 [Fn ("+",
                   [Fn ("0", []);
                    Fn ("*",
                     [Var "y";
                      Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])]);
                  Fn ("*",
                   [Var "x";
                    Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-1", [])])])])]);
                Fn ("0", [])]))))),
       Not
        (Atom
          (R ("=",
            [Fn ("+",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("-1", [])])]);
               Fn ("*", [Var "x"; Fn ("1", [])])]);
             Fn ("0", [])])))));
    Not     // CPU time (user): 0.008001
     (And
       (And
         (Atom
           (R ("=",
             [Fn ("+",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("2", [])])]);
                Fn ("*", [Var "x"; Fn ("-2", [])])]);
              Fn ("0", [])])),
         Or
          (Atom
            (R ("=",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "y";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "y"; Fn ("2", [])])])])]);
                 Fn ("*",
                  [Var "x";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-2", [])])])])]);
               Fn ("0", [])])),
          Not
           (Atom
             (R ("=",
               [Fn ("+",
                 [Fn ("+",
                   [Fn ("0", []);
                    Fn ("*",
                     [Var "y";
                      Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "y"; Fn ("2", [])])])])]);
                  Fn ("*",
                   [Var "x";
                    Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-2", [])])])])]);
                Fn ("0", [])]))))),
       Not
        (Atom
          (R ("=",
            [Fn ("+",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("-1", [])])]);
               Fn ("*", [Var "x"; Fn ("1", [])])]);
             Fn ("0", [])])))));
    True;   // CPU time (user): 0.008
    Not     // CPU time (user): 0.032002
     (Or
       (And
         (Or
           (And
             (Atom
               (R ("=",
                 [Fn ("+",
                   [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                  Fn ("0", [])])),
             Or
              (And
                (Atom
                  (R ("=",
                    [Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                     Fn ("0", [])])),
                And
                 (Atom
                   (R ("=",
                     [Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                      Fn ("0", [])])),
                 Not
                  (Atom
                    (R ("=",
                      [Fn ("+",
                        [Fn ("0", []);
                         Fn ("*",
                          [Var "a";
                           Fn ("+",
                            [Fn ("0", []);
                             Fn ("*", [Var "x"; Fn ("1", [])])])])]);
                       Fn ("0", [])]))))),
              And
               (Not
                 (Atom
                   (R ("=",
                     [Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                      Fn ("0", [])]))),
               Not
                (Atom
                  (R ("=",
                    [Fn ("+",
                      [Fn ("+",
                        [Fn ("0", []);
                         Fn ("*",
                          [Var "b";
                           Fn ("+",
                            [Fn ("+",
                              [Fn ("0", []);
                               Fn ("*",
                                [Var "c";
                                 Fn ("+",
                                  [Fn ("0", []);
                                   Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
                             Fn ("*",
                              [Var "b";
                               Fn ("+",
                                [Fn ("0", []);
                                 Fn ("*",
                                  [Var "c";
                                   Fn ("+",
                                    [Fn ("0", []);
                                     Fn ("*", [Var "x"; Fn ("-1", [])])])])])])])])]);
                       Fn ("*",
                        [Var "a";
                         Fn ("+",
                          [Fn ("+",
                            [Fn ("0", []);
                             Fn ("*",
                              [Var "c";
                               Fn ("+",
                                [Fn ("0", []);
                                 Fn ("*",
                                  [Var "c";
                                   Fn ("+",
                                    [Fn ("0", []);
                                     Fn ("*", [Var "x"; Fn ("-1", [])])])])])])]);
                           Fn ("*",
                            [Var "b";
                             Fn ("+",
                              [Fn ("0", []);
                               Fn ("*",
                                [Var "c";
                                 Fn ("+",
                                  [Fn ("0", []);
                                   Fn ("*",
                                    [Var "x";
                                     Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*", [Var "x"; Fn ("-1", [])])])])])])])])])])]);
                     Fn ("0", [])])))))),
           And
            (Not
              (Atom
                (R ("=",
                  [Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                   Fn ("0", [])]))),
            Or
             (Not
               (Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("0", []);
                      Fn ("*",
                       [Var "a";
                        Fn ("+",
                         [Fn ("0", []);
                          Fn ("*",
                           [Var "a";
                            Fn ("+",
                             [Fn ("+",
                               [Fn ("+",
                                 [Fn ("0", []);
                                  Fn ("*",
                                   [Var "c";
                                    Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*",
                                       [Var "c";
                                        Fn ("+",
                                         [Fn ("0", []);
                                          Fn ("*",
                                           [Var "c"; Fn ("-1", [])])])])])])]);
                                Fn ("*",
                                 [Var "b";
                                  Fn ("+",
                                   [Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*",
                                       [Var "c";
                                        Fn ("+",
                                         [Fn ("0", []);
                                          Fn ("*",
                                           [Var "c";
                                            Fn ("+",
                                             [Fn ("0", []);
                                              Fn ("*",
                                               [Var "x"; Fn ("-2", [])])])])])])]);
                                    Fn ("*",
                                     [Var "b";
                                      Fn ("+",
                                       [Fn ("0", []);
                                        Fn ("*",
                                         [Var "c";
                                          Fn ("+",
                                           [Fn ("0", []);
                                            Fn ("*",
                                             [Var "x";
                                              Fn ("+",
                                               [Fn ("0", []);
                                                Fn ("*",
                                                 [Var "x"; Fn ("-1", [])])])])])])])])])])]);
                              Fn ("*",
                               [Var "a";
                                Fn ("+",
                                 [Fn ("+",
                                   [Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*",
                                       [Var "c";
                                        Fn ("+",
                                         [Fn ("0", []);
                                          Fn ("*",
                                           [Var "c";
                                            Fn ("+",
                                             [Fn ("0", []);
                                              Fn ("*",
                                               [Var "x";
                                                Fn ("+",
                                                 [Fn ("0", []);
                                                  Fn ("*",
                                                   [Var "x"; Fn ("-2", [])])])])])])])])]);
                                    Fn ("*",
                                     [Var "b";
                                      Fn ("+",
                                       [Fn ("0", []);
                                        Fn ("*",
                                         [Var "c";
                                          Fn ("+",
                                           [Fn ("0", []);
                                            Fn ("*",
                                             [Var "x";
                                              Fn ("+",
                                               [Fn ("0", []);
                                                Fn ("*",
                                                 [Var "x";
                                                  Fn ("+",
                                                   [Fn ("0", []);
                                                    Fn ("*",
                                                     [Var "x";
                                                      Fn ("-2", [])])])])])])])])])])]);
                                  Fn ("*",
                                   [Var "a";
                                    Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*",
                                       [Var "c";
                                        Fn ("+",
                                         [Fn ("0", []);
                                          Fn ("*",
                                           [Var "x";
                                            Fn ("+",
                                             [Fn ("0", []);
                                              Fn ("*",
                                               [Var "x";
                                                Fn ("+",
                                                 [Fn ("0", []);
                                                  Fn ("*",
                                                   [Var "x";
                                                    Fn ("+",
                                                     [Fn ("0", []);
                                                      Fn ("*",
                                                       [Var "x";
                                                        Fn ("-1", [])])])])])])])])])])])])])])])])])])]);
                    Fn ("0", [])]))),
             Not
              (Atom
                (R ("=",
                  [Fn ("+",
                    [Fn ("0", []);
                     Fn ("*",
                      [Var "a";
                       Fn ("+",
                        [Fn ("0", []);
                         Fn ("*",
                          [Var "a";
                           Fn ("+",
                            [Fn ("+",
                              [Fn ("0", []);
                               Fn ("*",
                                [Var "b";
                                 Fn ("+",
                                  [Fn ("+",
                                    [Fn ("0", []);
                                     Fn ("*",
                                      [Var "c";
                                       Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
                                   Fn ("*",
                                    [Var "b";
                                     Fn ("+",
                                      [Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*",
                                          [Var "c";
                                           Fn ("+",
                                            [Fn ("0", []);
                                             Fn ("*",
                                              [Var "x"; Fn ("-2", [])])])])]);
                                       Fn ("*",
                                        [Var "b";
                                         Fn ("+",
                                          [Fn ("0", []);
                                           Fn ("*",
                                            [Var "x";
                                             Fn ("+",
                                              [Fn ("0", []);
                                               Fn ("*",
                                                [Var "x"; Fn ("-1", [])])])])])])])])])])]);
                             Fn ("*",
                              [Var "a";
                               Fn ("+",
                                [Fn ("+",
                                  [Fn ("0", []);
                                   Fn ("*",
                                    [Var "b";
                                     Fn ("+",
                                      [Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*",
                                          [Var "c";
                                           Fn ("+",
                                            [Fn ("0", []);
                                             Fn ("*",
                                              [Var "x";
                                               Fn ("+",
                                                [Fn ("0", []);
                                                 Fn ("*",
                                                  [Var "x"; Fn ("-2", [])])])])])])]);
                                       Fn ("*",
                                        [Var "b";
                                         Fn ("+",
                                          [Fn ("0", []);
                                           Fn ("*",
                                            [Var "x";
                                             Fn ("+",
                                              [Fn ("0", []);
                                               Fn ("*",
                                                [Var "x";
                                                 Fn ("+",
                                                  [Fn ("0", []);
                                                   Fn ("*",
                                                    [Var "x";
                                                     Fn ("-2", [])])])])])])])])])])]);
                                 Fn ("*",
                                  [Var "a";
                                   Fn ("+",
                                    [Fn ("0", []);
                                     Fn ("*",
                                      [Var "b";
                                       Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*",
                                          [Var "x";
                                           Fn ("+",
                                            [Fn ("0", []);
                                             Fn ("*",
                                              [Var "x";
                                               Fn ("+",
                                                [Fn ("0", []);
                                                 Fn ("*",
                                                  [Var "x";
                                                   Fn ("+",
                                                    [Fn ("0", []);
                                                     Fn ("*",
                                                      [Var "x";
                                                       Fn ("-1", [])])])])])])])])])])])])])])])])])])]);
                   Fn ("0", [])])))))),
         Atom
          (R ("=",
            [Fn ("+",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                 Fn ("*",
                  [Var "b";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
               Fn ("*",
                [Var "a";
                 Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "x";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])]);
             Fn ("0", [])]))),
       And
        (Or
          (And
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                 Fn ("0", [])])),
            Or
             (And
               (Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                    Fn ("0", [])])),
               And
                (Atom
                  (R ("=",
                    [Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                     Fn ("0", [])])),
                Not
                 (Atom
                   (R ("=",
                     [Fn ("+",
                       [Fn ("+",
                         [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                        Fn ("*",
                         [Var "a";
                          Fn ("+",
                           [Fn ("0", []);
                            Fn ("*", [Var "x"; Fn ("1", [])])])])]);
                      Fn ("0", [])]))))),
             And
              (Not
                (Atom
                  (R ("=",
                    [Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                     Fn ("0", [])]))),
              Not
               (Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("+",
                       [Fn ("0", []);
                        Fn ("*",
                         [Var "b";
                          Fn ("+",
                           [Fn ("0", []);
                            Fn ("*",
                             [Var "b";
                              Fn ("+",
                               [Fn ("+",
                                 [Fn ("0", []);
                                  Fn ("*", [Var "c"; Fn ("1", [])])]);
                                Fn ("*",
                                 [Var "b";
                                  Fn ("+",
                                   [Fn ("0", []);
                                    Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])]);
                      Fn ("*",
                       [Var "a";
                        Fn ("+",
                         [Fn ("+",
                           [Fn ("0", []);
                            Fn ("*",
                             [Var "c";
                              Fn ("+",
                               [Fn ("0", []);
                                Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
                          Fn ("*",
                           [Var "b";
                            Fn ("+",
                             [Fn ("0", []);
                              Fn ("*",
                               [Var "b";
                                Fn ("+",
                                 [Fn ("0", []);
                                  Fn ("*",
                                   [Var "x";
                                    Fn ("+",
                                     [Fn ("0", []);
                                      Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])])])]);
                    Fn ("0", [])])))))),
          And
           (Not
             (Atom
               (R ("=",
                 [Fn ("+",
                   [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                  Fn ("0", [])]))),
           Not
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "a";
                     Fn ("+",
                      [Fn ("0", []);
                       Fn ("*",
                        [Var "a";
                         Fn ("+",
                          [Fn ("0", []);
                           Fn ("*",
                            [Var "a";
                             Fn ("+",
                              [Fn ("+",
                                [Fn ("+",
                                  [Fn ("0", []);
                                   Fn ("*",
                                    [Var "c";
                                     Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*", [Var "c"; Fn ("1", [])])])])]);
                                 Fn ("*",
                                  [Var "b";
                                   Fn ("+",
                                    [Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*",
                                        [Var "c";
                                         Fn ("+",
                                          [Fn ("0", []);
                                           Fn ("*",
                                            [Var "x"; Fn ("2", [])])])])]);
                                     Fn ("*",
                                      [Var "b";
                                       Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*",
                                          [Var "x";
                                           Fn ("+",
                                            [Fn ("0", []);
                                             Fn ("*",
                                              [Var "x"; Fn ("1", [])])])])])])])])]);
                               Fn ("*",
                                [Var "a";
                                 Fn ("+",
                                  [Fn ("+",
                                    [Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*",
                                        [Var "c";
                                         Fn ("+",
                                          [Fn ("0", []);
                                           Fn ("*",
                                            [Var "x";
                                             Fn ("+",
                                              [Fn ("0", []);
                                               Fn ("*",
                                                [Var "x"; Fn ("2", [])])])])])])]);
                                     Fn ("*",
                                      [Var "b";
                                       Fn ("+",
                                        [Fn ("0", []);
                                         Fn ("*",
                                          [Var "x";
                                           Fn ("+",
                                            [Fn ("0", []);
                                             Fn ("*",
                                              [Var "x";
                                               Fn ("+",
                                                [Fn ("0", []);
                                                 Fn ("*",
                                                  [Var "x"; Fn ("2", [])])])])])])])])]);
                                   Fn ("*",
                                    [Var "a";
                                     Fn ("+",
                                      [Fn ("0", []);
                                       Fn ("*",
                                        [Var "x";
                                         Fn ("+",
                                          [Fn ("0", []);
                                           Fn ("*",
                                            [Var "x";
                                             Fn ("+",
                                              [Fn ("0", []);
                                               Fn ("*",
                                                [Var "x";
                                                 Fn ("+",
                                                  [Fn ("0", []);
                                                   Fn ("*",
                                                    [Var "x"; Fn ("1", [])])])])])])])])])])])])])])])])])])]);
                 Fn ("0", [])]))))),
        Atom
         (R ("=",
           [Fn ("+",
             [Fn ("+",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                Fn ("*",
                 [Var "b";
                  Fn ("+",
                   [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
              Fn ("*",
               [Var "a";
                Fn ("+",
                 [Fn ("0", []);
                  Fn ("*",
                   [Var "x";
                    Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])]);
            Fn ("0", [])])))));
    |]

[<TestCase(@"(a * x^2 + b * x + c = 0) /\
  (a * y^2 + b * y + c = 0) /\
  (forall z. (a * z^2 + b * z + c = 0)
       ==> (z = x) \/ (z = y))
  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", 0)>]
[<TestCase(@"~(forall x1 y1 x2 y2 x3 y3.
      exists x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\
                    (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2)", 1)>]
[<TestCase(@"forall a b c.
      (exists x y. (a * x^2 + b * x + c = 0) /\
             (a * y^2 + b * y + c = 0) /\
             ~(x = y)) <=>
      (a = 0) /\ (b = 0) /\ (c = 0) \/
      ~(a = 0) /\ ~(b^2 = 4 * a * c)", 2)>]
[<TestCase(@"~(forall x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
        (x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2
        ==> x0 = x0' /\ y0 = y0')", 3)>]
[<TestCase(@"forall a b c.
        a * x^2 + b * x + c = 0 /\
        a * y^2 + b * y + c = 0 /\
        ~(x = y)
        ==> a * (x + y) + b = 0", 4)>]
[<TestCase(@"forall a b c.
        (a * x^2 + b * x + c = 0) /\
        (2 * a * y^2 + 2 * b * y + 2 * c = 0) /\
        ~(x = y)
        ==> (a * (x + y) + b = 0)", 5)>]
[<TestCase(@"forall y_1 y_2 y_3 y_4.
       (y_1 = 2 * y_3) /\
       (y_2 = 2 * y_4) /\
       (y_1 * y_3 = y_2 * y_4)
       ==> (y_1^2 = y_2^2)", 6)>]
[<TestCase(@"forall y.
         a * x^2 + b * x + c = 0 /\
         a * y^2 + b * y + c = 0 /\
         ~(x = y)
         ==> a * x * y = c /\ a * (x + y) + b = 0", 7)>]
let ``examples 3`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_3.[idx]

(* NOTE : This test case, originally from ``examples 3``, cannot be used
            because it's printed form (from the OCaml toplevel) is over 15k lines!

[<TestCase(@"forall y. (a * x^2 + b * x + c = 0) /\
        (a * y^2 + b * y + c = 0) /\
        (forall z. (a * z^2 + b * z + c = 0)
                    ==> (z = x) \/ (z = y))
        ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", 1)>]
*)

let private example_results_3a : formula<fol>[] = [|
    True;
    True;
    True;
    True;
    True;
    |]

[<TestCase(@"a * x^2 + b * x + c = 0 /\
    a * y^2 + b * y + c = 0 /\
    ~(x = y)
    ==> a * x * y = c /\ a * (x + y) + b = 0", 0)>]
[<TestCase(@"(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)", 1)>]
[<TestCase(@"(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)", 2)>]
[<TestCase(@"(y1 * y3 + x1 * x3 = 0) /\
  (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) /\
  ~(x3 = 0) /\
  ~(y3 = 0)
  ==> (y1 * (x2 - x3) = x1 * (y2 - y3))", 3)>]
[<TestCase(@"a * x^2 + b * x + c = 0 /\
    a * y^2 + b * y + c = 0 /\
    ~(x = y)
    ==> a * x * y = c /\ a * (x + y) + b = 0", 4)>]
let ``examples 3a`` (f, idx) =
    parse f
    |> generalize
    |> complex_qelim
    |> should equal example_results_3a.[idx]


(* ------------------------------------------------------------------------- *)
(* Checking resultants from Maple.                                           *)
(* ------------------------------------------------------------------------- *)

let private example_results_4 : formula<fol>[] = [|
    True;
    True;
    True;
    |]

[<TestCase(@"forall a b c.
           (exists x. a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0) \/ (a = 0) <=>
           (4*a^2*c-b^2*a = 0)", 0)>]
[<TestCase(@"forall a b c d e.
            (exists x. a * x^2 + b * x + c = 0 /\ d * x + e = 0) \/
            a = 0 /\ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0", 1)>]
[<TestCase(@"forall a b c d e f.
           (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
           (a = 0) /\ (d = 0) <=>
           d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0", 2)>]
let ``examples 4`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_4.[idx]


(* ------------------------------------------------------------------------- *)
(* Some trigonometric addition formulas (checking stuff from Maple).         *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 5``() =
    @"forall x y. x^2 + y^2 = 1 ==> (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1"
    |> parse
    |> complex_qelim
    |> should equal formula<fol>.True


(* ------------------------------------------------------------------------- *)
(* The examples from my thesis.                                              *)
(* ------------------------------------------------------------------------- *)

let private example_results_6 : formula<fol>[] = [|
    True;
    True;
    True;
    |]

[<TestCase(@"forall s c. s^2 + c^2 = 1
            ==> 2 * s - (2 * s * c * c - s^3) = 3 * s^3", 0)>]
[<TestCase(@"forall u v.
  -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
     (((7 * u^6) * v) * v - (u * u^7)) * 144 -
     (((5 * u^4) * v) * v - (u * u^5)) * 168 -
     (((3 * u^2) * v) * v - (u * u^3)) * 210 -
     (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
   (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
   (u^2 + v^2 - 1)", 1)>]
[<TestCase(@"forall u v.
        u^2 + v^2 = 1
        ==> (((9 * u^8) * v) * v - (u * u^9)) * 128 +
            (((7 * u^6) * v) * v - (u * u^7)) * 144 +
            (((5 * u^4) * v) * v - (u * u^5)) * 168 +
            (((3 * u^2) * v) * v - (u * u^3)) * 210 +
            (v * v - (u * u)) * 315 + 1280 * u^10 = 315", 2)>]
let ``examples 6`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_6.[idx]


(* ------------------------------------------------------------------------- *)
(* Deliberately silly examples from Poizat's model theory book (6.6).        *)
(* ------------------------------------------------------------------------- *)

let private example_results_7 : formula<fol>[] = [|
    Or
     (And
       (Atom
         (R ("=",
           [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
            Fn ("0", [])])),
       Not
        (Atom
          (R ("=",
            [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
             Fn ("0", [])])))),
     Not
      (Atom
        (R ("=",
          [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
           Fn ("0", [])]))));
    Not
     (And
       (Atom
         (R ("=",
           [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
            Fn ("0", [])])),
       Or
        (And
          (Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("2", [])])]);
               Fn ("0", [])])),
          And
           (Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
                Fn ("0", [])])),
           Not
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("0", []); Fn ("*", [Var "z"; Fn ("1", [])])]);
                 Fn ("0", [])]))))),
        And
         (Not
           (Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("2", [])])]);
                Fn ("0", [])]))),
         Not
          (Atom
            (R ("=",
              [Fn ("+",
                [Fn ("0", []);
                 Fn ("*",
                  [Var "x";
                   Fn ("+",
                    [Fn ("+",
                      [Fn ("0", []);
                       Fn ("*",
                        [Var "y";
                         Fn ("+",
                          [Fn ("0", []);
                           Fn ("*", [Var "y"; Fn ("-1", [])])])])]);
                     Fn ("*",
                      [Var "x";
                       Fn ("+",
                        [Fn ("0", []); Fn ("*", [Var "z"; Fn ("4", [])])])])])])]);
               Fn ("0", [])])))))));
    |]

[<TestCase(@"exists z. x * z^87 + y * z^44 + 1 = 0", 0)>]
[<TestCase(@"forall u. exists v. x * (u + v^2)^2 + y * (u + v^2) + z = 0", 1)>]
let ``examples 7`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_7.[idx]


(* ------------------------------------------------------------------------- *)
(* Actually prove simple equivalences.                                       *)
(* ------------------------------------------------------------------------- *)

let private example_results_8 : formula<fol>[] = [|
    True;
    True;
    |]

[<TestCase(@"forall x y. (exists z. x * z^87 + y * z^44 + 1 = 0)
                  <=> ~(x = 0) \/ ~(y = 0)", 0)>]
[<TestCase(@"forall x y z. (forall u. exists v.
                         x * (u + v^2)^2 + y * (u + v^2) + z = 0)
                    <=> ~(x = 0) \/ ~(y = 0) \/ z = 0", 1)>]
let ``examples 8`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_8.[idx]


(* ------------------------------------------------------------------------- *)
(* Invertibility of 2x2 matrix in terms of nonzero determinant.              *)
(* ------------------------------------------------------------------------- *)

let private example_results_9 : formula<fol>[] = [|
    // CPU time (user): 0.004
    And
     (Or
       (And
         (Not
           (Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                Fn ("0", [])]))),
         Or
          (And
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("+",
                    [Fn ("0", []);
                     Fn ("*",
                      [Var "b";
                       Fn ("+",
                        [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])])])]);
                   Fn ("*",
                    [Var "a";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
                 Fn ("0", [])])),
            Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
                Fn ("0", [])]))),
          Not
           (Atom
             (R ("=",
               [Fn ("+",
                 [Fn ("+",
                   [Fn ("0", []);
                    Fn ("*",
                     [Var "b";
                      Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])])])]);
                  Fn ("*",
                   [Var "a";
                    Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
                Fn ("0", [])]))))),
       Or
        (And
          (Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
               Fn ("0", [])])),
          And
           (Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
                Fn ("0", [])])),
           And
            (Not
              (Atom
                (R ("=",
                  [Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                   Fn ("0", [])]))),
            Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                Fn ("0", [])]))))),
        And
         (Atom
           (R ("=",
             [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
              Fn ("0", [])])),
         And
          (Not
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
                 Fn ("0", [])]))),
          Not
           (Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
                Fn ("0", [])]))))))),
     Or
      (And
        (Not
          (Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
               Fn ("0", [])]))),
        Or
         (And
           (Atom
             (R ("=",
               [Fn ("+",
                 [Fn ("+",
                   [Fn ("0", []);
                    Fn ("*",
                     [Var "b";
                      Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
                  Fn ("*",
                   [Var "a";
                    Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])])])]);
                Fn ("0", [])])),
           Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
               Fn ("0", [])]))),
         Not
          (Atom
            (R ("=",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "b";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
                 Fn ("*",
                  [Var "a";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])])])]);
               Fn ("0", [])]))))),
      Or
       (And
         (Atom
           (R ("=",
             [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
              Fn ("0", [])])),
         And
          (Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
               Fn ("0", [])])),
          And
           (Not
             (Atom
               (R ("=",
                 [Fn ("+",
                   [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
                  Fn ("0", [])]))),
           Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
               Fn ("0", [])]))))),
       And
        (Atom
          (R ("=",
            [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
             Fn ("0", [])])),
        And
         (Not
           (Atom
             (R ("=",
               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
                Fn ("0", [])]))),
         Not
          (Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
               Fn ("0", [])]))))))));
    // CPU time (user): 0.060004
    True;
    |]

[<TestCase(@"exists w x y z. (a * w + b * y = 1) /\
                      (a * x + b * z = 0) /\
                      (c * w + d * y = 0) /\
                      (c * x + d * z = 1)", 0)>]
[<TestCase(@"forall a b c d.
        (exists w x y z. (a * w + b * y = 1) /\
                         (a * x + b * z = 0) /\
                         (c * w + d * y = 0) /\
                         (c * x + d * z = 1))
        <=> ~(a * d = b * c)", 1)>]
let ``examples 9`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_9.[idx]


(* ------------------------------------------------------------------------- *)
(* Inspired by Cardano's formula for a cubic. Not all complex cbrts work.    *)
(* ------------------------------------------------------------------------- *)

let private example_results_10 : formula<fol>[] = [|
    False;
    True;
    |]

[<TestCase(@"forall m n x u t cu ct.
   t - u = n /\ 27 * t * u = m^3 /\
   ct^3 = t /\ cu^3 = u /\
   x = ct - cu
   ==> x^3 + m * x = n", 0)>]
[<TestCase(@"forall m n x u t.
   t - u = n /\ 27 * t * u = m^3
   ==> exists ct cu. ct^3 = t /\ cu^3 = u /\
                     (x = ct - cu ==> x^3 + m * x = n)", 1)>]
[<Category("LongRunning")>]
let ``examples 10`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_10.[idx]


(* ------------------------------------------------------------------------- *)
(* SOS in rational functions for Motzkin polynomial (dehomogenized).         *)
(* Of course these are just trivial normalization, nothing deep.             *)
(* ------------------------------------------------------------------------- *)

let private example_results_11 : formula<fol>[] = [|
    True;
    True;
    True;
    True;
    |]

[<TestCase(@"forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
     x^2 * y^2 * (x^2 + y^2 + 1) * (x^2 + y^2 - 2)^2 + (x^2 - y^2)^2", 0)>]
[<TestCase(@"forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    x^2 * y^2 * x^2  * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * y^2 * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
    (x^2 - y^2)^2", 1)>]
[<TestCase(@"forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    x^4 * y^2 * (x^2 + y^2 - 2)^2 +
    x^2 * y^4 * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
    (x^2 - y^2)^2", 2)>]
[<TestCase(@"forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    (x^2 * y * (x^2 + y^2 - 2))^2 +
    (x * y^2 * (x^2 + y^2 - 2))^2 +
    (x * y * (x^2 + y^2 - 2))^2 +
    (x^2 - y^2)^2", 3)>]
let ``examples 11`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_11.[idx]


(* ------------------------------------------------------------------------- *)
(* A cute bilinear identity -- see ch14 of Rajwade's "Squares" for more.     *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 12``() =
    @"(x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_6^2 + x_7^2 + x_8^2 + x_9^2) *
    (y_1^2 + y_2^2 + y_3^2 + y_4^2 + y_5^2 + y_6^2 + y_7^2 + y_8^2 +
    y_9^2 + y_10^2 + y_11^2 + y_12^2 + y_13^2 + y_14^2 + y_15^2 + y_16^2) -
    ((0 + x_1 * y_1 + x_2 * y_2 + x_3 * y_3 + x_4 * y_4 + x_5 * y_5 + x_6 * y_6 + x_7 * y_7 + x_8 * y_8 + x_9 * y_9)^2 +
    (0 - x_2 * y_1 + x_1 * y_2 + x_4 * y_3 - x_3 * y_4 + x_6 * y_5 - x_5 * y_6 - x_8 * y_7 + x_7 * y_8 + x_9 * y_10)^2 +
    (0 - x_3 * y_1 - x_4 * y_2 + x_1 * y_3 + x_2 * y_4 + x_7 * y_5 + x_8 * y_6 - x_5 * y_7 - x_6 * y_8 + x_9 * y_11)^2 +
    (0 - x_4 * y_1 + x_3 * y_2 - x_2 * y_3 + x_1 * y_4 + x_8 * y_5 - x_7 * y_6 + x_6 * y_7 - x_5 * y_8 + x_9 * y_12)^2 +
    (0 - x_5 * y_1 - x_6 * y_2 - x_7 * y_3 - x_8 * y_4 + x_1 * y_5 + x_2 * y_6 + x_3 * y_7 + x_4 * y_8 + x_9 * y_13)^2 +
    (0 - x_6 * y_1 + x_5 * y_2 - x_8 * y_3 + x_7 * y_4 - x_2 * y_5 + x_1 * y_6 - x_4 * y_7 + x_3 * y_8 + x_9 * y_14)^2 +
    (0 - x_7 * y_1 + x_8 * y_2 + x_5 * y_3 - x_6 * y_4 - x_3 * y_5 + x_4 * y_6 + x_1 * y_7 - x_2 * y_8 + x_9 * y_15)^2 +
    (0 - x_8 * y_1 - x_7 * y_2 + x_6 * y_3 + x_5 * y_4 - x_4 * y_5 - x_3 * y_6 + x_2 * y_7 + x_1 * y_8 + x_9 * y_16)^2 +
    (0 - x_9 * y_1 + x_1 * y_9 - x_2 * y_10 - x_3 * y_11 - x_4 * y_12 - x_5 * y_13 - x_6 * y_14 - x_7 * y_15 - x_8 * y_16)^2 +
    (0 - x_9 * y_2 + x_2 * y_9 + x_1 * y_10 - x_4 * y_11 + x_3 * y_12 - x_6 * y_13 + x_5 * y_14 + x_8 * y_15 - x_7 * y_16)^2 +
    (0 - x_9 * y_3 + x_3 * y_9 + x_4 * y_10 + x_1 * y_11 - x_2 * y_12 - x_7 * y_13 - x_8 * y_14 + x_5 * y_15 + x_6 * y_16)^2 +
    (0 - x_9 * y_4 + x_4 * y_9 - x_3 * y_10 + x_2 * y_11 + x_1 * y_12 - x_8 * y_13 + x_7 * y_14 - x_6 * y_15 + x_5 * y_16)^2 +
    (0 - x_9 * y_5 + x_5 * y_9 + x_6 * y_10 + x_7 * y_11 + x_8 * y_12 + x_1 * y_13 - x_2 * y_14 - x_3 * y_15 - x_4 * y_16)^2 +
    (0 - x_9 * y_6 + x_6 * y_9 - x_5 * y_10 + x_8 * y_11 - x_7 * y_12 + x_2 * y_13 + x_1 * y_14 + x_4 * y_15 - x_3 * y_16)^2 +
    (0 - x_9 * y_7 + x_7 * y_9 - x_8 * y_10 - x_5 * y_11 + x_6 * y_12 + x_3 * y_13 - x_4 * y_14 + x_1 * y_15 + x_2 * y_16)^2 +
    (0 - x_9 * y_8 + x_8 * y_9 + x_7 * y_10 - x_6 * y_11 - x_5 * y_12 + x_4 * y_13 + x_3 * y_14 - x_2 * y_15 + x_1 * y_16)^2)"
    |> parset
    |> polytest
    |> should equal
    <| Fn ("0", [])

(* ------------------------------------------------------------------------- *)
(* This is essentially the Cauchy-Riemann conditions for a differential.     *)
(* ------------------------------------------------------------------------- *)

let private example_results_13 : formula<fol>[] = [|
    // CPU time (user): 0.004
    Not
     (And
       (Or
         (And
           (Atom
             (R ("=",
               [Fn ("+",
                 [Fn ("+",
                   [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
                  Fn ("*", [Var "d"; Fn ("1", [])])]);
                Fn ("0", [])])),
           And
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])]);
                   Fn ("*", [Var "b"; Fn ("1", [])])]);
                 Fn ("0", [])])),
            Or
             (And
               (Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
                      Fn ("*", [Var "a"; Fn ("1", [])])]);
                    Fn ("0", [])])),
               Or
                (Atom
                  (R ("=",
                    [Fn ("+",
                      [Fn ("+",
                        [Fn ("0", []); Fn ("*", [Var "v"; Fn ("-1", [])])]);
                       Fn ("*", [Var "c"; Fn ("1", [])])]);
                     Fn ("0", [])])),
                Not
                 (Atom
                   (R ("=",
                     [Fn ("+",
                       [Fn ("+",
                         [Fn ("0", []); Fn ("*", [Var "v"; Fn ("-1", [])])]);
                        Fn ("*", [Var "c"; Fn ("1", [])])]);
                      Fn ("0", [])]))))),
             Not
              (Atom
                (R ("=",
                  [Fn ("+",
                    [Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
                     Fn ("*", [Var "a"; Fn ("1", [])])]);
                   Fn ("0", [])])))))),
         Or
          (And
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])]);
                   Fn ("*", [Var "b"; Fn ("1", [])])]);
                 Fn ("0", [])])),
            And
             (Not
               (Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
                      Fn ("*", [Var "d"; Fn ("1", [])])]);
                    Fn ("0", [])]))),
             Or
              (Atom
                (R ("=",
                  [Fn ("+",
                    [Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
                     Fn ("*", [Var "a"; Fn ("1", [])])]);
                   Fn ("0", [])])),
              Not
               (Atom
                 (R ("=",
                   [Fn ("+",
                     [Fn ("+",
                       [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
                      Fn ("*", [Var "a"; Fn ("1", [])])]);
                    Fn ("0", [])])))))),
          And
           (Not
             (Atom
               (R ("=",
                 [Fn ("+",
                   [Fn ("+",
                     [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])]);
                    Fn ("*", [Var "b"; Fn ("1", [])])]);
                  Fn ("0", [])]))),
           Or
            (Atom
              (R ("=",
                [Fn ("+",
                  [Fn ("+",
                    [Fn ("+",
                      [Fn ("+",
                        [Fn ("+",
                          [Fn ("+",
                            [Fn ("0", []);
                             Fn ("*",
                              [Var "v";
                               Fn ("+",
                                [Fn ("0", []);
                                 Fn ("*", [Var "v"; Fn ("-1", [])])])])]);
                           Fn ("*",
                            [Var "u";
                             Fn ("+",
                              [Fn ("0", []);
                               Fn ("*", [Var "u"; Fn ("-1", [])])])])]);
                         Fn ("*",
                          [Var "d";
                           Fn ("+",
                            [Fn ("0", []);
                             Fn ("*", [Var "u"; Fn ("1", [])])])])]);
                       Fn ("*",
                        [Var "c";
                         Fn ("+",
                          [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])])])]);
                     Fn ("*",
                      [Var "b";
                       Fn ("+",
                        [Fn ("+",
                          [Fn ("0", []);
                           Fn ("*", [Var "v"; Fn ("-1", [])])]);
                         Fn ("*", [Var "c"; Fn ("1", [])])])])]);
                   Fn ("*",
                    [Var "a";
                     Fn ("+",
                      [Fn ("+",
                        [Fn ("0", []); Fn ("*", [Var "u"; Fn ("1", [])])]);
                       Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
                 Fn ("0", [])])),
            Not
             (Atom
               (R ("=",
                 [Fn ("+",
                   [Fn ("+",
                     [Fn ("+",
                       [Fn ("+",
                         [Fn ("+",
                           [Fn ("+",
                             [Fn ("0", []);
                              Fn ("*",
                               [Var "v";
                                Fn ("+",
                                 [Fn ("0", []);
                                  Fn ("*", [Var "v"; Fn ("-1", [])])])])]);
                            Fn ("*",
                             [Var "u";
                              Fn ("+",
                               [Fn ("0", []);
                                Fn ("*", [Var "u"; Fn ("-1", [])])])])]);
                          Fn ("*",
                           [Var "d";
                            Fn ("+",
                             [Fn ("0", []);
                              Fn ("*", [Var "u"; Fn ("1", [])])])])]);
                        Fn ("*",
                         [Var "c";
                          Fn ("+",
                           [Fn ("0", []);
                            Fn ("*", [Var "v"; Fn ("1", [])])])])]);
                      Fn ("*",
                       [Var "b";
                        Fn ("+",
                         [Fn ("+",
                           [Fn ("0", []);
                            Fn ("*", [Var "v"; Fn ("-1", [])])]);
                          Fn ("*", [Var "c"; Fn ("1", [])])])])]);
                    Fn ("*",
                     [Var "a";
                      Fn ("+",
                       [Fn ("+",
                         [Fn ("0", []); Fn ("*", [Var "u"; Fn ("1", [])])]);
                        Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
                  Fn ("0", [])]))))))),
       Not
        (Atom
          (R ("=",
            [Fn ("+",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("-1", [])])]);
               Fn ("*", [Var "a"; Fn ("1", [])])]);
             Fn ("0", [])])))));
    // CPU time (user): 0.004
    True;
    // CPU time (user): 0.008001
    True;
    |]

[<TestCase(@"forall x y. (a * x + b * y = u * x - v * y) /\
                (c * x + d * y = u * y + v * x)
                ==> (a = d)", 0)>]
[<TestCase(@"forall a b c d.
      (forall x y. (a * x + b * y = u * x - v * y) /\
                   (c * x + d * y = u * y + v * x))
                   ==> (a = d) /\ (b = -(c))", 1)>]
[<TestCase(@"forall a b c d.
        (exists u v. forall x y. (a * x + b * y = u * x - v * y) /\
                                 (c * x + d * y = u * y + v * x))
        <=> (a = d) /\ (b = -(c))", 2)>]
let ``examples 13`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_13.[idx]

(* ------------------------------------------------------------------------- *)
(* Finding non-trivial perpendiculars to lines.                              *)
(* ------------------------------------------------------------------------- *)

let ``examples 14``() =
    @"forall x1 y1 x2 y2. exists a b.
      ~(a = 0 /\ b = 0) /\ a * x1 + b * y1 = 0 /\ a * x2 + b * y2 = 0"
    |> parse
    |> complex_qelim
    |> should equal False

