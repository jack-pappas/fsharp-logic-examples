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
    parse "((w + x)^4 + (w + y)^4 + (w + z)^4 +
             (x + y)^4 + (x + z)^4 + (y + z)^4 +
             (w - x)^4 + (w - y)^4 + (w - z)^4 +
             (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
            (w^2 + x^2 + y^2 + z^2)^2"
    |> fun f -> print_fol_formula f; f
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

[<TestCase("forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0", 0)>]
[<TestCase("forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0", 1)>]
[<TestCase("forall c. (forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0) <=> c = 1", 2)>]
[<TestCase("forall a b c x y.
              a * x^2 + b * x + c = 0 /\ a * y^2 + b * y + c = 0 /\ ~(x = y)
              ==> a * x * y = c /\ a * (x + y) + b = 0", 3)>]
let ``examples 1`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_1.[idx]


(* ------------------------------------------------------------------------- *)
(* More tests, not in the main text.                                         *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``lagrange_4``() =
    parset "((w + x)^4 + (w + y)^4 + (w + z)^4 +
             (x + y)^4 + (x + z)^4 + (y + z)^4 +
             (w - x)^4 + (w - y)^4 + (w - z)^4 +
             (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
            (w^2 + x^2 + y^2 + z^2)^2"
    |> polytest
    |> should equal
    <| Fn ("0", [])

[<Test>]
let ``lagrange_8``() =
    parset "((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
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
    parset "6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
      (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
     ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
      (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))"
    |> polytest
    |> should equal
    <| Fn ("0", [])

[<Test>]
let ``fleck``() =
    parset "60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
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
    parset "5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
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
    parset "22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
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

[<TestCase("exists x. x + 2 = 3", 0)>]
[<TestCase("exists x. x^2 + a = 3", 1)>]
[<TestCase("exists x. x^2 + x + 1 = 0", 2)>]
[<TestCase("exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0", 3)>]
[<TestCase("exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0", 4)>]
[<TestCase("forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0", 5)>]
[<TestCase("forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 6)>]
[<TestCase("exists a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)", 7)>]
[<TestCase("exists x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)", 8)>]
[<TestCase("forall x. x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 9)>]
[<TestCase("forall a. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 10)>]
[<TestCase("exists a b c x y.
                a * x^2 + b * x + c = 0 /\
                a * y^2 + b * y + c = 0 /\
                ~(x = y) /\
                ~(a * x * y = c)", 11)>]
[<TestCase("forall a b c x.
            (forall z. a * z^2 + b * z + c = 0 <=> z = x)
            ==> a * x * x = c /\ a * (x + x) + b = 0", 12)>]
[<TestCase("forall x y.
            (forall a b c. (a * x^2 + b * x + c = 0) /\
                   (a * y^2 + b * y + c = 0)
                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
                    <=> ~(x = y)", 13)>]
[<TestCase("forall y_1 y_2 y_3 y_4.
             (y_1 = 2 * y_3) /\
             (y_2 = 2 * y_4) /\
             (y_1 * y_3 = y_2 * y_4)
             ==> (y_1^2 = y_2^2)", 14)>]
[<TestCase("forall x y. x^2 = 2 /\ y^2 = 3
                ==> (x * y)^2 = 6", 15)>]
[<TestCase("forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
                ==> (x^4 + 1 = 0)", 16)>]
[<TestCase("forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
                ==> (x^4 + 1 = 0)", 17)>]
[<TestCase("~(exists a x y. (a^2 = 2) /\
             (x^2 + a * x + 1 = 0) /\
             (y * (x^4 + 1) + 1 = 0))", 18)>]
[<TestCase("forall x. exists y. x^2 = y^3", 19)>]
[<TestCase("forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
               2 * (b * x + b * z - a * y)", 20)>]
[<TestCase("forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)", 21)>]
[<TestCase("forall a b c x y. (a * x^2 + b * x + c = 0) /\
               (a * y^2 + b * y + c = 0) /\
               ~(x = y)
               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", 22)>]
[<TestCase("~(forall a b c x y. (a * x^2 + b * x + c = 0) /\
                 (a * y^2 + b * y + c = 0)
                 ==> (a * x * y = c) /\ (a * (x + y) + b = 0))", 23)>]
[<TestCase("forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)", 24)>]
[<TestCase("forall a1 b1 c1 a2 b2 c2.
            ~(a1 * b2 = a2 * b1)
            ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)", 25)>]
let ``examples 2`` (f, idx) =
    parse f
    |> complex_qelim
    |> should equal example_results_2.[idx]


(* ------------------------------------------------------------------------- *)
(* This seems harder, so see how many quantifiers are feasible.              *)
(* ------------------------------------------------------------------------- *)

// TODO : Implement remaining tests from complex.ml.



