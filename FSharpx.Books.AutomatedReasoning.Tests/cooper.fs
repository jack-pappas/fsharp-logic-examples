// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.cooper

open NUnit.Framework
open FsUnit

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.cooper

// pg.349
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

let private integer_qelim_results1 : formula<fol>[] = [|
    True;
    True;
    False;
    True;
    Not
     (Atom
       (R ("<",
         [Fn ("0", []);
          Fn ("+",
           [Fn ("*", [Fn ("1", []); Var "a"]);
            Fn ("+", [Fn ("*", [Fn ("-1", []); Var "b"]); Fn ("-1", [])])])])));
    |]

// cooper.p001
[<TestCase(@"forall x y. ~(2 * x + 1 = 2 * y)", 0)>]

// cooper.p002
[<TestCase(@"forall x. exists y. 2 * y <= x /\ x < 2 * (y + 1)", 1)>]

// cooper.p003
[<TestCase(@"exists x y. 4 * x - 6 * y = 1", 2)>]

// cooper.p004
[<TestCase(@"forall x. ~divides(2,x) /\ divides(3,x-1) <=> divides(12,x-1) \/ divides(12,x-7)", 3)>]

// cooper.p005
[<TestCase(@"forall x. b < x ==> a <= x", 4)>]

let ``integer_qelim examples 1`` (f, idx) =
    integer_qelim (parse f)
    |> should equal integer_qelim_results1.[idx]

// cooper.p006
[<Test>]
let ``natural_qelim examples 1``() =
    natural_qelim (parse "forall d. exists x y. 3 * x + 5 * y = d")
    |> should equal formula<fol>.False

(* ------------------------------------------------------------------------- *)
(* Natural number version.                                                   *)
(* ------------------------------------------------------------------------- *)

// cooper.p007
[<Test>]
let ``integer_qelim examples 2``() =
    integer_qelim (parse @"forall d. exists x y. 3 * x + 5 * y = d")
    |> should equal formula<fol>.True

let private natural_qelim_results2 = [|
    formula<fol>.True;
    formula<fol>.True;
    |]

// cooper.p008
[<TestCase(@"forall d. d >= 8 ==> exists x y. 3 * x + 5 * y = d", 0)>]

// cooper.p009
[<TestCase(@"forall d. exists x y. 3 * x - 5 * y = d", 1)>]

let ``natural_qelim examples 2`` (f, idx) =
    natural_qelim (parse f)
    |> should equal natural_qelim_results2.[idx]

(* ------------------------------------------------------------------------- *)
(* Other tests, not in the main text.                                        *)
(* ------------------------------------------------------------------------- *)

let private other_integer_qelim_results1 : formula<fol>[] = [|
    True;
    False;
    Not
     (Or
       (And
         (Atom
           (R ("divides",
             [Fn ("3", []);
              Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("1", [])])])),
         Atom
          (R ("<",
            [Fn ("0", []);
             Fn ("+",
              [Fn ("*", [Fn ("-1", []); Var "a"]);
               Fn ("+", [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("0", [])])])]))),
       Or
        (And
          (Atom
            (R ("divides",
              [Fn ("3", []);
               Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("2", [])])])),
          Atom
           (R ("<",
             [Fn ("0", []);
              Fn ("+",
               [Fn ("*", [Fn ("-1", []); Var "a"]);
                Fn ("+",
                 [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-1", [])])])]))),
        And
         (Atom
           (R ("divides",
             [Fn ("3", []);
              Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("3", [])])])),
         Atom
          (R ("<",
            [Fn ("0", []);
             Fn ("+",
              [Fn ("*", [Fn ("-1", []); Var "a"]);
               Fn ("+", [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-2", [])])])]))))));
    False;
    Imp
     (Atom
       (R ("divides",
         [Fn ("65", []);
          Fn ("+", [Fn ("*", [Fn ("1", []); Var "y"]); Fn ("0", [])])])),
     Atom
      (R ("divides",
        [Fn ("5", []);
         Fn ("+", [Fn ("*", [Fn ("1", []); Var "y"]); Fn ("0", [])])])));
    True;
    True;
    True;
    Not
     (Atom
       (R ("<",
         [Fn ("0", []);
          Fn ("+",
           [Fn ("*", [Fn ("-1", []); Var "a"]);
            Fn ("+", [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("0", [])])])])));
    Not
     (Atom
       (R ("<",
         [Fn ("0", []);
          Fn ("+",
           [Fn ("*", [Fn ("-1", []); Var "a"]);
            Fn ("+", [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("1", [])])])])));
    |]

// cooper.p010
[<TestCase(@"exists x y. x > 0 /\ y >= 0 /\ 3 * x - 5 * y = 1", 0)>]

// cooper.p011
[<TestCase(@"exists x y z. 4 * x - 6 * y = 1", 1)>]

// cooper.p012
[<TestCase(@"forall x. a < 3 * x ==> b < 3 * x", 2)>]

// cooper.p013
[<TestCase(@"forall x y. x <= y ==> 2 * x + 1 < 2 * y", 3)>]

// cooper.p014
[<TestCase(@"(exists d. y = 65 * d) ==> (exists d. y = 5 * d)", 4)>]

// cooper.p015
[<TestCase(@"forall y. (exists d. y = 65 * d) ==> (exists d. y = 5 * d)", 5)>]

// cooper.p016
[<TestCase(@"forall x y. ~(2 * x + 1 = 2 * y)", 6)>]

// cooper.p017
[<TestCase(@"forall x y z. (2 * x + 1 = 2 * y) ==> x + y + z > 129", 7)>]

// cooper.p018
[<TestCase(@"forall x. a < x ==> b < x", 8)>]

// cooper.p019
[<TestCase(@"forall x. a <= x ==> b < x", 9)>]

let ``integer_qelim examples other 1`` (f, idx) =
    integer_qelim (parse f)
    |> should equal other_integer_qelim_results1.[idx]

(* ------------------------------------------------------------------------- *)
(* Formula examples from Cooper's paper.                                     *)
(* ------------------------------------------------------------------------- *)

let private other_integer_qelim_results2 : formula<fol>[] = [|
    False;
    Or
     (And
       (Atom
         (R ("divides",
           [Fn ("20", []);
            Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("1", [])])])),
       Atom
        (R ("<",
          [Fn ("0", []);
           Fn ("+",
            [Fn ("*", [Fn ("-1", []); Var "a"]);
             Fn ("+", [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-1", [])])])]))),
     Or
      (And
        (Atom
          (R ("divides",
            [Fn ("20", []);
             Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("2", [])])])),
        Atom
         (R ("<",
           [Fn ("0", []);
            Fn ("+",
             [Fn ("*", [Fn ("-1", []); Var "a"]);
              Fn ("+", [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-2", [])])])]))),
      Or
       (And
         (Atom
           (R ("divides",
             [Fn ("20", []);
              Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("3", [])])])),
         Atom
          (R ("<",
            [Fn ("0", []);
             Fn ("+",
              [Fn ("*", [Fn ("-1", []); Var "a"]);
               Fn ("+", [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-3", [])])])]))),
       Or
        (And
          (Atom
            (R ("divides",
              [Fn ("20", []);
               Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("4", [])])])),
          Atom
           (R ("<",
             [Fn ("0", []);
              Fn ("+",
               [Fn ("*", [Fn ("-1", []); Var "a"]);
                Fn ("+",
                 [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-4", [])])])]))),
        Or
         (And
           (Atom
             (R ("divides",
               [Fn ("20", []);
                Fn ("+", [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("5", [])])])),
           Atom
            (R ("<",
              [Fn ("0", []);
               Fn ("+",
                [Fn ("*", [Fn ("-1", []); Var "a"]);
                 Fn ("+",
                  [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-5", [])])])]))),
         Or
          (And
            (Atom
              (R ("divides",
                [Fn ("20", []);
                 Fn ("+",
                  [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("6", [])])])),
            Atom
             (R ("<",
               [Fn ("0", []);
                Fn ("+",
                 [Fn ("*", [Fn ("-1", []); Var "a"]);
                  Fn ("+",
                   [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-6", [])])])]))),
          Or
           (And
             (Atom
               (R ("divides",
                 [Fn ("20", []);
                  Fn ("+",
                   [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("7", [])])])),
             Atom
              (R ("<",
                [Fn ("0", []);
                 Fn ("+",
                  [Fn ("*", [Fn ("-1", []); Var "a"]);
                   Fn ("+",
                    [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-7", [])])])]))),
           Or
            (And
              (Atom
                (R ("divides",
                  [Fn ("20", []);
                   Fn ("+",
                    [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("8", [])])])),
              Atom
               (R ("<",
                 [Fn ("0", []);
                  Fn ("+",
                   [Fn ("*", [Fn ("-1", []); Var "a"]);
                    Fn ("+",
                     [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-8", [])])])]))),
            Or
             (And
               (Atom
                 (R ("divides",
                   [Fn ("20", []);
                    Fn ("+",
                     [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("9", [])])])),
               Atom
                (R ("<",
                  [Fn ("0", []);
                   Fn ("+",
                    [Fn ("*", [Fn ("-1", []); Var "a"]);
                     Fn ("+",
                      [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-9", [])])])]))),
             Or
              (And
                (Atom
                  (R ("divides",
                    [Fn ("20", []);
                     Fn ("+",
                      [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("10", [])])])),
                Atom
                 (R ("<",
                   [Fn ("0", []);
                    Fn ("+",
                     [Fn ("*", [Fn ("-1", []); Var "a"]);
                      Fn ("+",
                       [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-10", [])])])]))),
              Or
               (And
                 (Atom
                   (R ("divides",
                     [Fn ("20", []);
                      Fn ("+",
                       [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("11", [])])])),
                 Atom
                  (R ("<",
                    [Fn ("0", []);
                     Fn ("+",
                      [Fn ("*", [Fn ("-1", []); Var "a"]);
                       Fn ("+",
                        [Fn ("*", [Fn ("1", []); Var "b"]); Fn ("-11", [])])])]))),
               Or
                (And
                  (Atom
                    (R ("divides",
                      [Fn ("20", []);
                       Fn ("+",
                        [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("12", [])])])),
                  Atom
                   (R ("<",
                     [Fn ("0", []);
                      Fn ("+",
                       [Fn ("*", [Fn ("-1", []); Var "a"]);
                        Fn ("+",
                         [Fn ("*", [Fn ("1", []); Var "b"]);
                          Fn ("-12", [])])])]))),
                Or
                 (And
                   (Atom
                     (R ("divides",
                       [Fn ("20", []);
                        Fn ("+",
                         [Fn ("*", [Fn ("1", []); Var "a"]); Fn ("13", [])])])),
                   Atom
                    (R ("<",
                      [Fn ("0", []);
                       Fn ("+",
                        [Fn ("*", [Fn ("-1", []); Var "a"]);
                         Fn ("+",
                          [Fn ("*", [Fn ("1", []); Var "b"]);
                           Fn ("-13", [])])])]))),
                 Or
                  (And
                    (Atom
                      (R ("divides",
                        [Fn ("20", []);
                         Fn ("+",
                          [Fn ("*", [Fn ("1", []); Var "a"]);
                           Fn ("14", [])])])),
                    Atom
                     (R ("<",
                       [Fn ("0", []);
                        Fn ("+",
                         [Fn ("*", [Fn ("-1", []); Var "a"]);
                          Fn ("+",
                           [Fn ("*", [Fn ("1", []); Var "b"]);
                            Fn ("-14", [])])])]))),
                  Or
                   (And
                     (Atom
                       (R ("divides",
                         [Fn ("20", []);
                          Fn ("+",
                           [Fn ("*", [Fn ("1", []); Var "a"]);
                            Fn ("15", [])])])),
                     Atom
                      (R ("<",
                        [Fn ("0", []);
                         Fn ("+",
                          [Fn ("*", [Fn ("-1", []); Var "a"]);
                           Fn ("+",
                            [Fn ("*", [Fn ("1", []); Var "b"]);
                             Fn ("-15", [])])])]))),
                   Or
                    (And
                      (Atom
                        (R ("divides",
                          [Fn ("20", []);
                           Fn ("+",
                            [Fn ("*", [Fn ("1", []); Var "a"]);
                             Fn ("16", [])])])),
                      Atom
                       (R ("<",
                         [Fn ("0", []);
                          Fn ("+",
                           [Fn ("*", [Fn ("-1", []); Var "a"]);
                            Fn ("+",
                             [Fn ("*", [Fn ("1", []); Var "b"]);
                              Fn ("-16", [])])])]))),
                    Or
                     (And
                       (Atom
                         (R ("divides",
                           [Fn ("20", []);
                            Fn ("+",
                             [Fn ("*", [Fn ("1", []); Var "a"]);
                              Fn ("17", [])])])),
                       Atom
                        (R ("<",
                          [Fn ("0", []);
                           Fn ("+",
                            [Fn ("*", [Fn ("-1", []); Var "a"]);
                             Fn ("+",
                              [Fn ("*", [Fn ("1", []); Var "b"]);
                               Fn ("-17", [])])])]))),
                     Or
                      (And
                        (Atom
                          (R ("divides",
                            [Fn ("20", []);
                             Fn ("+",
                              [Fn ("*", [Fn ("1", []); Var "a"]);
                               Fn ("18", [])])])),
                        Atom
                         (R ("<",
                           [Fn ("0", []);
                            Fn ("+",
                             [Fn ("*", [Fn ("-1", []); Var "a"]);
                              Fn ("+",
                               [Fn ("*", [Fn ("1", []); Var "b"]);
                                Fn ("-18", [])])])]))),
                      Or
                       (And
                         (Atom
                           (R ("divides",
                             [Fn ("20", []);
                              Fn ("+",
                               [Fn ("*", [Fn ("1", []); Var "a"]);
                                Fn ("19", [])])])),
                         Atom
                          (R ("<",
                            [Fn ("0", []);
                             Fn ("+",
                              [Fn ("*", [Fn ("-1", []); Var "a"]);
                               Fn ("+",
                                [Fn ("*", [Fn ("1", []); Var "b"]);
                                 Fn ("-19", [])])])]))),
                       And
                        (Atom
                          (R ("divides",
                            [Fn ("20", []);
                             Fn ("+",
                              [Fn ("*", [Fn ("1", []); Var "a"]);
                               Fn ("20", [])])])),
                        Atom
                         (R ("<",
                           [Fn ("0", []);
                            Fn ("+",
                             [Fn ("*", [Fn ("-1", []); Var "a"]);
                              Fn ("+",
                               [Fn ("*", [Fn ("1", []); Var "b"]);
                                Fn ("-20", [])])])]))))))))))))))))))))));
    False;
    True;
    False;
    |]

// cooper.p020
[<TestCase(@"forall a b. exists x. a < 20 * x /\ 20 * x < b", 0)>]

// cooper.p021
[<TestCase(@"exists x. a < 20 * x /\ 20 * x < b", 1)>]

// cooper.p022
[<TestCase(@"forall b. exists x. a < 20 * x /\ 20 * x < b", 2)>]

// cooper.p023
[<TestCase(@"forall a. exists b. a < 4 * b + 3 * a \/ (~(a < b) /\ a > b + 1)", 3)>]

// cooper.p024
[<TestCase(@"exists y. forall x. x + 5 * y > 1 /\ 13 * x - y > 1 /\ x + 2 < 0", 4)>]

let ``integer_qelim examples other 2`` (f, idx) =
    integer_qelim (parse f)
    |> should equal other_integer_qelim_results2.[idx]


(* ------------------------------------------------------------------------- *)
(* More of my own.                                                           *)
(* ------------------------------------------------------------------------- *)

let private other_integer_qelim_results3 : formula<fol>[] = [|
    False;
    True;
    False;
    True;
    True;
    True;
    True;
    False;
    False;
    True;
    True;
    False;
    True;
    Imp
     (Atom
       (R ("=",
         [Fn ("0", []);
          Fn ("+",
           [Fn ("*", [Fn ("-6", []); Var "x"]);
            Fn ("+", [Fn ("*", [Fn ("5", []); Var "y"]); Fn ("0", [])])])])),
     Atom
      (R ("divides",
        [Fn ("3", []);
         Fn ("+", [Fn ("*", [Fn ("1", []); Var "y"]); Fn ("0", [])])])));
    |]

// cooper.p025
[<TestCase(@"forall x y. x >= 0 /\ y >= 0
                ==> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2", 0)>]

// cooper.p026
[<TestCase(@"exists x y. 5 * x + 3 * y = 1", 1)>]

// cooper.p027
[<TestCase(@"exists x y. 5 * x + 10 * y = 1", 2)>]

// cooper.p028
[<TestCase(@"exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 6 * y = 1", 3)>]

// cooper.p029
[<TestCase(@"exists w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1", 4)>]

// cooper.p030
[<TestCase(@"exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 3 * y = 1", 5)>]

// cooper.p031
[<TestCase(@"exists x y. x >= 0 /\ y >= 0 /\ 3 * x - 5 * y = 1", 6)>]

// cooper.p032
[<TestCase(@"exists x y. x >= 0 /\ y >= 0 /\ 6 * x - 3 * y = 1", 7)>]

// cooper.p033
[<TestCase(@"forall x y. ~(x = 0) ==> 5 * y < 6 * x \/ 5 * y > 6 * x", 8)>]

// cooper.p034
[<TestCase(@"forall x y. ~divides(5,x) /\ ~divides(6,y) ==> ~(6 * x = 5 * y)", 9)>]

// cooper.p035
[<TestCase(@"forall x y. ~divides(5,x) ==> ~(6 * x = 5 * y)", 10)>]

// cooper.p036
[<TestCase(@"forall x y. ~(6 * x = 5 * y)", 11)>]

// cooper.p037
[<TestCase(@"forall x y. 6 * x = 5 * y ==> exists d. y = 3 * d", 12)>]

// cooper.p038
[<TestCase(@"6 * x = 5 * y ==> exists d. y = 3 * d", 13)>]

let ``integer_qelim examples other 3`` (f, idx) =
    integer_qelim (parse f)
    |> should equal other_integer_qelim_results3.[idx]


(* ------------------------------------------------------------------------- *)
(* Positive variant of the Bezout theorem (see the exercise).                *)
(* ------------------------------------------------------------------------- *)
let private other_integer_qelim_results4 : formula<fol>[] = [|
    True;
    False;
    True;
    |]

// cooper.p039
[<TestCase(@"forall z. z > 7 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z", 0)>]

// cooper.p040
[<TestCase(@"forall z. z > 2 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z", 1)>]

// cooper.p041
[<TestCase(@"forall z. z <= 7 ==>
                ((exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z) <=>
                ~(exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = 7 - z))", 2)>]

let ``integer_qelim examples other 4`` (f, idx) =
    integer_qelim (parse f)
    |> should equal other_integer_qelim_results4.[idx]


(* ------------------------------------------------------------------------- *)
(* Basic result about congruences.                                           *)
(* ------------------------------------------------------------------------- *)

let private other_integer_qelim_results5 : formula<fol>[] = [|
    True;
    True;
    |]

// cooper.p042
[<TestCase(@"forall x. ~divides(2,x) /\ divides(3,x-1) <=> divides(12,x-1) \/ divides(12,x-7)", 0)>]

// cooper.p043
[<TestCase(@"forall x. ~(exists m. x = 2 * m) /\ (exists m. x = 3 * m + 1) <=>
            (exists m. x = 12 * m + 1) \/ (exists m. x = 12 * m + 7)", 1)>]

let ``integer_qelim examples other 5`` (f, idx) =
    integer_qelim (parse f)
    |> should equal other_integer_qelim_results5.[idx]

(* ------------------------------------------------------------------------- *)
(* Something else.                                                           *)
(* ------------------------------------------------------------------------- *)

// cooper.p044
[<Test>]
let ``integer_qelim examples other 6``() =
    parse @"forall x. ~(divides(2,x)) ==>
            divides(4,x-1) \/
            divides(8,x-1) \/
            divides(8,x-3) \/
            divides(6,x-1) \/
            divides(14,x-1) \/
            divides(14,x-9) \/
            divides(14,x-11) \/
            divides(24,x-5) \/
            divides(24,x-11)"
    |> integer_qelim
    |> should equal formula<fol>.False

(* ------------------------------------------------------------------------- *)
(* Testing fix for an earlier version with negative result from formlcm.     *)
(* ------------------------------------------------------------------------- *)

// cooper.p045
[<Test>]
let ``integer_qelim examples other 7``() =
    parse @"a + 2 = b /\ v_3 = b - a + 1 /\ v_2 = b - 2 /\ v_1 = 3 ==> false"
    |> generalize
    |> integer_qelim
    |> should equal formula<fol>.False


(* ------------------------------------------------------------------------- *)
(* Inspired by the Collatz conjecture.                                       *)
(* ------------------------------------------------------------------------- *)

let private other_integer_qelim_results8 : formula<fol>[] = [|
    True;
    False;
    |]

// cooper.p046
[<TestCase(@"exists a b. ~(a = 1) /\ ((2 * b = a) \/
                (2 * b = 3 * a + 1)) /\ (a = b)", 0)>]

// cooper.p047
[<TestCase(@"exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)", 1)>]

let ``integer_qelim examples other 8`` (f, idx) =
    integer_qelim (parse f)
    |> should equal other_integer_qelim_results8.[idx]

(* ------------------------------------------------------------------------- *)
(* Bob Constable's "stamp problem".                                          *)
(* ------------------------------------------------------------------------- *)

let private other_integer_qelim_results9 : formula<fol>[] = [|
    True;
    True;
    True;
    |]

// cooper.p050
[<TestCase(@"forall x. x >= 8 ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v", 0)>]

// cooper.p051
[<TestCase(@"exists l.
                forall x. x >= l
                    ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v", 1)>]
// cooper.p052
[<TestCase(@"exists l.
                forall x. x >= l
                    ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 7 * v", 2)>]

let ``integer_qelim examples other 9`` (f, idx) =
    integer_qelim (parse f)
    |> should equal other_integer_qelim_results9.[idx]

