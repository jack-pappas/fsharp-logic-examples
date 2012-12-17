// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.complex

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.cooper
open FSharpx.Books.AutomatedReasoning.complex

open NUnit.Framework
open FsUnit

let private polyatomValues : (string list * string * formula<fol> * string)[] = [| 
    (
        // idx 0
        // complex.p001
        ["w"; "x"; "y"; "z"],
        @"((w + x)^4 + (w + y)^4 + (w + z)^4 +
            (x + y)^4 + (x + z)^4 + (y + z)^4 +
            (w - x)^4 + (w - y)^4 + (w - z)^4 +
            (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
            (w^2 + x^2 + y^2 + z^2)^2",
        Atom (R ("=",[Fn ("0",[]); Fn ("0",[])])),
        @"<<0 =0>>"
    );
    |]

[<TestCase(0, TestName = "complex.p001")>]

[<Test>]
let ``polyatom tests`` idx = 
    let (vars, _, _, _) = polyatomValues.[idx]
    let (_, formula, _, _) = polyatomValues.[idx]
    let (_, _, astResult, _) = polyatomValues.[idx]
    let (_, _, _, stringResult) = polyatomValues.[idx]
    let result = polyatom vars (parse formula)
    result
    |> should equal astResult
    let result1 = sprint_fol_formula result
    result1
    |> should equal stringResult

let private complex_qelimValues : (string * formula<fol> * string)[] = [| 
    (
        // idx 0
        // complex.p002
        @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 1
        // complex.p003
        @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0",
        Atom
          (R ("=",
              [Fn
                 ("+",
                  [Fn ("1",[]);
                   Fn
                     ("*",
                      [Var "c";
                       Fn
                         ("+",
                          [Fn ("-4",[]);
                           Fn
                             ("*",
                              [Var "c";
                               Fn
                                 ("+",
                                  [Fn ("6",[]);
                                   Fn
                                     ("*",
                                      [Var "c";
                                       Fn
                                         ("+",
                                          [Fn ("-4",[]);
                                           Fn ("*",[Var "c"; Fn ("1",[])])])])])])])])]);
               Fn ("0",[])])),
        @"<<1 +c *(-4 +c *(6 +c *(-4 +c *1))) =0>>"
    );
    (
        // idx 2
        // complex.p004
        @"forall c.
            (forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0)
            <=> c = 1",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 3
        // complex.p005
        @"forall a b c x y.
            a * x^2 + b * x + c = 0 /\ a * y^2 + b * y + c = 0 /\ ~(x = y)
            ==> a * x * y = c /\ a * (x + y) + b = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 4
        // complex.p012
        @"exists x. x + 2 = 3",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 5
        // complex.p013
        @"exists x. x^2 + a = 3",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 6
        // complex.p014
        @"exists x. x^2 + x + 1 = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 7
        // complex.p015
        @"exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0",
        formula<fol>.False,
        @"<<false>>"
    );
    (
        // idx 8
        // complex.p016
        @"exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 9
        // complex.p017
        @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 10
        // complex.p018
        @"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0",
        formula<fol>.False,
        @"<<false>>"
    );
    (
        // idx 11
        // complex.p019
        @"exists a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 12
        // complex.p020
        @"exists x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)",
        And
          (Or
             (Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn ("9",[]);
                            Fn
                              ("*",
                               [Var "a";
                                Fn
                                  ("+",
                                   [Fn ("0",[]);
                                    Fn
                                      ("*",
                                       [Var "a";
                                        Fn
                                          ("+",
                                           [Fn ("-10",[]);
                                            Fn
                                              ("*",
                                               [Var "a";
                                                Fn
                                                  ("+",
                                                   [Fn ("0",[]);
                                                    Fn
                                                      ("*",
                                                       [Var "a";
                                                        Fn
                                                          ("+",
                                                           [Fn ("5",[]);
                                                            Fn
                                                              ("*",
                                                               [Var "a";
                                                                Fn
                                                                  ("+",
                                                                   [Fn
                                                                      ("0",[]);
                                                                    Fn
                                                                      ("*",
                                                                       [Var
                                                                          "a";
                                                                        Fn
                                                                          ("-1",
                                                                           [])])])])])])])])])])])])]);
                        Fn ("0",[])]))),
              Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn ("0",[]);
                            Fn
                              ("*",
                               [Var "a";
                                Fn
                                  ("+",
                                   [Fn ("12",[]);
                                    Fn
                                      ("*",
                                       [Var "a";
                                        Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn
                                              ("*",
                                               [Var "a";
                                                Fn
                                                  ("+",
                                                   [Fn ("-14",[]);
                                                    Fn
                                                      ("*",
                                                       [Var "a";
                                                        Fn
                                                          ("+",
                                                           [Fn ("0",[]);
                                                            Fn
                                                              ("*",
                                                               [Var "a";
                                                                Fn
                                                                  ("+",
                                                                   [Fn
                                                                      ("6",[]);
                                                                    Fn
                                                                      ("*",
                                                                       [Var
                                                                          "a";
                                                                        Fn
                                                                          ("+",
                                                                           [Fn
                                                                              ("0",
                                                                               []);
                                                                            Fn
                                                                              ("*",
                                                                               [Var
                                                                                  "a";
                                                                                Fn
                                                                                  ("-1",
                                                                                   [])])])])])])])])])])])])])])]);
                        Fn ("0",[])])))),
           Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn ("-2",[]);
                      Fn
                        ("*",
                         [Var "a";
                          Fn
                            ("+",
                             [Fn ("0",[]); Fn ("*",[Var "a"; Fn ("1",[])])])])]);
                  Fn ("0",[])]))),
        @"<<(~9 +a *(0 +a *(-10 +a *(0 +a *(5 +a *(0 +a *-1))))) =0 \/ ~0 +a *(12 +a *(0 +a *(-14 +a *(0 +a *(6 +a *(0 +a *-1)))))) =0) /\ -2 +a *(0 +a *1) =0>>"
    );
    (
        // idx 13
        // complex.p021
        @"forall x. x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0",
        Not
          (Or
             (Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn ("9",[]);
                            Fn
                              ("*",
                               [Var "a";
                                Fn
                                  ("+",
                                   [Fn ("0",[]);
                                    Fn
                                      ("*",
                                       [Var "a";
                                        Fn
                                          ("+",
                                           [Fn ("-10",[]);
                                            Fn
                                              ("*",
                                               [Var "a";
                                                Fn
                                                  ("+",
                                                   [Fn ("0",[]);
                                                    Fn
                                                      ("*",
                                                       [Var "a";
                                                        Fn
                                                          ("+",
                                                           [Fn ("5",[]);
                                                            Fn
                                                              ("*",
                                                               [Var "a";
                                                                Fn
                                                                  ("+",
                                                                   [Fn
                                                                      ("0",[]);
                                                                    Fn
                                                                      ("*",
                                                                       [Var
                                                                          "a";
                                                                        Fn
                                                                          ("-1",
                                                                           [])])])])])])])])])])])])]);
                        Fn ("0",[])]))),
              Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn ("0",[]);
                            Fn
                              ("*",
                               [Var "a";
                                Fn
                                  ("+",
                                   [Fn ("12",[]);
                                    Fn
                                      ("*",
                                       [Var "a";
                                        Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn
                                              ("*",
                                               [Var "a";
                                                Fn
                                                  ("+",
                                                   [Fn ("-14",[]);
                                                    Fn
                                                      ("*",
                                                       [Var "a";
                                                        Fn
                                                          ("+",
                                                           [Fn ("0",[]);
                                                            Fn
                                                              ("*",
                                                               [Var "a";
                                                                Fn
                                                                  ("+",
                                                                   [Fn
                                                                      ("6",[]);
                                                                    Fn
                                                                      ("*",
                                                                       [Var
                                                                          "a";
                                                                        Fn
                                                                          ("+",
                                                                           [Fn
                                                                              ("0",
                                                                               []);
                                                                            Fn
                                                                              ("*",
                                                                               [Var
                                                                                  "a";
                                                                                Fn
                                                                                  ("-1",
                                                                                   [])])])])])])])])])])])])])])]);
                        Fn ("0",[])]))))),

        @"<<~(~9 +a *(0 +a *(-10 +a *(0 +a *(5 +a *(0 +a *-1))))) =0 \/ ~0 +a *(12 +a *(0 +a *(-14 +a *(0 +a *(6 +a *(0 +a *-1)))))) =0)>>"
    );
    (
        // idx 14
        // complex.p022
        @"forall a. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0",
        Not
          (And
             (Or
                (And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "x"; Fn ("1",[])])]);
                           Fn ("0",[])])),
                    Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("1",[]);
                               Fn
                                 ("*",
                                  [Var "x";
                                   Fn
                                     ("+",
                                      [Fn ("0",[]);
                                       Fn ("*",[Var "x"; Fn ("1",[])])])])]);
                           Fn ("0",[])]))),
                 And
                   (Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "x"; Fn ("1",[])])]);
                              Fn ("0",[])]))),
                    Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("1",[]);
                               Fn
                                 ("*",
                                  [Var "x";
                                   Fn
                                     ("+",
                                      [Fn ("0",[]);
                                       Fn
                                         ("*",
                                          [Var "x";
                                           Fn
                                             ("+",
                                              [Fn ("0",[]);
                                               Fn
                                                 ("*",
                                                  [Var "x";
                                                   Fn
                                                     ("+",
                                                      [Fn ("0",[]);
                                                       Fn
                                                         ("*",
                                                          [Var "x";
                                                           Fn ("1",[])])])])])])])])]);
                           Fn ("0",[])])))),
              Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn ("2",[]);
                            Fn
                              ("*",
                               [Var "x";
                                Fn
                                  ("+",
                                   [Fn ("0",[]);
                                    Fn
                                      ("*",
                                       [Var "x";
                                        Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn
                                              ("*",
                                               [Var "x";
                                                Fn
                                                  ("+",
                                                   [Fn ("0",[]);
                                                    Fn
                                                      ("*",
                                                       [Var "x"; Fn ("1",[])])])])])])])])]);
                        Fn ("0",[])]))))),
        @"<<~((0 +x *1 =0 /\ 1 +x *(0 +x *1) =0 \/ ~0 +x *1 =0 /\ 1 +x *(0 +x *(0 +x *(0 +x *1))) =0) /\ ~2 +x *(0 +x *(0 +x *(0 +x *1))) =0)>>"

    );
    (
        // idx 15
        // complex.p023
        @"exists a b c x y.
            a * x^2 + b * x + c = 0 /\ 
            a * y^2 + b * y + c = 0 /\ 
            ~(x = y) /\ 
            ~(a * x * y = c)",
        formula<fol>.False,
        @"<<false>>"
    );
    (
        // idx 16
        // complex.p024
        @"forall a b c x y.
            ~(a = 0) /\ 
            (forall z. a * z^2 + b * z + c = 0 <=> z = x) /\ x = y
            ==> a * x * y = c /\ a * (x + y) + b = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 17
        // complex.p025
        @"forall a b c x y.
          (forall z. a * z^2 + b * z + c = 0 <=> z = x \/ z = y)
          ==> a * x * y = c /\ a * (x + y) + b = 0",
        formula<fol>.False,
        @""
    );
    (
        // idx 18
        // complex.p026
        @"forall a b c x.
            (forall z. a * z^2 + b * z + c = 0 <=> z = x)
            ==> a * x * x = c /\ a * (x + x) + b = 0",
        formula<fol>.False,
        @"<<false>>"
    );
    (
        // idx 19
        // complex.p027
        @"forall x y.
            (forall a b c. (a * x^2 + b * x + c = 0) /\ 
                    (a * y^2 + b * y + c = 0)
                    ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
            <=> ~(x = y)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 20
        // complex.p028
        @"forall y_1 y_2 y_3 y_4.
            (y_1 = 2 * y_3) /\ 
            (y_2 = 2 * y_4) /\ 
            (y_1 * y_3 = y_2 * y_4)
            ==> (y_1^2 = y_2^2)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 21
        // complex.p029
        @"forall x y. x^2 = 2 /\ y^2 = 3
            ==> (x * y)^2 = 6",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 22
        // complex.p030
        @"forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
            ==> (x^4 + 1 = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 23
        // complex.p031
        @"forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
            ==> (x^4 + 1 = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 24
        // complex.p032
        @"~(exists a x y. (a^2 = 2) /\ 
                (x^2 + a * x + 1 = 0) /\ 
                (y * (x^4 + 1) + 1 = 0))",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 25
        // complex.p033
        @"forall x. exists y. x^2 = y^3",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 26
        // complex.p034
        @"forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
                2 * (b * x + b * z - a * y)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 27
        // complex.p035
        @"forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 28
        // complex.p036
        @"forall a b c x y. (a * x^2 + b * x + c = 0) /\ 
                (a * y^2 + b * y + c = 0) /\ 
                ~(x = y)
                ==> (a * x * y = c) /\ (a * (x + y) + b = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 29
        // complex.p037
        @"~(forall a b c x y. (a * x^2 + b * x + c = 0) /\ 
                    (a * y^2 + b * y + c = 0)
                    ==> (a * x * y = c) /\ (a * (x + y) + b = 0))",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 30
        // complex.p038
        @"forall y_1 y_2 y_3 y_4.
            (y_1 = 2 * y_3) /\ 
            (y_2 = 2 * y_4) /\ 
            (y_1 * y_3 = y_2 * y_4)
            ==> (y_1^2 = y_2^2)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 31
        // complex.p039
        @"forall a1 b1 c1 a2 b2 c2.
            ~(a1 * b2 = a2 * b1)
            ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 32
        // complex.p040
        @"(a * x^2 + b * x + c = 0) /\ 
            (a * y^2 + b * y + c = 0) /\ 
            (forall z. (a * z^2 + b * z + c = 0)
                ==> (z = x) \/ (z = y))
            ==> (a * x * y = c) /\ (a * (x + y) + b = 0)",
        Imp
          (And
             (Atom
                (R ("=",
                    [Fn
                       ("+",
                        [Fn
                           ("+",
                            [Fn
                               ("+",
                                [Fn ("0",[]); Fn ("*",[Var "c"; Fn ("1",[])])]);
                             Fn
                               ("*",
                                [Var "b";
                                 Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "x"; Fn ("1",[])])])])]);
                         Fn
                           ("*",
                            [Var "a";
                             Fn
                               ("+",
                                [Fn ("0",[]);
                                 Fn
                                   ("*",
                                    [Var "x";
                                     Fn
                                       ("+",
                                        [Fn ("0",[]);
                                         Fn ("*",[Var "x"; Fn ("1",[])])])])])])]);
                     Fn ("0",[])])),
              And
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn
                              ("+",
                               [Fn
                                  ("+",
                                   [Fn ("0",[]);
                                    Fn ("*",[Var "c"; Fn ("1",[])])]);
                                Fn
                                  ("*",
                                   [Var "b";
                                    Fn
                                      ("+",
                                       [Fn ("0",[]);
                                        Fn ("*",[Var "y"; Fn ("1",[])])])])]);
                            Fn
                              ("*",
                               [Var "a";
                                Fn
                                  ("+",
                                   [Fn ("0",[]);
                                    Fn
                                      ("*",
                                       [Var "y";
                                        Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn ("*",[Var "y"; Fn ("1",[])])])])])])]);
                        Fn ("0",[])])),
                 Not
                   (Or
                      (And
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "a"; Fn ("1",[])])]);
                                 Fn ("0",[])])),
                          Or
                            (And
                               (Atom
                                  (R ("=",
                                      [Fn
                                         ("+",
                                          [Fn ("0",[]);
                                           Fn ("*",[Var "b"; Fn ("1",[])])]);
                                       Fn ("0",[])])),
                                Atom
                                  (R ("=",
                                      [Fn
                                         ("+",
                                          [Fn ("0",[]);
                                           Fn ("*",[Var "c"; Fn ("1",[])])]);
                                       Fn ("0",[])]))),
                             And
                               (Not
                                  (Atom
                                     (R ("=",
                                         [Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn ("*",[Var "b"; Fn ("1",[])])]);
                                          Fn ("0",[])]))),
                                Not
                                  (Atom
                                     (R ("=",
                                         [Fn
                                            ("+",
                                             [Fn
                                                ("+",
                                                 [Fn ("0",[]);
                                                  Fn
                                                    ("*",
                                                     [Var "c";
                                                      Fn
                                                        ("+",
                                                         [Fn ("0",[]);
                                                          Fn
                                                            ("*",
                                                             [Var "c";
                                                              Fn ("1",[])])])])]);
                                              Fn
                                                ("*",
                                                 [Var "b";
                                                  Fn
                                                    ("+",
                                                     [Fn
                                                        ("+",
                                                         [Fn ("0",[]);
                                                          Fn
                                                            ("*",
                                                             [Var "c";
                                                              Fn
                                                                ("+",
                                                                 [Fn
                                                                    ("+",
                                                                     [Fn
                                                                        ("0",
                                                                         []);
                                                                      Fn
                                                                        ("*",
                                                                         [Var
                                                                            "y";
                                                                          Fn
                                                                            ("1",
                                                                             [])])]);
                                                                  Fn
                                                                    ("*",
                                                                     [Var "x";
                                                                      Fn
                                                                        ("1",
                                                                         [])])])])]);
                                                      Fn
                                                        ("*",
                                                         [Var "b";
                                                          Fn
                                                            ("+",
                                                             [Fn ("0",[]);
                                                              Fn
                                                                ("*",
                                                                 [Var "x";
                                                                  Fn
                                                                    ("+",
                                                                     [Fn
                                                                        ("0",
                                                                         []);
                                                                      Fn
                                                                        ("*",
                                                                         [Var
                                                                            "y";
                                                                          Fn
                                                                            ("1",
                                                                             [])])])])])])])])]);
                                          Fn ("0",[])])))))),
                       And
                         (Not
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn ("0",[]);
                                        Fn ("*",[Var "a"; Fn ("1",[])])]);
                                    Fn ("0",[])]))),
                          Or
                            (Not
                               (Atom
                                  (R ("=",
                                      [Fn
                                         ("+",
                                          [Fn
                                             ("+",
                                              [Fn ("0",[]);
                                               Fn
                                                 ("*",
                                                  [Var "b";
                                                   Fn
                                                     ("+",
                                                      [Fn ("0",[]);
                                                       Fn
                                                         ("*",
                                                          [Var "b";
                                                           Fn
                                                             ("+",
                                                              [Fn ("0",[]);
                                                               Fn
                                                                 ("*",
                                                                  [Var "c";
                                                                   Fn
                                                                     ("-1",[])])])])])])]);
                                           Fn
                                             ("*",
                                              [Var "a";
                                               Fn
                                                 ("+",
                                                  [Fn
                                                     ("+",
                                                      [Fn
                                                         ("+",
                                                          [Fn ("0",[]);
                                                           Fn
                                                             ("*",
                                                              [Var "c";
                                                               Fn
                                                                 ("+",
                                                                  [Fn ("0",[]);
                                                                   Fn
                                                                     ("*",
                                                                      [Var "c";
                                                                       Fn
                                                                         ("1",
                                                                          [])])])])]);
                                                       Fn
                                                         ("*",
                                                          [Var "b";
                                                           Fn
                                                             ("+",
                                                              [Fn ("0",[]);
                                                               Fn
                                                                 ("*",
                                                                  [Var "c";
                                                                   Fn
                                                                     ("+",
                                                                      [Fn
                                                                         ("+",
                                                                          [Fn
                                                                             ("0",
                                                                              []);
                                                                           Fn
                                                                             ("*",
                                                                              [Var
                                                                                 "y";
                                                                               Fn
                                                                                 ("-2",
                                                                                  [])])]);
                                                                       Fn
                                                                         ("*",
                                                                          [Var
                                                                             "x";
                                                                           Fn
                                                                             ("-2",
                                                                              [])])])])])])]);
                                                   Fn
                                                     ("*",
                                                      [Var "a";
                                                       Fn
                                                         ("+",
                                                          [Fn
                                                             ("+",
                                                              [Fn ("0",[]);
                                                               Fn
                                                                 ("*",
                                                                  [Var "c";
                                                                   Fn
                                                                     ("+",
                                                                      [Fn
                                                                         ("+",
                                                                          [Fn
                                                                             ("0",
                                                                              []);
                                                                           Fn
                                                                             ("*",
                                                                              [Var
                                                                                 "y";
                                                                               Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("0",
                                                                                      []);
                                                                                   Fn
                                                                                     ("*",
                                                                                      [Var
                                                                                         "y";
                                                                                       Fn
                                                                                         ("-1",
                                                                                          [])])])])]);
                                                                       Fn
                                                                         ("*",
                                                                          [Var
                                                                             "x";
                                                                           Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("0",
                                                                                      []);
                                                                                   Fn
                                                                                     ("*",
                                                                                      [Var
                                                                                         "y";
                                                                                       Fn
                                                                                         ("-4",
                                                                                          [])])]);
                                                                               Fn
                                                                                 ("*",
                                                                                  [Var
                                                                                     "x";
                                                                                   Fn
                                                                                     ("-1",
                                                                                      [])])])])])])]);
                                                           Fn
                                                             ("*",
                                                              [Var "a";
                                                               Fn
                                                                 ("+",
                                                                  [Fn ("0",[]);
                                                                   Fn
                                                                     ("*",
                                                                      [Var "x";
                                                                       Fn
                                                                         ("+",
                                                                          [Fn
                                                                             ("0",
                                                                              []);
                                                                           Fn
                                                                             ("*",
                                                                              [Var
                                                                                 "x";
                                                                               Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("0",
                                                                                      []);
                                                                                   Fn
                                                                                     ("*",
                                                                                      [Var
                                                                                         "y";
                                                                                       Fn
                                                                                         ("+",
                                                                                          [Fn
                                                                                             ("0",
                                                                                              []);
                                                                                           Fn
                                                                                             ("*",
                                                                                              [Var
                                                                                                 "y";
                                                                                               Fn
                                                                                                 ("1",
                                                                                                  [])])])])])])])])])])])])])])]);
                                       Fn ("0",[])]))),
                             Not
                               (Atom
                                  (R ("=",
                                      [Fn
                                         ("+",
                                          [Fn
                                             ("+",
                                              [Fn ("0",[]);
                                               Fn
                                                 ("*",
                                                  [Var "b";
                                                   Fn
                                                     ("+",
                                                      [Fn ("0",[]);
                                                       Fn
                                                         ("*",
                                                          [Var "b";
                                                           Fn
                                                             ("+",
                                                              [Fn ("0",[]);
                                                               Fn
                                                                 ("*",
                                                                  [Var "b";
                                                                   Fn
                                                                     ("-1",[])])])])])])]);
                                           Fn
                                             ("*",
                                              [Var "a";
                                               Fn
                                                 ("+",
                                                  [Fn
                                                     ("+",
                                                      [Fn ("0",[]);
                                                       Fn
                                                         ("*",
                                                          [Var "b";
                                                           Fn
                                                             ("+",
                                                              [Fn
                                                                 ("+",
                                                                  [Fn ("0",[]);
                                                                   Fn
                                                                     ("*",
                                                                      [Var "c";
                                                                       Fn
                                                                         ("2",
                                                                          [])])]);
                                                               Fn
                                                                 ("*",
                                                                  [Var "b";
                                                                   Fn
                                                                     ("+",
                                                                      [Fn
                                                                         ("+",
                                                                          [Fn
                                                                             ("0",
                                                                              []);
                                                                           Fn
                                                                             ("*",
                                                                              [Var
                                                                                 "y";
                                                                               Fn
                                                                                 ("-2",
                                                                                  [])])]);
                                                                       Fn
                                                                         ("*",
                                                                          [Var
                                                                             "x";
                                                                           Fn
                                                                             ("-2",
                                                                              [])])])])])])]);
                                                   Fn
                                                     ("*",
                                                      [Var "a";
                                                       Fn
                                                         ("+",
                                                          [Fn
                                                             ("+",
                                                              [Fn
                                                                 ("+",
                                                                  [Fn ("0",[]);
                                                                   Fn
                                                                     ("*",
                                                                      [Var "c";
                                                                       Fn
                                                                         ("+",
                                                                          [Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("0",
                                                                                  []);
                                                                               Fn
                                                                                 ("*",
                                                                                  [Var
                                                                                     "y";
                                                                                   Fn
                                                                                     ("2",
                                                                                      [])])]);
                                                                           Fn
                                                                             ("*",
                                                                              [Var
                                                                                 "x";
                                                                               Fn
                                                                                 ("2",
                                                                                  [])])])])]);
                                                               Fn
                                                                 ("*",
                                                                  [Var "b";
                                                                   Fn
                                                                     ("+",
                                                                      [Fn
                                                                         ("+",
                                                                          [Fn
                                                                             ("0",
                                                                              []);
                                                                           Fn
                                                                             ("*",
                                                                              [Var
                                                                                 "y";
                                                                               Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("0",
                                                                                      []);
                                                                                   Fn
                                                                                     ("*",
                                                                                      [Var
                                                                                         "y";
                                                                                       Fn
                                                                                         ("-1",
                                                                                          [])])])])]);
                                                                       Fn
                                                                         ("*",
                                                                          [Var
                                                                             "x";
                                                                           Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("0",
                                                                                      []);
                                                                                   Fn
                                                                                     ("*",
                                                                                      [Var
                                                                                         "y";
                                                                                       Fn
                                                                                         ("-4",
                                                                                          [])])]);
                                                                               Fn
                                                                                 ("*",
                                                                                  [Var
                                                                                     "x";
                                                                                   Fn
                                                                                     ("-1",
                                                                                      [])])])])])])]);
                                                           Fn
                                                             ("*",
                                                              [Var "a";
                                                               Fn
                                                                 ("+",
                                                                  [Fn ("0",[]);
                                                                   Fn
                                                                     ("*",
                                                                      [Var "x";
                                                                       Fn
                                                                         ("+",
                                                                          [Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("0",
                                                                                  []);
                                                                               Fn
                                                                                 ("*",
                                                                                  [Var
                                                                                     "y";
                                                                                   Fn
                                                                                     ("+",
                                                                                      [Fn
                                                                                         ("0",
                                                                                          []);
                                                                                       Fn
                                                                                         ("*",
                                                                                          [Var
                                                                                             "y";
                                                                                           Fn
                                                                                             ("-2",
                                                                                              [])])])])]);
                                                                           Fn
                                                                             ("*",
                                                                              [Var
                                                                                 "x";
                                                                               Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("0",
                                                                                      []);
                                                                                   Fn
                                                                                     ("*",
                                                                                      [Var
                                                                                         "y";
                                                                                       Fn
                                                                                         ("-2",
                                                                                          [])])])])])])])])])])])])]);
                                       Fn ("0",[])]))))))))),
           And
             (Atom
                (R ("=",
                    [Fn
                       ("+",
                        [Fn
                           ("+",
                            [Fn ("0",[]); Fn ("*",[Var "c"; Fn ("-1",[])])]);
                         Fn
                           ("*",
                            [Var "a";
                             Fn
                               ("+",
                                [Fn ("0",[]);
                                 Fn
                                   ("*",
                                    [Var "x";
                                     Fn
                                       ("+",
                                        [Fn ("0",[]);
                                         Fn ("*",[Var "y"; Fn ("1",[])])])])])])]);
                     Fn ("0",[])])),
              Atom
                (R ("=",
                    [Fn
                       ("+",
                        [Fn
                           ("+",[Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                         Fn
                           ("*",
                            [Var "a";
                             Fn
                               ("+",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "y"; Fn ("1",[])])]);
                                 Fn ("*",[Var "x"; Fn ("1",[])])])])]);
                     Fn ("0",[])])))),
        @"<<((0 +c *1) +b *(0 +x *1)) +a *(0 +x *(0 +x *1)) =0 /\ ((0 +c *1) +b *(0 +y *1)) +a *(0 +y *(0 +y *1)) =0 /\ ~(0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 \/ ~0 +b *1 =0 /\ ~(0 +c *(0 +c *1)) +b *((0 +c *((0 +y *1) +x *1)) +b *(0 +x *(0 +y *1))) =0) \/ ~0 +a *1 =0 /\ (~(0 +b *(0 +b *(0 +c *-1))) +a *(((0 +c *(0 +c *1)) +b *(0 +c *((0 +y *-2) +x *-2))) +a *((0 +c *((0 +y *(0 +y *-1)) +x *((0 +y *-4) +x *-1))) +a *(0 +x *(0 +x *(0 +y *(0 +y *1)))))) =0 \/ ~(0 +b *(0 +b *(0 +b *-1))) +a *((0 +b *((0 +c *2) +b *((0 +y *-2) +x *-2))) +a *(((0 +c *((0 +y *2) +x *2)) +b *((0 +y *(0 +y *-1)) +x *((0 +y *-4) +x *-1))) +a *(0 +x *((0 +y *(0 +y *-2)) +x *(0 +y *-2))))) =0)) ==> (0 +c *-1) +a *(0 +x *(0 +y *1)) =0 /\ (0 +b *1) +a *((0 +y *1) +x *1) =0>>"
    );
    (
        // idx 33
        // complex.p041
        @"forall y. (a * x^2 + b * x + c = 0) /\ 
            (a * y^2 + b * y + c = 0) /\ 
            (forall z. (a * z^2 + b * z + c = 0)
                        ==> (z = x) \/ (z = y))
            ==> (a * x * y = c) /\ (a * (x + y) + b = 0)",
        formula<fol>.False,  // Dummy value used as place holder
        @"<<~((~0 +a *1 =0 /\ (0 +a *(0 +a *((0 +b *-1) +a *(0 +x *-2))) =0 /\ (0 +a *((0 +b *(0 +b *-2)) +a *(((0 +c *2) +b *(0 +x *-4)) +a *(0 +x *(0 +x *-2)))) =0 /\ (0 +b *(0 +b *(0 +b *-1))) +a *((0 +b *((0 +c *2) +b *(0 +x *-2))) +a *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *-1)))) =0 /\ (0 +a *(0 +a *((0 +c *-1) +a *(0 +x *(0 +x *1)))) =0 /\ (0 +a *((0 +b *(0 +c *-2)) +a *(0 +c *(0 +x *-4))) =0 /\ (0 +b *(0 +b *(0 +c *-1))) +a *(((0 +c *(0 +c *1)) +b *(0 +c *(0 +x *-2))) +a *(0 +c *(0 +x *(0 +x *-1)))) =0 /\ (0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~0 +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *(0 +c *-1)) +a *(0 +c *(0 +x *-1)) =0) \/ ~0 +a *1 =0 /\ (~0 +a *((0 +c *(0 +c *1)) +a *(0 +c *(0 +x *(0 +x *-1)))) =0 \/ ~0 +a *(0 +a *((0 +c *(0 +x *-2)) +b *(0 +x *(0 +x *-1)))) =0)) \/ ~0 +a *((0 +b *(0 +c *-2)) +a *(0 +c *(0 +x *-4))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +b *(0 +b *(0 +c *(0 +c *-1)))))) +a *((0 +b *(0 +b *((0 +c *(0 +c *(0 +c *4))) +b *(0 +c *(0 +c *(0 +x *-4)))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *16)))) +b *(0 +c *(0 +c *(0 +x *(0 +x *-4)))))) +a *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *14))))) +a *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))))) =0 /\ ~0 +a *((0 +b *((0 +c *(0 +c *2)) +b *(0 +c *(0 +x *1)))) +a *(((0 +c *(0 +c *(0 +x *3))) +b *(0 +c *(0 +x *(0 +x *2)))) +a *(0 +c *(0 +x *(0 +x *(0 +x *1)))))) =0) \/ ~0 +a *(0 +a *((0 +c *-1) +a *(0 +x *(0 +x *1)))) =0 /\ (0 +a *(0 +a *((0 +b *(0 +c *1)) +a *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *1))))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +c *1))) +a *(((0 +c *(0 +c *-2)) +b *(0 +c *(0 +x *2))) +a *(0 +c *(0 +x *(0 +x *2))))) =0 /\ (~0 +a *(0 +a *(((0 +c *(0 +c *(0 +c *-1))) +b *(0 +b *(0 +c *(0 +x *(0 +x *1))))) +a *((0 +b *(0 +c *(0 +x *(0 +x *(0 +x *2))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))) =0 \/ ~0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *(0 +x *2))) +b *(0 +c *(0 +x *(0 +x *2)))) +a *(0 +c *(0 +x *(0 +x *(0 +x *2))))))) =0) \/ ~0 +a *(0 +a *((0 +b *(0 +c *1)) +a *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *1))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *((0 +c *(0 +c *(0 +c *(0 +c *1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *2)))) +b *(0 +c *(0 +c *(0 +x *(0 +x *1)))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +c *-4))))) +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *-8))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *-3))))) +b *(0 +b *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-1))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *(0 +x *-4)))))) +b *(0 +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *3)))))) +b *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-2))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *4))))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *8))))))) +b *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-1))))))))) +a *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *4)))))))))))))))) =0 /\ ~0 +a *(0 +a *((0 +b *((0 +c *(0 +c *-1)) +b *(0 +c *(0 +x *-1)))) +a *(((0 +c *(0 +c *(0 +x *-2))) +b *(0 +c *(0 +x *(0 +x *-3)))) +a *(0 +c *(0 +x *(0 +x *(0 +x *-2))))))) =0)) \/ ~0 +a *((0 +b *(0 +b *-2)) +a *(((0 +c *2) +b *(0 +x *-4)) +a *(0 +x *(0 +x *-2)))) =0 /\ 0 +a *(0 +a *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +c *-1))))))) +a *((0 +b *(0 +b *(0 +b *(0 +b *((0 +c *(0 +c *4)) +b *((0 +c *(0 +x *-4)) +b *(0 +x *(0 +x *1)))))))) +a *((0 +b *(0 +b *((0 +c *(0 +c *(0 +c *-8))) +b *((0 +c *(0 +c *(0 +x *4))) +b *((0 +c *(0 +x *(0 +x *-14))) +b *(0 +x *(0 +x *(0 +x *4)))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *4)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *-8)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-4)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-32)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *6)))))))) +a *((0 +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-4))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-37))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *4)))))))) +a *((0 +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-20)))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-4)))))))))))))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-1)))))) +a *((0 +b *(0 +b *(0 +b *(0 +b *((0 +c *6) +b *(0 +x *-4)))))) +a *((0 +b *(0 +b *((0 +c *(0 +c *-8)) +b *((0 +c *(0 +x *20)) +b *(0 +x *(0 +x *-6)))))) +a *(((0 +c *(0 +c *(0 +c *4))) +b *((0 +c *(0 +c *(0 +x *-12))) +b *((0 +c *(0 +x *(0 +x *26))) +b *(0 +x *(0 +x *(0 +x *-4)))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *-4)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *16)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *-1)))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *4)))))))))) =0 /\ ~0 +a *((0 +b *(0 +b *((0 +c *2) +b *(0 +x *1)))) +a *(((0 +c *(0 +c *-2)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *2)))) +a *(0 +b *(0 +x *(0 +x *(0 +x *1)))))) =0) \/ ~0 +a *(0 +a *((0 +b *-1) +a *(0 +x *-2))) =0 /\ (0 +a *(0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *2)) +b *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *2)))) +a *(((0 +c *(0 +x *(0 +x *4))) +b *(0 +x *(0 +x *(0 +x *4)))) +a *(0 +x *(0 +x *(0 +x *(0 +x *2))))))))) =0 /\ 0 +a *(0 +a *(0 +a *((0 +b *((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1))))) +a *((0 +b *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *2))))) +a *(0 +b *(0 +x *(0 +x *(0 +x *(0 +x *1))))))))) =0 /\ (0 +a *(0 +a *((0 +b *(0 +b *1)) +a *(((0 +c *-2) +b *(0 +x *2)) +a *(0 +x *(0 +x *2))))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +b *1))) +a *((0 +b *((0 +c *-3) +b *(0 +x *2))) +a *((0 +c *(0 +x *-4)) +b *(0 +x *(0 +x *1))))) =0 /\ (~0 +a *(0 +a *((0 +b *((0 +c *(0 +c *-1)) +b *(0 +b *(0 +x *(0 +x *1))))) +a *(((0 +c *(0 +c *(0 +x *-2))) +b *((0 +c *(0 +x *(0 +x *-2))) +b *(0 +x *(0 +x *(0 +x *2))))) +a *((0 +c *(0 +x *(0 +x *(0 +x *-2)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))) =0 \/ ~0 +a *(0 +a *(0 +a *((0 +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *2)))) +a *(((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *4)))) +a *(0 +x *(0 +x *(0 +x *(0 +x *2)))))))) =0) \/ ~0 +a *(0 +a *((0 +b *(0 +b *1)) +a *(((0 +c *-2) +b *(0 +x *2)) +a *(0 +x *(0 +x *2))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *(0 +b *((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1))))))) +a *((0 +b *((0 +c *(0 +c *(0 +c *-4))) +b *((0 +c *(0 +c *(0 +x *-6))) +b *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *4))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *-8)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-24)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-12)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *5))))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-16))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-20))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *2))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-8))))))))))))))) =0 /\ ~0 +a *(0 +a *((0 +b *(0 +b *((0 +c *-1) +b *(0 +x *-1)))) +a *(((0 +c *(0 +c *2)) +b *((0 +c *(0 +x *1)) +b *(0 +x *(0 +x *-2)))) +a *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *-1))))))) =0) \/ ~0 +a *(0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *2)) +b *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *2)))) +a *(((0 +c *(0 +x *(0 +x *4))) +b *(0 +x *(0 +x *(0 +x *4)))) +a *(0 +x *(0 +x *(0 +x *(0 +x *2))))))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *(0 +b *((0 +c *(0 +c *(0 +c *(0 +c *-1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *-4)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-6)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-4)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *-1))))))))))) +a *((0 +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +c *4))))) +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *14))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *12))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-8))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-16))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-6))))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +c *(0 +x *8)))))) +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *(0 +x *48)))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *88)))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *50)))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-12)))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-14))))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *32))))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *120))))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *132))))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *28))))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-16))))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *48)))))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *112)))))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *56)))))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-9))))))))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *32))))))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *36))))))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-2))))))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *8))))))))))))))))))))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *(0 +b *((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1))))))) +a *((0 +b *((0 +c *(0 +c *(0 +c *-4))) +b *((0 +c *(0 +c *(0 +x *-6))) +b *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *4))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *-8)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-24)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-12)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *5))))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-16))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-20))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *2))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-8)))))))))))))) =0 /\ ~0 +a *(0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *(0 +c *-2))) +b *((0 +c *(0 +c *(0 +x *-5))) +b *((0 +c *(0 +x *(0 +x *-4))) +b *(0 +x *(0 +x *(0 +x *-1)))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *-4)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-6)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *-2)))))) +a *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-2))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-1))))))))))) =0)) \/ 0 +a *1 =0 /\ ~0 +b *1 =0 /\ (0 +b *((0 +c *1) +b *(0 +x *1)) =0 /\ (0 +c *(0 +c *1)) +b *(0 +c *(0 +x *1)) =0 /\ (0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~0 +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *(0 +c *-1)) +a *(0 +c *(0 +x *-1)) =0) \/ ~0 +a *1 =0 /\ (~0 +a *((0 +c *(0 +c *1)) +a *(0 +c *(0 +x *(0 +x *-1)))) =0 \/ ~0 +a *(0 +a *((0 +c *(0 +x *-2)) +b *(0 +x *(0 +x *-1)))) =0)) \/ ~0 +b *((0 +c *1) +b *(0 +x *1)) =0 /\ 0 +a *((0 +c *(0 +c *(0 +c *(0 +c *1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *2)))) +b *(0 +c *(0 +c *(0 +x *(0 +x *1)))))) =0 /\ ~(0 +b *((0 +c *(0 +c *-1)) +b *(0 +c *(0 +x *-1)))) +a *((0 +c *(0 +c *(0 +x *-1))) +b *(0 +c *(0 +x *(0 +x *-1)))) =0) \/ 0 +a *1 =0 /\ 0 +b *1 =0 /\ ~0 +c *1 =0 /\ (0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~0 +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *(0 +c *-1)) +a *(0 +c *(0 +x *-1)) =0) \/ ~0 +a *1 =0 /\ (~0 +a *((0 +c *(0 +c *1)) +a *(0 +c *(0 +x *(0 +x *-1)))) =0 \/ ~0 +a *(0 +a *((0 +c *(0 +x *-2)) +b *(0 +x *(0 +x *-1)))) =0))) /\ ((0 +c *1) +b *(0 +x *1)) +a *(0 +x *(0 +x *1)) =0 \/ (~0 +a *1 =0 /\ (0 +a *(0 +a *((0 +b *-1) +a *(0 +x *-2))) =0 /\ (0 +a *((0 +b *(0 +b *-2)) +a *(((0 +c *2) +b *(0 +x *-4)) +a *(0 +x *(0 +x *-2)))) =0 /\ (0 +b *(0 +b *(0 +b *-1))) +a *((0 +b *((0 +c *2) +b *(0 +x *-2))) +a *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *-1)))) =0 /\ (0 +a *(0 +a *((0 +c *-1) +a *(0 +x *(0 +x *1)))) =0 /\ (0 +a *((0 +b *(0 +c *-2)) +a *(0 +c *(0 +x *-4))) =0 /\ (0 +b *(0 +b *(0 +c *-1))) +a *(((0 +c *(0 +c *1)) +b *(0 +c *(0 +x *-2))) +a *(0 +c *(0 +x *(0 +x *-1)))) =0 /\ 0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~(0 +b *1) +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *(0 +b *1)) +a *((0 +c *-1) +b *(0 +x *1)) =0) \/ ~0 +a *((0 +b *(0 +c *-2)) +a *(0 +c *(0 +x *-4))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +b *(0 +b *(0 +c *(0 +c *-1)))))) +a *((0 +b *(0 +b *((0 +c *(0 +c *(0 +c *4))) +b *(0 +c *(0 +c *(0 +x *-4)))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *16)))) +b *(0 +c *(0 +c *(0 +x *(0 +x *-4)))))) +a *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *14))))) +a *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))))) =0 /\ ~0 +a *((0 +b *(0 +b *(0 +c *-1))) +a *(((0 +c *(0 +c *-1)) +b *(0 +c *(0 +x *-4))) +a *(0 +c *(0 +x *(0 +x *-3))))) =0) \/ ~0 +a *(0 +a *((0 +c *-1) +a *(0 +x *(0 +x *1)))) =0 /\ (0 +a *(0 +a *((0 +b *(0 +c *1)) +a *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *1))))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +c *1))) +a *(((0 +c *(0 +c *-2)) +b *(0 +c *(0 +x *2))) +a *(0 +c *(0 +x *(0 +x *2))))) =0 /\ (~0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *-1)) +b *(0 +b *(0 +x *(0 +x *1)))) +a *((0 +b *(0 +x *(0 +x *(0 +x *2)))) +a *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))) =0 \/ ~0 +a *(0 +a *(0 +a *(0 +a *(((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *2))) +a *(0 +x *(0 +x *(0 +x *2))))))) =0) \/ ~0 +a *(0 +a *((0 +b *(0 +c *1)) +a *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *1))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *((0 +c *(0 +c *(0 +c *(0 +c *1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *2)))) +b *(0 +c *(0 +c *(0 +x *(0 +x *1)))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +c *-4))))) +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *-8))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *-3))))) +b *(0 +b *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-1))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *(0 +x *-4)))))) +b *(0 +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *3)))))) +b *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-2))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *4))))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *8))))))) +b *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-1))))))))) +a *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *4)))))))))))))))) =0 /\ ~0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *2)) +b *((0 +c *(0 +x *3)) +b *(0 +x *(0 +x *1)))) +a *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *1))))))) =0)) \/ ~0 +a *((0 +b *(0 +b *-2)) +a *(((0 +c *2) +b *(0 +x *-4)) +a *(0 +x *(0 +x *-2)))) =0 /\ 0 +a *(0 +a *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +c *-1))))))) +a *((0 +b *(0 +b *(0 +b *(0 +b *((0 +c *(0 +c *4)) +b *((0 +c *(0 +x *-4)) +b *(0 +x *(0 +x *1)))))))) +a *((0 +b *(0 +b *((0 +c *(0 +c *(0 +c *-8))) +b *((0 +c *(0 +c *(0 +x *4))) +b *((0 +c *(0 +x *(0 +x *-14))) +b *(0 +x *(0 +x *(0 +x *4)))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *4)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *-8)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-4)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-32)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *6)))))))) +a *((0 +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-4))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-37))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *4)))))))) +a *((0 +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-20)))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-4)))))))))))))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-1)))))) +a *((0 +b *(0 +b *(0 +b *(0 +b *((0 +c *6) +b *(0 +x *-4)))))) +a *((0 +b *(0 +b *((0 +c *(0 +c *-8)) +b *((0 +c *(0 +x *20)) +b *(0 +x *(0 +x *-6)))))) +a *(((0 +c *(0 +c *(0 +c *4))) +b *((0 +c *(0 +c *(0 +x *-12))) +b *((0 +c *(0 +x *(0 +x *26))) +b *(0 +x *(0 +x *(0 +x *-4)))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *-4)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *16)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *-1)))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *4)))))))))) =0 /\ ~0 +a *((0 +b *(0 +b *(0 +b *-1))) +a *((0 +b *(0 +b *(0 +x *-4))) +a *((0 +b *(0 +x *(0 +x *-5))) +a *(0 +x *(0 +x *(0 +x *-2)))))) =0) \/ ~0 +a *(0 +a *((0 +b *-1) +a *(0 +x *-2))) =0 /\ (0 +a *(0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *2)) +b *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *2)))) +a *(((0 +c *(0 +x *(0 +x *4))) +b *(0 +x *(0 +x *(0 +x *4)))) +a *(0 +x *(0 +x *(0 +x *(0 +x *2))))))))) =0 /\ 0 +a *(0 +a *(0 +a *((0 +b *((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1))))) +a *((0 +b *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *2))))) +a *(0 +b *(0 +x *(0 +x *(0 +x *(0 +x *1))))))))) =0 /\ (0 +a *(0 +a *((0 +b *(0 +b *1)) +a *(((0 +c *-2) +b *(0 +x *2)) +a *(0 +x *(0 +x *2))))) =0 /\ 0 +a *((0 +b *(0 +b *(0 +b *1))) +a *((0 +b *((0 +c *-3) +b *(0 +x *2))) +a *((0 +c *(0 +x *-4)) +b *(0 +x *(0 +x *1))))) =0 /\ (~0 +a *(0 +a *(0 +a *((0 +b *((0 +c *-2) +b *(0 +x *-2))) +a *(((0 +c *(0 +x *-2)) +b *(0 +x *(0 +x *-4))) +a *(0 +x *(0 +x *(0 +x *-2))))))) =0 \/ ~0 +a *(0 +a *(0 +a *(0 +a *(((0 +c *-2) +b *(0 +x *-2)) +a *(0 +x *(0 +x *-2)))))) =0) \/ ~0 +a *(0 +a *((0 +b *(0 +b *1)) +a *(((0 +c *-2) +b *(0 +x *2)) +a *(0 +x *(0 +x *2))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *(0 +b *((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1))))))) +a *((0 +b *((0 +c *(0 +c *(0 +c *-4))) +b *((0 +c *(0 +c *(0 +x *-6))) +b *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *4))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *-8)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-24)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-12)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *5))))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-16))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-20))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *2))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-8))))))))))))))) =0 /\ ~0 +a *(0 +a *(0 +a *((0 +b *((0 +c *1) +b *(0 +x *1))) +a *(((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *3))) +a *(0 +x *(0 +x *(0 +x *2))))))) =0) \/ ~0 +a *(0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *2)) +b *((0 +c *(0 +x *4)) +b *(0 +x *(0 +x *2)))) +a *(((0 +c *(0 +x *(0 +x *4))) +b *(0 +x *(0 +x *(0 +x *4)))) +a *(0 +x *(0 +x *(0 +x *(0 +x *2))))))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *(0 +b *((0 +c *(0 +c *(0 +c *(0 +c *-1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *-4)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-6)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-4)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *-1))))))))))) +a *((0 +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +c *4))))) +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *14))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *12))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-8))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-16))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-6))))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +c *(0 +x *8)))))) +b *((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *(0 +x *48)))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *88)))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *50)))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-12)))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-14))))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *32))))))) +b *((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *120))))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *132))))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *28))))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-16))))))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *48)))))))) +b *((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *112)))))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *56)))))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-9))))))))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *32))))))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *36))))))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-2))))))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *8))))))))))))))))))))))) =0 /\ 0 +a *(0 +a *(0 +a *(0 +a *(0 +a *((0 +b *(0 +b *(0 +b *((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1))))))) +a *((0 +b *((0 +c *(0 +c *(0 +c *-4))) +b *((0 +c *(0 +c *(0 +x *-6))) +b *((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *4))))))) +a *(((0 +c *(0 +c *(0 +c *(0 +x *-8)))) +b *((0 +c *(0 +c *(0 +x *(0 +x *-24)))) +b *((0 +c *(0 +x *(0 +x *(0 +x *-12)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *5))))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *(0 +x *-16))))) +b *((0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-20))))) +b *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *2))))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *-8)))))))))))))) =0 /\ ~0 +a *(0 +a *(0 +a *(0 +a *((0 +b *((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1))))) +a *(((0 +c *(0 +c *(0 +x *2))) +b *((0 +c *(0 +x *(0 +x *6))) +b *(0 +x *(0 +x *(0 +x *4))))) +a *(((0 +c *(0 +x *(0 +x *(0 +x *4)))) +b *(0 +x *(0 +x *(0 +x *(0 +x *5))))) +a *(0 +x *(0 +x *(0 +x *(0 +x *(0 +x *2))))))))))) =0)) \/ 0 +a *1 =0 /\ ~0 +b *1 =0 /\ (0 +b *((0 +c *1) +b *(0 +x *1)) =0 /\ (0 +c *(0 +c *1)) +b *(0 +c *(0 +x *1)) =0 /\ (0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~(0 +b *1) +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *(0 +b *1)) +a *((0 +c *-1) +b *(0 +x *1)) =0) \/ ~0 +a *1 =0 /\ (~0 +a *((0 +b *(0 +b *1)) +a *(((0 +c *-1) +b *(0 +x *2)) +a *(0 +x *(0 +x *1)))) =0 \/ ~0 +a *(0 +a *((0 +b *1) +a *(0 +x *2))) =0)) \/ ~0 +b *((0 +c *1) +b *(0 +x *1)) =0 /\ 0 +a *((0 +c *(0 +c *(0 +c *(0 +c *1)))) +b *((0 +c *(0 +c *(0 +c *(0 +x *2)))) +b *(0 +c *(0 +c *(0 +x *(0 +x *1)))))) =0 /\ ~(0 +b *(0 +b *((0 +c *1) +b *(0 +x *1)))) +a *((0 +c *(0 +c *-1)) +b *(0 +b *(0 +x *(0 +x *1)))) =0) \/ 0 +a *1 =0 /\ 0 +b *1 =0 /\ ~0 +c *1 =0 /\ (0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~(0 +b *1) +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *(0 +b *1)) +a *((0 +c *-1) +b *(0 +x *1)) =0) \/ ~0 +a *1 =0 /\ (~0 +a *((0 +b *(0 +b *1)) +a *(((0 +c *-1) +b *(0 +x *2)) +a *(0 +x *(0 +x *1)))) =0 \/ ~0 +a *(0 +a *((0 +b *1) +a *(0 +x *2))) =0))) /\ ((0 +c *1) +b *(0 +x *1)) +a *(0 +x *(0 +x *1)) =0)>>"
    );
    (
        // idx 34
        // complex.p042
        @"forall x y. (a * x^2 + b * x + c = 0) /\ 
                  (a * y^2 + b * y + c = 0) /\ 
                  (forall z. (a * z^2 + b * z + c = 0)
                             ==> (z = x) \/ (z = y))
                  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)",
        formula<fol>.False,
        @""
    );
    (
        // idx 35
        // complex.p043
        @"forall c x y. (a * x^2 + b * x + c = 0) /\ 
                  (a * y^2 + b * y + c = 0) /\ 
                  (forall z. (a * z^2 + b * z + c = 0)
                             ==> (z = x) \/ (z = y))
                  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)",
        formula<fol>.False,
        @""
    );
    (
        // idx 36
        // complex.p044
        @"forall a b c x y. (a * x^2 + b * x + c = 0) /\ 
                   (a * y^2 + b * y + c = 0) /\ 
                   (forall z. (a * z^2 + b * z + c = 0)
                        ==> (z = x) \/ (z = y))
                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0)",
        formula<fol>.False,
        @""
    );
    (
        // idx 37
        // complex.p045
        @"~(forall x1 y1 x2 y2 x3 y3.
            exists x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\ 
                        (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 38
        // complex.p046
        @"forall a b c.
        (exists x y. (a * x^2 + b * x + c = 0) /\ 
                (a * y^2 + b * y + c = 0) /\ 
                ~(x = y)) <=>
        (a = 0) /\ (b = 0) /\ (c = 0) \/
        ~(a = 0) /\ ~(b^2 = 4 * a * c)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 39
        // complex.p047
        @"~(forall x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
        (x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\ 
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\ 
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\ 
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2
        ==> x0 = x0' /\ y0 = y0')",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 40
        // complex.p048
        @"forall a b c.
        a * x^2 + b * x + c = 0 /\ 
        a * y^2 + b * y + c = 0 /\ 
        ~(x = y)
        ==> a * (x + y) + b = 0",
        Not
          (And
             (And
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn
                              ("+",
                               [Fn ("0",[]); Fn ("*",[Var "y"; Fn ("1",[])])]);
                            Fn ("*",[Var "x"; Fn ("-1",[])])]); Fn ("0",[])])),
                 Or
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn
                                 ("+",
                                  [Fn ("0",[]);
                                   Fn
                                     ("*",
                                      [Var "y";
                                       Fn
                                         ("+",
                                          [Fn ("0",[]);
                                           Fn ("*",[Var "y"; Fn ("1",[])])])])]);
                               Fn
                                 ("*",
                                  [Var "x";
                                   Fn
                                     ("+",
                                      [Fn ("0",[]);
                                       Fn ("*",[Var "x"; Fn ("-1",[])])])])]);
                           Fn ("0",[])])),
                    Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn
                                        ("*",
                                         [Var "y";
                                          Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn ("*",[Var "y"; Fn ("1",[])])])])]);
                                  Fn
                                    ("*",
                                     [Var "x";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "x"; Fn ("-1",[])])])])]);
                              Fn ("0",[])]))))),
              Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn
                              ("+",
                               [Fn ("0",[]); Fn ("*",[Var "y"; Fn ("-1",[])])]);
                            Fn ("*",[Var "x"; Fn ("1",[])])]); Fn ("0",[])]))))),
        @"<<~(((0 +y *1) +x *-1 =0 /\ ((0 +y *(0 +y *1)) +x *(0 +x *-1) =0 \/ ~(0 +y *(0 +y *1)) +x *(0 +x *-1) =0)) /\ ~(0 +y *-1) +x *1 =0)>>"
    );
    (
        // idx 41
        // complex.p049
        @"forall a b c.
        (a * x^2 + b * x + c = 0) /\ 
        (2 * a * y^2 + 2 * b * y + 2 * c = 0) /\ 
        ~(x = y)
        ==> (a * (x + y) + b = 0)",
        Not
          (And
             (And
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn
                              ("+",
                               [Fn ("0",[]); Fn ("*",[Var "y"; Fn ("2",[])])]);
                            Fn ("*",[Var "x"; Fn ("-2",[])])]); Fn ("0",[])])),
                 Or
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn
                                 ("+",
                                  [Fn ("0",[]);
                                   Fn
                                     ("*",
                                      [Var "y";
                                       Fn
                                         ("+",
                                          [Fn ("0",[]);
                                           Fn ("*",[Var "y"; Fn ("2",[])])])])]);
                               Fn
                                 ("*",
                                  [Var "x";
                                   Fn
                                     ("+",
                                      [Fn ("0",[]);
                                       Fn ("*",[Var "x"; Fn ("-2",[])])])])]);
                           Fn ("0",[])])),
                    Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn
                                        ("*",
                                         [Var "y";
                                          Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn ("*",[Var "y"; Fn ("2",[])])])])]);
                                  Fn
                                    ("*",
                                     [Var "x";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "x"; Fn ("-2",[])])])])]);
                              Fn ("0",[])]))))),
              Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn
                              ("+",
                               [Fn ("0",[]); Fn ("*",[Var "y"; Fn ("-1",[])])]);
                            Fn ("*",[Var "x"; Fn ("1",[])])]); Fn ("0",[])]))))),
        @"<<~(((0 +y *2) +x *-2 =0 /\ ((0 +y *(0 +y *2)) +x *(0 +x *-2) =0 \/ ~(0 +y *(0 +y *2)) +x *(0 +x *-2) =0)) /\ ~(0 +y *-1) +x *1 =0)>>"
    );
    (
        // idx 42
        // complex.p050
        @"~(y_1 = 2 * y_3 /\ 
        y_2 = 2 * y_4 /\ 
        y_1 * y_3 = y_2 * y_4 /\ 
        (y_1^2 - y_2^2) * z = 1)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 43
        // complex.p051
        @"forall y_1 y_2 y_3 y_4.
        (y_1 = 2 * y_3) /\ 
        (y_2 = 2 * y_4) /\ 
        (y_1 * y_3 = y_2 * y_4)
        ==> (y_1^2 = y_2^2)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 44
        // complex.p052
        @"~((c^2 = a^2 + b^2) /\ 
            (c^2 = x0^2 + (y0 - b)^2) /\ 
            (y0 * t1 = a + x0) /\ 
            (y0 * t2 = a - x0) /\ 
            ((1 - t1 * t2) * t = t1 + t2) /\ 
            (u * (b * t - a) = 1) /\ 
            (v1 * a + v2 * x0 + v3 * y0 = 1))",
        formula<fol>.False,   // The result was unknown when test created. False used as place holder.
        @""
    );
    (
        // idx 45
        // complex.p053
        @"(c^2 = a^2 + b^2) /\ 
           (c^2 = x0^2 + (y0 - b)^2) /\ 
           (y0 * t1 = a + x0) /\ 
           (y0 * t2 = a - x0) /\ 
           ((1 - t1 * t2) * t = t1 + t2) /\ 
           (~(a = 0) \/ ~(x0 = 0) \/ ~(y0 = 0))
           ==> (b * t = a)",
        formula<fol>.False,   // The result was unknown when test created. False used as place holder.
        @""
    );
    (
        // idx 46
        // complex.p054
        @"(x1 = u3) /\ 
        (x1 * (u2 - u1) = x2 * u3) /\ 
        (x4 * (x2 - u1) = x1 * (x3 - u1)) /\ 
        (x3 * u3 = x4 * u2) /\ 
        ~(u1 = 0) /\ 
        ~(u3 = 0)
        ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 47
        // complex.p055
        @"(u1 * x1 - u1 * u3 = 0) /\ 
        (u3 * x2 - (u2 - u1) * x1 = 0) /\ 
        (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\ 
        (u3 * x4 - u2 * x3 = 0) /\ 
        ~(u1 = 0) /\ 
        ~(u3 = 0)
        ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 48
        // complex.p056
        @"(y1 * y3 + x1 * x3 = 0) /\ 
        (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) /\ 
        ~(x3 = 0) /\ 
        ~(y3 = 0)
        ==> (y1 * (x2 - x3) = x1 * (y2 - y3))",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 49
        // complex.p057
        @"(2 * u2 * x2 + 2 * u3 * x1 - u3^2 - u2^2 = 0) /\ 
        (2 * u1 * x2 - u1^2 = 0) /\ 
        (-(x3^2) + 2 * x2 * x3 + 2 * u4 * x1 - u4^2 = 0) /\ 
        (u3 * x5 + (-(u2) + u1) * x4 - u1 * u3 = 0) /\ 
        ((u2 - u1) * x5 + u3 * x4 + (-(u2) + u1) * x3 - u3 * u4 = 0) /\ 
        (u3 * x7 - u2 * x6 = 0) /\ 
        (u2 * x7 + u3 * x6 - u2 * x3 - u3 * u4 = 0) /\ 
        ~(4 * u1 * u3 = 0) /\ 
        ~(2 * u1 = 0) /\ 
        ~(-(u3^2) - u2^2 + 2 * u1 * u2 - u1^2 = 0) /\ 
        ~(u3 = 0) /\ 
        ~(-(u3^2) - u2^2 = 0) /\ 
        ~(u2 = 0)
        ==> (x4 * x7 + (-(x5) + x3) * x6 - x3 * x4 = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 50
        // complex.p058
        @"exists c.
        (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\ 
        (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\ 
        (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))",
        formula<fol>.False,  // Dummy value used as place holder
        @"<<((0 +b *(0 +b *1)) +ae *(0 +ae *-1)) +a *(0 +b *-2) =0 /\ (((0 +b *(0 +b *(0 +b *-1))) +ae *(0 +ae *(0 +b *2))) +a *((0 +b *(0 +b *1)) +a *(0 +b *2)) =0 /\ (0 +p2 *1) +ae *(0 +ae *(0 +b *(0 +b *-1))) =0 /\ (0 +b *1 =0 /\ ((0 +b *(0 +b *2)) +ai *(0 +ai *-1) =0 /\ (((0 +b *(0 +b *(0 +b *1))) +ai *(0 +ai *(0 +b *-2))) +a *(0 +a *(0 +b *-1)) =0 /\ (0 +p1 *1) +ai *(0 +ai *(0 +b *(0 +b *-1))) =0 /\ (0 +a *-1 =0 /\ ((0 +be *(0 +be *-1)) +a *(0 +a *2) =0 /\ (0 +a *(((0 +be *(0 +be *2)) +b *(0 +b *1)) +a *(0 +a *-1)) =0 /\ (0 +p3 *1) +a *(0 +a *(0 +be *(0 +be *-1))) =0 \/ ~0 +a *(((0 +be *(0 +be *2)) +b *(0 +b *1)) +a *(0 +a *-1)) =0) \/ ~(0 +be *(0 +be *-1)) +a *(0 +a *2) =0) \/ ~0 +a *-1 =0) \/ ~((0 +b *(0 +b *(0 +b *1))) +ai *(0 +ai *(0 +b *-2))) +a *(0 +a *(0 +b *-1)) =0 /\ ((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *-1)))) +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +p3 *1)))))))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *2)))) +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *2))) +b *(0 +b *(0 +p3 *-6)))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-4))) +b *(0 +b *((0 +p3 *12) +b *(0 +b *(0 +be *(0 +be *-1))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p3 *-8) +b *(0 +b *(0 +be *(0 +be *2))))))))))))) +a *((((0 +p1 *(0 +p1 *(0 +p1 *1))) +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-2))) +b *(0 +b *(0 +p1 *-1))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *(0 +p1 *-3)) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *8))) +b *(0 +b *((0 +p1 *4) +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *1)))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-8))) +b *(0 +b *((0 +p1 *-1) +b *(0 +b *((0 +be *(0 +be *-8)) +b *(0 +b *-4)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *3)))))))))))) +a *(((0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *1)))) +b *(0 +b *((0 +p1 *(0 +p1 *2)) +b *(0 +b *(0 +b *(0 +b *((0 +p3 *-3) +b *(0 +b *(0 +be *(0 +be *-1))))))))))) +ai *(0 +ai *((0 +b *((0 +p1 *(0 +p1 *-4)) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-2))) +b *(0 +b *(((0 +p3 *12) +p1 *-4) +b *(0 +b *(0 +be *(0 +be *6))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p3 *-12) +p1 *8) +b *(0 +b *((0 +be *(0 +be *-11)) +b *(0 +b *2))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *-4))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *4))) +b *(0 +b *(0 +p1 *3))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-8))) +b *(0 +b *((0 +p1 *-8) +b *(0 +b *((0 +be *(0 +be *-4)) +b *(0 +b *-3)))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *4) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *8)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))))))) +a *(((0 +b *((0 +p1 *(0 +p1 *-2)) +b *(0 +b *(0 +b *(0 +b *((0 +p3 *3) +b *(0 +b *(0 +be *(0 +be *3))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p3 *-6) +p1 *4) +b *(0 +b *(0 +be *(0 +be *-12))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *12)) +b *(0 +b *-2))))))))) +a *(((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-2))) +b *(0 +b *(0 +p1 *-3))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *4) +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *3)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))))) +a *(((0 +b *(0 +b *(0 +b *((0 +p3 *-1) +b *(0 +b *(0 +be *(0 +be *-3))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *6))))))) +a *(((0 +b *(0 +b *(0 +p1 *1))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-1)))))) +a *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *1)))))))))))) =0) \/ ~(0 +b *(0 +b *2)) +ai *(0 +ai *-1) =0 /\ (((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *2))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-5))))) +ai *(0 +ai *(0 +b *(0 +be *(0 +be *2))))))) +a *(((0 +b *(0 +b *((0 +p1 *2) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *3)))))) +ai *(0 +ai *(((0 +p1 *-1) +b *(0 +b *((0 +be *(0 +be *-8)) +b *(0 +b *-2)))) +ai *(0 +ai *((0 +be *(0 +be *2)) +b *(0 +b *-2)))))) +a *(((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *-4))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *1)) +b *(0 +b *10))) +ai *(0 +ai *(0 +b *-4))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *-2)))) +ai *(0 +ai *(0 +ai *(0 +ai *-1)))) +a *(((0 +b *(0 +b *(0 +b *4))) +ai *(0 +ai *(0 +b *-2))) +a *(0 +b *(0 +b *-1)))))) =0 /\ ((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *2))) +b *(0 +b *(0 +p3 *4))))) +ai *(0 +ai *(((0 +be *(0 +be *(0 +p1 *-1))) +b *(0 +b *((0 +p3 *-4) +b *(0 +b *(0 +be *(0 +be *-2)))))) +ai *(0 +ai *((0 +p3 *1) +b *(0 +b *(0 +be *(0 +be *1)))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +p1 *-1)))) +ai *(0 +ai *((0 +b *((0 +p1 *2) +b *(0 +b *(0 +b *(0 +b *1))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *-2))))))) +a *(((0 +b *(0 +b *((0 +p1 *-4) +b *(0 +b *(0 +be *(0 +be *-4)))))) +ai *(0 +ai *(((0 +p1 *2) +b *(0 +b *((0 +be *(0 +be *4)) +b *(0 +b *4)))) +ai *(0 +ai *((0 +be *(0 +be *-1)) +b *(0 +b *-2)))))) +a *((0 +b *(0 +p1 *1)) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *-1))))))) =0 \/ ~((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *2))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-5))))) +ai *(0 +ai *(0 +b *(0 +be *(0 +be *2))))))) +a *(((0 +b *(0 +b *((0 +p1 *2) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *3)))))) +ai *(0 +ai *(((0 +p1 *-1) +b *(0 +b *((0 +be *(0 +be *-8)) +b *(0 +b *-2)))) +ai *(0 +ai *((0 +be *(0 +be *2)) +b *(0 +b *-2)))))) +a *(((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *-4))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *1)) +b *(0 +b *10))) +ai *(0 +ai *(0 +b *-4))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *-2)))) +ai *(0 +ai *(0 +ai *(0 +ai *-1)))) +a *(((0 +b *(0 +b *(0 +b *4))) +ai *(0 +ai *(0 +b *-2))) +a *(0 +b *(0 +b *-1)))))) =0 /\ ((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *8)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p3 *32)))) +b *(0 +b *((0 +p3 *(0 +p3 *32)) +b *(0 +b *(0 +be *(0 +be *(0 +p3 *-8))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-12)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p3 *-64)))) +b *(0 +b *(((0 +p3 *(0 +p3 *-80)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-16))))) +b *(0 +b *(0 +be *(0 +be *(0 +p3 *12))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *6)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p3 *48)))) +b *(0 +b *(((0 +p3 *(0 +p3 *80)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *24))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *-22))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *8)))))))))))))) +ai *(0 +ai *(((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-1)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p3 *-16)))) +b *(0 +b *(((0 +p3 *(0 +p3 *-40)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-12))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *25))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-12)))))))))))) +ai *(0 +ai *(((0 +be *(0 +be *(0 +p1 *(0 +p3 *2)))) +b *(0 +b *(((0 +p3 *(0 +p3 *10)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *2))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *-12))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *6)))))))))) +ai *(0 +ai *((0 +p3 *(0 +p3 *-1)) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *2))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-1)))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *-4)))) +b *(0 +b *(((0 +p1 *(0 +p3 *-24)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *16))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-32) +p1 *8))) +b *(0 +b *(0 +p3 *-12)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *12)))) +b *(0 +b *(((0 +p1 *(0 +p3 *84)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-56))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *128) +p1 *-20))) +b *(0 +b *(((0 +p3 *60) +be *(0 +be *(0 +be *(0 +be *-16)))) +b *(0 +b *(0 +be *(0 +be *-8))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *-9)))) +b *(0 +b *(((0 +p1 *(0 +p3 *-90)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *60))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-176) +p1 *6))) +b *(0 +b *(((0 +p3 *-99) +be *(0 +be *(0 +be *(0 +be *56)))) +b *(0 +b *(0 +be *(0 +be *24))))))))))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *2)))) +b *(0 +b *(((0 +p1 *(0 +p3 *39)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-26))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *112) +p1 *5))) +b *(0 +b *(((0 +p3 *60) +be *(0 +be *(0 +be *(0 +be *-60)))) +b *(0 +b *(0 +be *(0 +be *-18))))))))))) +ai *(0 +ai *((0 +b *(((0 +p1 *(0 +p3 *-6)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *4))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-34) +p1 *-2))) +b *(0 +b *(((0 +p3 *-12) +be *(0 +be *(0 +be *(0 +be *26)))) +b *(0 +b *(0 +be *(0 +be *4))))))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *(0 +p3 *4))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-4))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *(0 +p1 *4))) +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *((0 +p3 *-64) +p1 *16)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *32))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-48) +p1 *56))) +b *(0 +b *(((0 +p3 *16) +p1 *12) +be *(0 +be *(0 +be *(0 +be *8)))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *(0 +p1 *(0 +p1 *-4))) +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *((0 +p3 *128) +p1 *-36)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-64))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *104) +p1 *-88))) +b *(0 +b *((((0 +p3 *-24) +p1 *-44) +be *(0 +be *(0 +be *(0 +be *-76)))) +b *(0 +b *((0 +be *(0 +be *-56)) +b *(0 +b *-12)))))))))))))) +ai *(0 +ai *(((0 +p1 *(0 +p1 *(0 +p1 *1))) +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *((0 +p3 *-96) +p1 *24)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *48))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-100) +p1 *30))) +b *(0 +b *((((0 +p3 *44) +p1 *51) +be *(0 +be *(0 +be *(0 +be *150)))) +b *(0 +b *((0 +be *(0 +be *88)) +b *(0 +b *28)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p1 *((0 +p3 *32) +p1 *-5)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-16))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *54) +p1 *8))) +b *(0 +b *((((0 +p3 *-50) +p1 *-24) +be *(0 +be *(0 +be *(0 +be *-121)))) +b *(0 +b *((0 +be *(0 +be *-30)) +b *(0 +b *-19)))))))))) +ai *(0 +ai *((((0 +p1 *(0 +p3 *-4)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *2))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-16) +p1 *-4))) +b *(0 +b *((((0 +p3 *24) +p1 *4) +be *(0 +be *(0 +be *(0 +be *44)))) +b *(0 +b *((0 +be *(0 +be *-8)) +b *(0 +b *4)))))))) +ai *(0 +ai *((0 +be *(0 +be *(0 +p3 *2))) +b *(0 +b *(((0 +p3 *-4) +be *(0 +be *(0 +be *(0 +be *-6)))) +b *(0 +b *(0 +be *(0 +be *4)))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *4)))) +b *(0 +b *(((0 +p1 *((0 +p3 *24) +p1 *8)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-16))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *32) +p1 *-24))) +b *(0 +b *((((0 +p3 *20) +p1 *-16) +be *(0 +be *(0 +be *(0 +be *32)))) +b *(0 +b *(0 +be *(0 +be *12))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *-4)))) +b *(0 +b *(((0 +p1 *((0 +p3 *-36) +p1 *-24)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *24))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-64) +p1 *60))) +b *(0 +b *((((0 +p3 *-60) +p1 *40) +be *(0 +be *(0 +be *(0 +be *-112)))) +b *(0 +b *((0 +be *(0 +be *-12)) +b *(0 +b *16))))))))))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *1)))) +b *(0 +b *(((0 +p1 *((0 +p3 *18) +p1 *18)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-12))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *48) +p1 *-58))) +b *(0 +b *((((0 +p3 *49) +p1 *-12) +be *(0 +be *(0 +be *(0 +be *152)))) +b *(0 +b *((0 +be *(0 +be *-49)) +b *(0 +b *-48))))))))))) +ai *(0 +ai *((0 +b *(((0 +p1 *((0 +p3 *-3) +p1 *-4)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *2))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-16) +p1 *25))) +b *(0 +b *((((0 +p3 *-22) +p1 *-10) +be *(0 +be *(0 +be *(0 +be *-100)))) +b *(0 +b *((0 +be *(0 +be *92)) +b *(0 +b *36))))))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *((0 +p3 *2) +p1 *-4))) +b *(0 +b *((((0 +p3 *9) +p1 *4) +be *(0 +be *(0 +be *(0 +be *32)))) +b *(0 +b *((0 +be *(0 +be *-53)) +b *(0 +b *-8))))))) +ai *(0 +ai *(0 +b *(((0 +p3 *-2) +be *(0 +be *(0 +be *(0 +be *-4)))) +b *(0 +b *(0 +be *(0 +be *10))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *16)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-8) +p1 *16))) +b *(0 +b *((((0 +p3 *-32) +p1 *-20) +be *(0 +be *(0 +be *(0 +be *16)))) +b *(0 +b *(0 +be *(0 +be *-16)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *-24)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *12) +p1 *-48))) +b *(0 +b *((((0 +p3 *112) +p1 *-12) +be *(0 +be *(0 +be *(0 +be *-24)))) +b *(0 +b *((0 +be *(0 +be *72)) +b *(0 +b *20)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *(0 +p1 *12)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-6) +p1 *36))) +b *(0 +b *((((0 +p3 *-120) +p1 *51) +be *(0 +be *(0 +be *(0 +be *20)))) +b *(0 +b *((0 +be *(0 +be *-124)) +b *(0 +b *-4)))))))))) +ai *(0 +ai *(((0 +p1 *(0 +p1 *-2)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *1) +p1 *-8))) +b *(0 +b *((((0 +p3 *52) +p1 *-32) +be *(0 +be *(0 +be *(0 +be *-14)))) +b *(0 +b *((0 +be *(0 +be *110)) +b *(0 +b *-27)))))))) +ai *(0 +ai *((0 +b *(0 +b *((((0 +p3 *-8) +p1 *6) +be *(0 +be *(0 +be *(0 +be *6)))) +b *(0 +b *((0 +be *(0 +be *-48)) +b *(0 +b *20)))))) +ai *(0 +ai *((0 +be *(0 +be *(0 +be *(0 +be *-1)))) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *-4)))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *-8)) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *16))) +b *(0 +b *((((0 +p3 *-4) +p1 *32) +be *(0 +be *(0 +be *(0 +be *-32)))) +b *(0 +b *(0 +be *(0 +be *-20))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *8)) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-24))) +b *(0 +b *((((0 +p3 *-4) +p1 *-64) +be *(0 +be *(0 +be *(0 +be *64)))) +b *(0 +b *((0 +be *(0 +be *20)) +b *(0 +b *-32))))))))))) +ai *(0 +ai *((0 +b *((0 +p1 *(0 +p1 *-2)) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *12))) +b *(0 +b *((((0 +p3 *3) +p1 *56) +be *(0 +be *(0 +be *(0 +be *-48)))) +b *(0 +b *((0 +be *(0 +be *11)) +b *(0 +b *72))))))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *(0 +p1 *-2))) +b *(0 +b *((((0 +p3 *2) +p1 *-24) +be *(0 +be *(0 +be *(0 +be *16)))) +b *(0 +b *((0 +be *(0 +be *-8)) +b *(0 +b *-64))))))) +ai *(0 +ai *((0 +b *((((0 +p3 *-1) +p1 *4) +be *(0 +be *(0 +be *(0 +be *-2)))) +b *(0 +b *((0 +be *(0 +be *-4)) +b *(0 +b *26))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *-4))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-8))) +b *(0 +b *((((0 +p3 *16) +p1 *4) +be *(0 +be *(0 +be *(0 +be *8)))) +b *(0 +b *(0 +be *(0 +be *32)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *8))) +b *(0 +b *((((0 +p3 *-24) +p1 *-4) +be *(0 +be *(0 +be *(0 +be *-12)))) +b *(0 +b *((0 +be *(0 +be *-104)) +b *(0 +b *-4)))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-2))) +b *(0 +b *((((0 +p3 *12) +p1 *5) +be *(0 +be *(0 +be *(0 +be *6)))) +b *(0 +b *((0 +be *(0 +be *112)) +b *(0 +b *4)))))))) +ai *(0 +ai *((0 +b *(0 +b *((((0 +p3 *-2) +p1 *-4) +be *(0 +be *(0 +be *(0 +be *-1)))) +b *(0 +b *((0 +be *(0 +be *-50)) +b *(0 +b *-5)))))) +ai *(0 +ai *(((0 +p1 *1) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *4)))) +ai *(0 +ai *(0 +b *(0 +b *-1)))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p3 *-4) +p1 *-16) +b *(0 +b *(0 +be *(0 +be *4))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p3 *4) +p1 *24) +b *(0 +b *((0 +be *(0 +be *4)) +b *(0 +b *16))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p3 *-1) +p1 *-12) +b *(0 +b *((0 +be *(0 +be *-3)) +b *(0 +b *-24))))))) +ai *(0 +ai *((0 +b *((0 +p1 *2) +b *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *12))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *1)) +b *(0 +b *-2))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *4) +b *(0 +b *(0 +be *(0 +be *-16)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *-4) +b *(0 +b *((0 +be *(0 +be *24)) +b *(0 +b *-4)))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *1) +b *(0 +b *((0 +be *(0 +be *-12)) +b *(0 +b *4)))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *-1)))))))))) +a *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *4))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-4))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *1))))))))))))))))) =0)) \/ ~0 +b *1 =0 /\ ((0 +b *(0 +be *(0 +be *-1))) +a *(((0 +b *(0 +b *2)) +ai *(0 +ai *-1)) +a *(0 +b *2)) =0 /\ (0 +a *(((0 +b *((0 +be *(0 +be *2)) +b *(0 +b *2))) +ai *(0 +ai *(0 +b *-2))) +a *(0 +a *(0 +b *-2))) =0 /\ (0 +b *(0 +p3 *1)) +a *(((0 +p1 *1) +ai *(0 +ai *(0 +b *(0 +b *-1)))) +a *(0 +b *(0 +be *(0 +be *-1)))) =0 \/ ~0 +a *(((0 +b *((0 +be *(0 +be *2)) +b *(0 +b *2))) +ai *(0 +ai *(0 +b *-2))) +a *(0 +a *(0 +b *-2))) =0 /\ (0 +b *(0 +b *(0 +b *(0 +b *(0 +p3 *(0 +p3 *(0 +p3 *-1))))))) +a *(((0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p3 *(0 +p3 *-3))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *(0 +p3 *4)))) +b *(0 +b *(0 +p3 *(0 +p3 *4))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p3 *(0 +p3 *-2)))) +b *(0 +b *(0 +p3 *(0 +p3 *-3))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +p3 *(0 +p3 *2))))))))) +a *(((0 +b *(0 +b *((0 +p1 *(0 +p1 *(0 +p3 *-3))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *(0 +p3 *3)) +p1 *(0 +p3 *8)))) +b *(0 +b *(((0 +p1 *(0 +p3 *8)) +be *(0 +be *(0 +be *(0 +be *(0 +p3 *-4))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *-8))) +b *(0 +b *(0 +p3 *-4))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p3 *-4)))) +b *(0 +b *(((0 +p1 *(0 +p3 *-6)) +be *(0 +be *(0 +be *(0 +be *(0 +p3 *8))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *16))) +b *(0 +b *(0 +p3 *8))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *(0 +p3 *4)) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *-12))) +b *(0 +b *(0 +p3 *-11))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +p3 *4))))))))))) +a *(((0 +b *((0 +p1 *(0 +p1 *(0 +p1 *-1))) +b *(0 +b *((0 +be *(0 +be *((0 +p1 *((0 +p3 *6) +p1 *4)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *8))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *-4)) +p1 *(0 +p1 *4)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-8) +p1 *20))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-8) +p1 *16))) +b *(0 +b *(0 +p1 *4)))))))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *-2)))) +b *(0 +b *((((0 +p3 *(0 +p3 *2)) +p1 *(0 +p1 *-3)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *4) +p1 *-16))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *6) +p1 *-32) +be *(0 +be *(0 +be *(0 +be *-8)))))) +b *(0 +b *(((0 +p1 *-16) +be *(0 +be *(0 +be *(0 +be *-20)))) +b *(0 +b *((0 +be *(0 +be *-16)) +b *(0 +b *-4))))))))))) +ai *(0 +ai *((0 +b *((0 +p1 *(0 +p1 *2)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-4) +p1 *12))) +b *(0 +b *(((0 +p1 *13) +be *(0 +be *(0 +be *(0 +be *16)))) +b *(0 +b *((0 +be *(0 +be *28)) +b *(0 +b *12))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +p1 *-4) +b *(0 +b *((0 +be *(0 +be *-10)) +b *(0 +b *-9))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *2))))))))))))) +a *(((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *3)))) +b *(0 +b *(((0 +p1 *(0 +p3 *-8)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *1) +p1 *-8))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *16) +p1 *-8) +be *(0 +be *(0 +be *(0 +be *4)))))) +b *(0 +b *(((0 +p3 *12) +be *(0 +be *(0 +be *(0 +be *8)))) +b *(0 +b *(0 +be *(0 +be *4)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p1 *(0 +p3 *4)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *4))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-24) +p1 *6) +be *(0 +be *(0 +be *(0 +be *-8)))))) +b *(0 +b *(((0 +p3 *-24) +be *(0 +be *(0 +be *(0 +be *-16)))) +b *(0 +b *(0 +be *(0 +be *-8)))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-4))) +b *(0 +b *(((0 +p3 *16) +be *(0 +be *(0 +be *(0 +be *12)))) +b *(0 +b *(0 +be *(0 +be *11)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-4)))))))))))) +a *(((0 +b *(0 +b *(0 +b *(((0 +p1 *(0 +p1 *-4)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-23))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *8) +p1 *-32) +be *(0 +be *(0 +be *(0 +be *4)))))) +b *(0 +b *((0 +p1 *-12) +be *(0 +be *(0 +be *(0 +be *4))))))))))) +ai *(0 +ai *((0 +b *((0 +p1 *(0 +p1 *2)) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-4) +p1 *24) +be *(0 +be *(0 +be *(0 +be *-2)))))) +b *(0 +b *(((0 +p1 *24) +be *(0 +be *(0 +be *(0 +be *17)))) +b *(0 +b *((0 +be *(0 +be *32)) +b *(0 +b *12))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p1 *-8) +be *(0 +be *(0 +be *(0 +be *2)))) +b *(0 +b *((0 +be *(0 +be *-24)) +b *(0 +b *-20))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *6))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-8) +p1 *8) +be *(0 +be *(0 +be *(0 +be *-3)))))) +b *(0 +b *(((0 +p3 *-12) +be *(0 +be *(0 +be *(0 +be *-16)))) +b *(0 +b *(0 +be *(0 +be *-12)))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-4))) +b *(0 +b *(((0 +p3 *16) +be *(0 +be *(0 +be *(0 +be *24)))) +b *(0 +b *(0 +be *(0 +be *24)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-16)))))))))) +a *(((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *16))) +b *(0 +b *((0 +p1 *12) +be *(0 +be *(0 +be *(0 +be *-4))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p1 *-8) +be *(0 +be *(0 +be *(0 +be *2)))) +b *(0 +b *((0 +be *(0 +be *-16)) +b *(0 +b *-12))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *8))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p3 *4) +be *(0 +be *(0 +be *(0 +be *8)))) +b *(0 +b *(0 +be *(0 +be *12)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-16)))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +p1 *-4)))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *4))))))) +a *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-4))))))))))))))) =0) \/ ~(0 +b *(0 +be *(0 +be *-1))) +a *(((0 +b *(0 +b *2)) +ai *(0 +ai *-1)) +a *(0 +b *2)) =0 /\ (((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p3 *1))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *1))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-2))))))))) +a *(((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *1))) +b *(0 +b *((0 +p3 *-2) +be *(0 +be *(0 +be *(0 +be *4)))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p3 *1) +be *(0 +be *(0 +be *(0 +be *-2)))) +b *(0 +b *(0 +be *(0 +be *3)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +be *(0 +be *-2)))))))) +a *(((0 +b *(0 +b *(0 +b *((((0 +p3 *-2) +p1 *-2) +be *(0 +be *(0 +be *(0 +be *2)))) +b *(0 +b *(0 +be *(0 +be *-4))))))) +ai *(0 +ai *((0 +b *((0 +p1 *1) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *-2))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *2))))))) +a *(((0 +b *(0 +b *((0 +p1 *-2) +b *(0 +b *(0 +be *(0 +be *-6)))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *3)) +b *(0 +b *-6)))) +ai *(0 +ai *(0 +b *(0 +b *4)))))) +a *((0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-2))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *-4))) +ai *(0 +ai *(0 +b *1)))))))) =0 /\ ((0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *1))))) +b *(0 +b *(0 +be *(0 +be *(0 +p3 *2))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p3 *-1))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-1)))))))))) +a *(((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p3 *2) +p1 *-2))) +b *(0 +b *(0 +p3 *-2)))))) +ai *(0 +ai *((0 +b *((0 +be *(0 +be *(0 +p1 *1))) +b *(0 +b *((0 +p3 *2) +b *(0 +b *(0 +be *(0 +be *2))))))) +ai *(0 +ai *(0 +b *((0 +p3 *-1) +b *(0 +b *(0 +be *(0 +be *-1))))))))) +a *(((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-2))) +b *(0 +b *(((0 +p3 *-4) +p1 *2) +be *(0 +be *(0 +be *(0 +be *-2)))))))) +ai *(0 +ai *((0 +b *(0 +b *((((0 +p3 *2) +p1 *-2) +be *(0 +be *(0 +be *(0 +be *1)))) +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *-2)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *2)))))))) +a *(((0 +b *(0 +b *(0 +b *((((0 +p3 *-2) +p1 *4) +be *(0 +be *(0 +be *(0 +be *-2)))) +b *(0 +b *(0 +be *(0 +be *2))))))) +ai *(0 +ai *((0 +b *((0 +p1 *-2) +b *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *-4))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *1)) +b *(0 +b *2))))))) +a *(((0 +b *(0 +b *((0 +p1 *2) +b *(0 +b *(0 +be *(0 +be *4)))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *-2)))))) +a *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *2))))))))) =0 \/ ~((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p3 *1))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *1))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-2))))))))) +a *(((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *1))) +b *(0 +b *((0 +p3 *-2) +be *(0 +be *(0 +be *(0 +be *4)))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p3 *1) +be *(0 +be *(0 +be *(0 +be *-2)))) +b *(0 +b *(0 +be *(0 +be *3)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +be *(0 +be *-2)))))))) +a *(((0 +b *(0 +b *(0 +b *((((0 +p3 *-2) +p1 *-2) +be *(0 +be *(0 +be *(0 +be *2)))) +b *(0 +b *(0 +be *(0 +be *-4))))))) +ai *(0 +ai *((0 +b *((0 +p1 *1) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *-2))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *2))))))) +a *(((0 +b *(0 +b *((0 +p1 *-2) +b *(0 +b *(0 +be *(0 +be *-6)))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *3)) +b *(0 +b *-6)))) +ai *(0 +ai *(0 +b *(0 +b *4)))))) +a *((0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-2))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *-4))) +ai *(0 +ai *(0 +b *1)))))))) =0 /\ ((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-1)))))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *(0 +p3 *(0 +p3 *1))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p3 *-4)))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *(0 +p3 *-2)))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *1)))))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p3 *2)))))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *2)))))))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *(0 +p3 *-1)))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *2))))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *-1))))))))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p1 *(0 +p3 *(0 +p3 *3))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *((0 +p3 *-6) +p1 *6)))))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *(0 +p3 *(0 +p3 *-4))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *-4)) +p1 *(0 +p3 *22)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-2))))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *(0 +p3 *8)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *4) +p1 *-1))))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *-4))))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-3)))))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *(0 +p3 *(0 +p3 *2))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *2)) +p1 *(0 +p3 *-26)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *4))))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *(0 +p3 *-3)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-4) +p1 *-10))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *2)))))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *1)))))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p3 *6)))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *(0 +p3 *4)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *4) +p1 *6))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-8) +be *(0 +be *(0 +be *(0 +be *-4)))))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *4)))))))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *(0 +p3 *-3)))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *6))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *-3)))))))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p1 *(0 +p1 *(0 +p3 *3))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *4)))))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *(0 +p3 *-4))) +p1 *(0 +p3 *(0 +p3 *-12))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *-5)) +p1 *((0 +p3 *60) +p1 *-16)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-4))))))))))) +b *(0 +b *(((0 +p3 *(0 +p3 *(0 +p3 *4))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *28)) +p1 *(0 +p3 *-44)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *6) +p1 *4))))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *(0 +p3 *-8)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-24) +p1 *4) +be *(0 +be *(0 +be *(0 +be *-1)))))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *4)))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p1 *(0 +p3 *(0 +p3 *6))) +be *(0 +be *(0 +be *(0 +be *((0 +p1 *((0 +p3 *-30) +p1 *14)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *2))))))))))) +b *(0 +b *(((0 +p3 *(0 +p3 *(0 +p3 *-4))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *-16)) +p1 *(0 +p3 *84)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-4) +p1 *-34))))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *(0 +p3 *4)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *20) +p1 *18) +be *(0 +be *(0 +be *(0 +be *8)))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *4) +be *(0 +be *(0 +be *(0 +be *-4)))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *-4))))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-3)))))))) +b *(0 +b *(((0 +p3 *(0 +p3 *(0 +p3 *1))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *10)) +p1 *(0 +p3 *-46)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *2) +p1 *12))))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *(0 +p3 *-4)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-40) +p1 *-22) +be *(0 +be *(0 +be *(0 +be *-6)))))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *5) +be *(0 +be *(0 +be *(0 +be *30)))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *-2))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p3 *6)))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *(0 +p3 *8)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *12) +p1 *6))))))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-16) +be *(0 +be *(0 +be *(0 +be *-12)))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *8))))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p3 *(0 +p3 *-3)))) +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p3 *6))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *(0 +be *-3))))))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *(0 +p1 *1))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p1 *((0 +p3 *(0 +p3 *-12)) +p1 *(0 +p3 *-12))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *((0 +p3 *32) +p1 *-16)))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *(0 +p3 *8))) +p1 *(0 +p3 *(0 +p3 *12))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *44)) +p1 *((0 +p3 *-172) +p1 *28)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *4) +p1 *24))))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *-48)) +p1 *(0 +p3 *40)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-48) +p1 *16) +be *(0 +be *(0 +be *(0 +be *-4)))))))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *40) +p1 *-4) +be *(0 +be *(0 +be *(0 +be *4)))))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p1 *(0 +p1 *(0 +p3 *6))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *8)))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *(0 +p3 *-4))) +p1 *(0 +p3 *(0 +p3 *-12))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *-22)) +p1 *((0 +p3 *196) +p1 *-33)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-2) +p1 *-40))))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *36)) +p1 *(0 +p3 *-104)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *44) +p1 *64) +be *(0 +be *(0 +be *(0 +be *10)))))))))) +b *(0 +b *(((0 +p3 *(0 +p3 *4)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-16) +p1 *-24) +be *(0 +be *(0 +be *(0 +be *-46)))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-8) +be *(0 +be *(0 +be *(0 +be *-16)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *4)))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *(0 +p3 *(0 +p3 *3))) +be *(0 +be *(0 +be *(0 +be *((0 +p1 *((0 +p3 *-46) +p1 *10)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *6))))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *-28)) +p1 *(0 +p3 *94)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-38) +p1 *-66) +be *(0 +be *(0 +be *(0 +be *-4)))))))))) +b *(0 +b *(((0 +p3 *(0 +p3 *-4)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *76) +p1 *35) +be *(0 +be *(0 +be *(0 +be *74)))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *8) +be *(0 +be *(0 +be *(0 +be *-48)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-4)))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-1)))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *14)) +p1 *(0 +p3 *-30)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *6) +p1 *12))))))) +b *(0 +b *(((0 +p3 *(0 +p3 *-3)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-72) +p1 *-14) +be *(0 +be *(0 +be *(0 +be *-18)))))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *6) +be *(0 +be *(0 +be *(0 +be *58)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-3)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p3 *2)))) +b *(0 +b *(((0 +p3 *(0 +p3 *4)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *12) +p1 *2))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-8) +be *(0 +be *(0 +be *(0 +be *-12)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *4)))))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p3 *(0 +p3 *-1)) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *2))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-1)))))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p1 *(0 +p1 *((0 +p3 *-12) +p1 *-4))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-3)))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *(0 +p3 *4))) +p1 *((0 +p3 *(0 +p3 *24)) +p1 *(0 +p3 *12))) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *(0 +p3 *24)) +p1 *((0 +p3 *-188) +p1 *40)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *4) +p1 *16))))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *-108)) +p1 *((0 +p3 *192) +p1 *-32)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-48) +p1 *-4) +be *(0 +be *(0 +be *(0 +be *-4)))))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *16)) +p1 *(0 +p3 *-16)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *108) +p1 *-40) +be *(0 +be *(0 +be *(0 +be *24)))))))) +b *(0 +b *(0 +be *(0 +be *((0 +p3 *-16) +be *(0 +be *(0 +be *(0 +be *-4))))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *(0 +p1 *2))))) +b *(0 +b *(((0 +p1 *((0 +p3 *(0 +p3 *-12)) +p1 *(0 +p3 *-12))) +be *(0 +be *(0 +be *(0 +be *((0 +p1 *((0 +p3 *94) +p1 *-28)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-8))))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *84)) +p1 *((0 +p3 *-360) +p1 *52)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *32) +p1 *128) +be *(0 +be *(0 +be *(0 +be *4)))))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *-8)) +p1 *(0 +p3 *48)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-76) +p1 *-36) +be *(0 +be *(0 +be *(0 +be *-96)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-32) +p1 *32) +be *(0 +be *(0 +be *(0 +be *44)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *40))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p1 *(0 +p1 *(0 +p3 *3))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *4)))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *-33)) +p1 *((0 +p3 *196) +p1 *-22)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-14) +p1 *-72) +be *(0 +be *(0 +be *(0 +be *-1)))))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *8)) +p1 *(0 +p3 *-60)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *142) +p1 *88) +be *(0 +be *(0 +be *(0 +be *78)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-4) +p1 *-48) +be *(0 +be *(0 +be *(0 +be *-217)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-4))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p1 *((0 +p3 *-26) +p1 *2)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *6))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *-16)) +p1 *(0 +p3 *32)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-66) +p1 *-38) +be *(0 +be *(0 +be *(0 +be *-12)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *76) +p1 *20) +be *(0 +be *(0 +be *(0 +be *134)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-60))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((((0 +p3 *(0 +p3 *6)) +p1 *(0 +p3 *-6)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *6) +p1 *4))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-40) +p1 *-2) +be *(0 +be *(0 +be *(0 +be *-18)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *34))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p3 *4))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-4))))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *(0 +p1 *-4))))) +b *(0 +b *(((0 +p1 *((0 +p3 *(0 +p3 *12)) +p1 *((0 +p3 *24) +p1 *4))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *((0 +p3 *-60) +p1 *8)))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *-104)) +p1 *((0 +p3 *312) +p1 *-80)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-40) +p1 *-28))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *64)) +p1 *((0 +p3 *-80) +p1 *16)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *144) +p1 *-100) +be *(0 +be *(0 +be *(0 +be *40)))))))) +b *(0 +b *(0 +be *(0 +be *(((0 +p3 *-64) +p1 *16) +be *(0 +be *(0 +be *(0 +be *-40)))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *(0 +p1 *((0 +p3 *-12) +p1 *-4))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-4)))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *52)) +p1 *((0 +p3 *-360) +p1 *84)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *20) +p1 *76))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *-60)) +p1 *((0 +p3 *208) +p1 *-36)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-100) +p1 *-56) +be *(0 +be *(0 +be *(0 +be *-76)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-56) +p1 *64) +be *(0 +be *(0 +be *(0 +be *216)))))) +b *(0 +b *((((0 +p3 *16) +p1 *-16) +be *(0 +be *(0 +be *(0 +be *68)))) +b *(0 +b *(0 +be *(0 +be *-16)))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *(0 +p1 *(0 +p1 *1))) +b *(0 +b *((0 +be *(0 +be *((0 +p1 *((0 +p3 *84) +p1 *-16)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-16))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *40)) +p1 *((0 +p3 *-188) +p1 *24)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *88) +p1 *142) +be *(0 +be *(0 +be *(0 +be *34)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-56) +p1 *-92) +be *(0 +be *(0 +be *(0 +be *-348)))))) +b *(0 +b *((((0 +p3 *-16) +p1 *32) +be *(0 +be *(0 +be *(0 +be *156)))) +b *(0 +b *(0 +be *(0 +be *16)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((((0 +p3 *(0 +p3 *-16)) +p1 *((0 +p3 *60) +p1 *-5)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-22) +p1 *-40) +be *(0 +be *(0 +be *(0 +be *-3)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *128) +p1 *32) +be *(0 +be *(0 +be *(0 +be *134)))))) +b *(0 +b *((((0 +p3 *-12) +p1 *-20) +be *(0 +be *(0 +be *(0 +be *-244)))) +b *(0 +b *(0 +be *(0 +be *12)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p1 *(0 +p3 *-4)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *2))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-34) +p1 *-4) +be *(0 +be *(0 +be *(0 +be *-12)))))) +b *(0 +b *((((0 +p3 *16) +p1 *4) +be *(0 +be *(0 +be *(0 +be *78)))) +b *(0 +b *(0 +be *(0 +be *-16)))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p3 *2))) +b *(0 +b *(((0 +p3 *-4) +be *(0 +be *(0 +be *(0 +be *-6)))) +b *(0 +b *(0 +be *(0 +be *4)))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *(0 +p1 *((0 +p3 *12) +p1 *8))) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *(0 +p1 *-4)))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *(0 +p3 *-36)) +p1 *((0 +p3 *208) +p1 *-60)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-20) +p1 *-12))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *96)) +p1 *((0 +p3 *-160) +p1 *64)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *136) +p1 *-112) +be *(0 +be *(0 +be *(0 +be *20)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-112) +p1 *80) +be *(0 +be *(0 +be *(0 +be *-100)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *16))))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *(0 +p1 *-4))) +b *(0 +b *((0 +be *(0 +be *((0 +p1 *((0 +p3 *-104) +p1 *36)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *6))))))) +b *(0 +b *((((0 +p3 *(0 +p3 *-80)) +p1 *((0 +p3 *312) +p1 *-104)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *-92) +p1 *-56) +be *(0 +be *(0 +be *(0 +be *-16)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-48) +p1 *16) +be *(0 +be *(0 +be *(0 +be *284)))))) +b *(0 +b *((((0 +p3 *80) +p1 *-64) +be *(0 +be *(0 +be *(0 +be *-48)))) +b *(0 +b *(0 +be *(0 +be *-64))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *-3)))) +b *(0 +b *((((0 +p3 *(0 +p3 *28)) +p1 *((0 +p3 *-172) +p1 *44)) +be *(0 +be *(0 +be *(0 +be *(((0 +p3 *35) +p1 *76) +be *(0 +be *(0 +be *(0 +be *4)))))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-56) +p1 *-100) +be *(0 +be *(0 +be *(0 +be *-244)))))) +b *(0 +b *((((0 +p3 *-64) +p1 *96) +be *(0 +be *(0 +be *(0 +be *436)))) +b *(0 +b *(0 +be *(0 +be *-16))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p1 *((0 +p3 *22) +p1 *-4)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *-8))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *64) +p1 *44) +be *(0 +be *(0 +be *(0 +be *58)))))) +b *(0 +b *((((0 +p3 *-28) +p1 *-40) +be *(0 +be *(0 +be *(0 +be *-348)))) +b *(0 +b *(0 +be *(0 +be *136))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-10) +p1 *-4) +be *(0 +be *(0 +be *(0 +be *-3)))))) +b *(0 +b *((((0 +p3 *24) +p1 *4) +be *(0 +be *(0 +be *(0 +be *74)))) +b *(0 +b *(0 +be *(0 +be *-76))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(((0 +p3 *-2) +be *(0 +be *(0 +be *(0 +be *-4)))) +b *(0 +b *(0 +be *(0 +be *10))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *(0 +p1 *4))) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *((0 +p3 *48) +p1 *-8)))) +b *(0 +b *((((0 +p3 *(0 +p3 *64)) +p1 *((0 +p3 *-160) +p1 *96)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *96) +p1 *-64))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-128) +p1 *160) +be *(0 +be *(0 +be *(0 +be *-96)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *64)))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *4)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-32)) +p1 *((0 +p3 *192) +p1 *-108)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *-48) +p1 *-4))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *16) +p1 *-48) +be *(0 +be *(0 +be *(0 +be *136)))))) +b *(0 +b *((((0 +p3 *160) +p1 *-112) +be *(0 +be *(0 +be *(0 +be *-208)))) +b *(0 +b *(0 +be *(0 +be *-96)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *((0 +p3 *-44) +p1 *28)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *5))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-36) +p1 *-76) +be *(0 +be *(0 +be *(0 +be *-60)))))) +b *(0 +b *((((0 +p3 *-112) +p1 *136) +be *(0 +be *(0 +be *(0 +be *436)))) +b *(0 +b *((0 +be *(0 +be *-160)) +b *(0 +b *16)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *(0 +p1 *-2)) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *18) +p1 *20) +be *(0 +be *(0 +be *(0 +be *8)))))) +b *(0 +b *((((0 +p3 *-4) +p1 *-48) +be *(0 +be *(0 +be *(0 +be *-217)))) +b *(0 +b *((0 +be *(0 +be *284)) +b *(0 +b *-32)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((((0 +p3 *4) +p1 *6) +be *(0 +be *(0 +be *(0 +be *30)))) +b *(0 +b *((0 +be *(0 +be *-96)) +b *(0 +b *20)))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *-1)))) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *-4)))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *(0 +p1 *4)))) +b *(0 +b *((((0 +p3 *(0 +p3 *16)) +p1 *((0 +p3 *-80) +p1 *64)) +be *(0 +be *(0 +be *(0 +be *((0 +p3 *32) +p1 *-16))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-112) +p1 *160) +be *(0 +be *(0 +be *(0 +be *-32)))))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *96))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p1 *((0 +p3 *40) +p1 *-48)) +be *(0 +be *(0 +be *(0 +be *(0 +p1 *8))))) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *64) +p1 *-56) +be *(0 +be *(0 +be *(0 +be *12)))))) +b *(0 +b *((((0 +p3 *160) +p1 *-128) +be *(0 +be *(0 +be *(0 +be *-160)))) +b *(0 +b *(0 +be *(0 +be *-80))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *8)) +b *(0 +b *((0 +be *(0 +be *(((0 +p3 *-24) +p1 *-16) +be *(0 +be *(0 +be *(0 +be *-3)))))) +b *(0 +b *((((0 +p3 *-100) +p1 *144) +be *(0 +be *(0 +be *(0 +be *156)))) +b *(0 +b *((0 +be *(0 +be *-208)) +b *(0 +b *64))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((((0 +p3 *16) +p1 *-48) +be *(0 +be *(0 +be *(0 +be *-48)))) +b *(0 +b *((0 +be *(0 +be *216)) +b *(0 +b *-96))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((((0 +p3 *-1) +p1 *4) +be *(0 +be *(0 +be *(0 +be *4)))) +b *(0 +b *((0 +be *(0 +be *-46)) +b *(0 +b *40))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *-4))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *((0 +p3 *-16) +p1 *16)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-64) +p1 *80))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *64)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *(0 +p1 *-8)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *32) +p1 *-32))) +b *(0 +b *((((0 +p3 *80) +p1 *-112) +be *(0 +be *(0 +be *(0 +be *-16)))) +b *(0 +b *(0 +be *(0 +be *-80)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *4))) +b *(0 +b *((((0 +p3 *-40) +p1 *108) +be *(0 +be *(0 +be *(0 +be *-4)))) +b *(0 +b *((0 +be *(0 +be *-48)) +b *(0 +b *96)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((((0 +p3 *4) +p1 *-24) +be *(0 +be *(0 +be *(0 +be *-2)))) +b *(0 +b *((0 +be *(0 +be *44)) +b *(0 +b *-100)))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *1) +b *(0 +b *((0 +be *(0 +be *-4)) +b *(0 +b *24)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-1)))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-16) +p1 *16))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *16))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-8))) +b *(0 +b *((((0 +p3 *16) +p1 *-64) +be *(0 +be *(0 +be *(0 +be *16)))) +b *(0 +b *(0 +be *(0 +be *-96))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((((0 +p3 *-4) +p1 *40) +be *(0 +be *(0 +be *(0 +be *-4)))) +b *(0 +b *((0 +be *(0 +be *68)) +b *(0 +b *64))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +p1 *-4) +b *(0 +b *((0 +be *(0 +be *-16)) +b *(0 +b *-40))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *1)) +b *(0 +b *4))))))))))))) +a *((0 +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *-16) +b *(0 +b *(0 +be *(0 +be *-64)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *4) +b *(0 +b *((0 +be *(0 +be *40)) +b *(0 +b *16)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *-4)) +b *(0 +b *-4)))))))))))) +a *(0 +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-16))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *4)))))))))))))))))))))) =0))) \/ ~((0 +b *(0 +b *(0 +b *-1))) +ae *(0 +ae *(0 +b *2))) +a *((0 +b *(0 +b *1)) +a *(0 +b *2)) =0 /\ (((0 +b *((0 +p2 *(0 +p2 *(0 +p2 *-1))) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-2)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-1) +p1 *-1)))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *1)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *2) +b *(0 +b *(0 +b *(0 +b *1))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *7)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *8) +p1 *6) +b *(0 +b *(0 +b *(0 +b *1))))))))))) +ai *(0 +ai *(0 +b *((0 +p2 *(0 +p2 *-2)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-10) +b *(0 +b *(0 +b *(0 +b *-8))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-15) +p1 *-12) +b *(0 +b *(0 +b *(0 +b *-6))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *12) +b *(0 +b *(0 +b *(0 +b *21))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *((0 +p1 *8) +b *(0 +b *(0 +b *(0 +b *9))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-18))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *2)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *2) +p1 *3))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-1)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-4) +b *(0 +b *(0 +b *(0 +b *-3)))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-8) +p1 *-12) +b *(0 +b *(0 +b *(0 +b *-2)))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *10) +b *(0 +b *(0 +b *(0 +b *16)))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +b *((0 +p1 *12) +b *(0 +b *(0 +b *(0 +b *6)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-21)))))))))))) +a *((((0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *4)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *4) +p1 *3)))))))) +ai *(0 +ai *(0 +b *((0 +p2 *(0 +p2 *-2)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-6) +b *(0 +b *(0 +b *(0 +b *-3))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-20) +p1 *-18) +b *(0 +b *(0 +b *(0 +b *-4))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *20) +b *(0 +b *(0 +b *(0 +b *24))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(((0 +p2 *4) +p1 *24) +b *(0 +b *(0 +b *(0 +b *16))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-42))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-4))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-6) +p1 *-11))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *8) +b *(0 +b *(0 +b *(0 +b *11)))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *4) +p1 *24) +b *(0 +b *(0 +b *(0 +b *6)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-32)))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-7) +p1 *-6)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *8) +b *(0 +b *(0 +b *(0 +b *6))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(((0 +p2 *8) +p1 *24) +b *(0 +b *(0 +b *(0 +b *7))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-32))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-8))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *4) +p1 *12))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-12)))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))))) +a *(((0 +b *(0 +b *(0 +b *((0 +p2 *4) +p1 *8)))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-8))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))))))))) =0 /\ ((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *1)))) +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +p3 *-1)))))))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-2)))) +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-2))) +b *(0 +b *(0 +p3 *6)))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *4))) +b *(0 +b *((0 +p3 *-12) +b *(0 +b *(0 +be *(0 +be *1))))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *((0 +p3 *8) +b *(0 +b *(0 +be *(0 +be *-2))))))))))))) +a *((((0 +p2 *(0 +p2 *(0 +p2 *1))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-1)))) +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-2))) +b *(0 +b *((0 +p3 *3) +p2 *-1))))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +p2 *(0 +p2 *-3)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *10))) +b *(0 +b *(((0 +p3 *-12) +p2 *4) +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *1)))))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-8))) +b *(0 +b *(((0 +p3 *12) +p2 *-1) +b *(0 +b *((0 +be *(0 +be *-9)) +b *(0 +b *-4)))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *3)))))))))))) +a *(((0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-2)))) +b *(0 +b *((0 +p2 *(0 +p2 *-2)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *4))) +b *(0 +b *(((0 +p3 *3) +p2 *2) +b *(0 +b *(0 +be *(0 +be *1))))))))))) +ae *(0 +ae *((0 +b *((0 +p2 *(0 +p2 *4)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-4))) +b *(0 +b *((0 +p3 *-18) +b *(0 +b *((0 +be *(0 +be *-10)) +b *(0 +b *-2))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(((0 +p3 *24) +p2 *-8) +b *(0 +b *((0 +be *(0 +be *18)) +b *(0 +b *2))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *-8)) +b *(0 +b *4))))))))))) +a *(((0 +b *(0 +b *((0 +p2 *(0 +p2 *2)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *6))) +b *(0 +b *(((0 +p3 *-11) +p2 *4) +b *(0 +b *(0 +be *(0 +be *-3)))))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-16))) +b *(0 +b *(((0 +p3 *24) +p2 *-16) +b *(0 +b *((0 +be *(0 +be *6)) +b *(0 +b *-4)))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +p2 *4) +b *(0 +b *((0 +be *(0 +be *4)) +b *(0 +b *14)))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))))))) +a *(((0 +b *((0 +p2 *(0 +p2 *4)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-8))) +b *(0 +b *(((0 +p3 *-6) +p2 *-6) +b *(0 +b *(0 +be *(0 +be *-3))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(((0 +p3 *24) +p2 *-4) +b *(0 +b *((0 +be *(0 +be *26)) +b *(0 +b *6))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-24))))))))) +a *(((0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-8))) +b *(0 +b *(((0 +p3 *12) +p2 *-7) +b *(0 +b *(0 +be *(0 +be *11)))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +p2 *8) +b *(0 +b *((0 +be *(0 +be *-16)) +b *(0 +b *7)))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *-8)))))))) +a *(((0 +b *(0 +b *(0 +b *(((0 +p3 *8) +p2 *4) +b *(0 +b *(0 +be *(0 +be *6))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *-24)) +b *(0 +b *-4))))))) +a *(((0 +b *(0 +b *((0 +p2 *4) +b *(0 +b *(0 +be *(0 +be *-12)))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))) +a *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-8)))))))))))) =0) \/ ~((0 +b *(0 +b *1)) +ae *(0 +ae *-1)) +a *(0 +b *-2) =0 /\ ((((0 +b *(0 +b *(0 +b *((0 +p2 *-1) +b *(0 +b *(0 +b *(0 +b *4))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-3))))))) +ae *(0 +ae *(((0 +b *((0 +p2 *1) +b *(0 +b *(0 +b *(0 +b *-11))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *7))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *8))) +ai *(0 +ai *(0 +b *-4))))))) +a *((((0 +b *(0 +b *((0 +p2 *2) +b *(0 +b *(0 +b *(0 +b *-12)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *11)))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +b *16)))) +ai *(0 +ai *(0 +b *(0 +b *-13)))))) +a *(((0 +ai *(0 +ai *(0 +b *(0 +b *(0 +b *-8))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *14))) +ai *(0 +ai *(0 +b *-2))) +ae *(0 +ae *(0 +b *-1))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *16)))) +ai *(0 +ai *(0 +b *(0 +b *-4)))) +ae *(0 +ae *(0 +b *(0 +b *-4)))))) =0 /\ (((0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-3) +p1 *1))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *1) +b *(0 +b *(0 +b *(0 +b *-1)))))))) +ae *(0 +ae *(((0 +b *(0 +b *(((0 +p2 *4) +p1 *-2) +b *(0 +b *(0 +b *(0 +b *3)))))) +ai *(0 +ai *((0 +p2 *-1) +b *(0 +b *(0 +b *(0 +b *1)))))) +ae *(0 +ae *((0 +p1 *1) +b *(0 +b *(0 +b *(0 +b *-4)))))))) +a *((((0 +b *(0 +b *(0 +b *((0 +p2 *5) +p1 *-4)))) +ai *(0 +ai *(0 +b *((0 +p2 *-2) +b *(0 +b *(0 +b *(0 +b *4))))))) +ae *(0 +ae *((0 +b *((0 +p1 *4) +b *(0 +b *(0 +b *(0 +b *-5))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *-2))))))) +a *(((0 +b *(0 +b *((0 +p2 *2) +p1 *4))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *-2))))))) =0 /\ (((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-1))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +be *(0 +be *3))))) +ae *(0 +ae *(0 +b *(0 +be *(0 +be *-2))))))) +a *(((0 +b *(0 +b *((0 +p2 *1) +b *(0 +b *(0 +be *(0 +be *5)))))) +ae *(0 +ae *(((0 +p2 *-1) +b *(0 +b *((0 +be *(0 +be *-9)) +b *(0 +b *1)))) +ae *(0 +ae *((0 +be *(0 +be *2)) +b *(0 +b *-2)))))) +a *(((0 +b *((0 +p2 *-2) +b *(0 +b *(0 +be *(0 +be *-8))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *6)) +b *(0 +b *-4))) +ae *(0 +ae *(0 +b *4))))) +a *((0 +b *(0 +b *(0 +be *(0 +be *4)))) +ae *(0 +ae *((0 +b *(0 +b *4)) +ae *(0 +ae *-1)))))) =0 /\ ((0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *1))) +b *(0 +b *(0 +p3 *1))))) +ae *(0 +ae *(((0 +be *(0 +be *(0 +p2 *-1))) +b *(0 +b *((0 +p3 *-2) +b *(0 +b *(0 +be *(0 +be *-1)))))) +ae *(0 +ae *((0 +p3 *1) +b *(0 +b *(0 +be *(0 +be *1)))))))) +a *(((0 +b *((0 +be *(0 +be *(0 +p2 *-2))) +b *(0 +b *((0 +p3 *-4) +p2 *1)))) +ae *(0 +ae *((0 +b *(((0 +p3 *4) +p2 *-2) +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *-1))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *2))))))) +a *(((0 +b *(0 +b *(((0 +p3 *4) +p2 *-3) +b *(0 +b *(0 +be *(0 +be *-1)))))) +ae *(0 +ae *(((0 +p2 *2) +b *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *3)))) +ae *(0 +ae *((0 +be *(0 +be *-1)) +b *(0 +b *-2)))))) +a *(((0 +b *((0 +p2 *2) +b *(0 +b *(0 +be *(0 +be *4))))) +ae *(0 +ae *(0 +b *((0 +be *(0 +be *-4)) +b *(0 +b *-2))))) +a *(0 +b *(0 +b *(0 +be *(0 +be *-4))))))) =0 \/ ~((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-1))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +be *(0 +be *3))))) +ae *(0 +ae *(0 +b *(0 +be *(0 +be *-2))))))) +a *(((0 +b *(0 +b *((0 +p2 *1) +b *(0 +b *(0 +be *(0 +be *5)))))) +ae *(0 +ae *(((0 +p2 *-1) +b *(0 +b *((0 +be *(0 +be *-9)) +b *(0 +b *1)))) +ae *(0 +ae *((0 +be *(0 +be *2)) +b *(0 +b *-2)))))) +a *(((0 +b *((0 +p2 *-2) +b *(0 +b *(0 +be *(0 +be *-8))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *6)) +b *(0 +b *-4))) +ae *(0 +ae *(0 +b *4))))) +a *((0 +b *(0 +b *(0 +be *(0 +be *4)))) +ae *(0 +ae *((0 +b *(0 +b *4)) +ae *(0 +ae *-1)))))) =0 /\ ((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *1)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p3 *2)))) +b *(0 +b *((0 +p3 *(0 +p3 *1)) +b *(0 +b *(0 +be *(0 +be *(0 +p3 *-1))))))))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *-3)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p3 *-8)))) +b *(0 +b *(((0 +p3 *(0 +p3 *-5)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-2))))) +b *(0 +b *(0 +be *(0 +be *(0 +p3 *5))))))))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *3)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p3 *12)))) +b *(0 +b *(((0 +p3 *(0 +p3 *10)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *6))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *-11))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *1)))))))))))))) +ae *(0 +ae *(((0 +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *-1)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p3 *-8)))) +b *(0 +b *(((0 +p3 *(0 +p3 *-10)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-6))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *13))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-3)))))))))))) +ae *(0 +ae *(((0 +be *(0 +be *(0 +p2 *(0 +p3 *2)))) +b *(0 +b *(((0 +p3 *(0 +p3 *5)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *2))))) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *-8))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *3)))))))))) +ae *(0 +ae *((0 +p3 *(0 +p3 *-1)) +b *(0 +b *((0 +be *(0 +be *(0 +p3 *2))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-1)))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *-6)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *-16) +p2 *1)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-10)) +p2 *(0 +p3 *3)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-2))))) +b *(0 +b *(0 +be *(0 +be *((0 +p3 *10) +p2 *-1)))))))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *12)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *48) +p2 *-4)))) +b *(0 +b *((((0 +p3 *(0 +p3 *40)) +p2 *(0 +p3 *-15)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *22))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-42) +p2 *3))) +b *(0 +b *(((0 +p3 *-1) +be *(0 +be *(0 +be *(0 +be *2)))) +b *(0 +b *(0 +be *(0 +be *1))))))))))))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *-6)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *-48) +p2 *5)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-60)) +p2 *(0 +p3 *27)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-42))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *76) +p2 *-1))) +b *(0 +b *(((0 +p3 *4) +be *(0 +be *(0 +be *(0 +be *-16)))) +b *(0 +b *(0 +be *(0 +be *-4))))))))))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *16) +p2 *-2)))) +b *(0 +b *((((0 +p3 *(0 +p3 *40)) +p2 *(0 +p3 *-21)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *26))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-70) +p2 *-3))) +b *(0 +b *(((0 +p3 *-5) +be *(0 +be *(0 +be *(0 +be *30)))) +b *(0 +b *(0 +be *(0 +be *5))))))))))) +ae *(0 +ae *((0 +b *((((0 +p3 *(0 +p3 *-10)) +p2 *(0 +p3 *6)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-4))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *30) +p2 *2))) +b *(0 +b *(((0 +p3 *2) +be *(0 +be *(0 +be *(0 +be *-20)))) +b *(0 +b *(0 +be *(0 +be *-2))))))))) +ae *(0 +ae *(0 +b *((0 +be *(0 +be *(0 +p3 *-4))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *4))))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *(0 +p2 *1))) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *12)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *48) +p2 *-5)))) +b *(0 +b *((((0 +p3 *(0 +p3 *40)) +p2 *((0 +p3 *-25) +p2 *2)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *16))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-41) +p2 *9))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *1)))))))))))))))) +ae *(0 +ae *((0 +b *(0 +b *(((0 +p2 *(0 +p2 *(0 +p2 *-2))) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *-12)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *-96) +p2 *14)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-120)) +p2 *((0 +p3 *97) +p2 *-9)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-86))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *141) +p2 *-21))) +b *(0 +b *((((0 +p3 *9) +p2 *-2) +be *(0 +be *(0 +be *(0 +be *-23)))) +b *(0 +b *(0 +be *(0 +be *-9)))))))))))))) +ae *(0 +ae *(((0 +p2 *(0 +p2 *(0 +p2 *1))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *48) +p2 *-9)))) +b *(0 +b *((((0 +p3 *(0 +p3 *120)) +p2 *((0 +p3 *-123) +p2 *12)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *102))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-203) +p2 *3))) +b *(0 +b *((((0 +p3 *-26) +p2 *8) +be *(0 +be *(0 +be *(0 +be *93)))) +b *(0 +b *(0 +be *(0 +be *26)))))))))))) +ae *(0 +ae *((0 +b *(0 +b *((((0 +p3 *(0 +p3 *-40)) +p2 *((0 +p3 *55) +p2 *-5)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-34))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *137) +p2 *13))) +b *(0 +b *((((0 +p3 *17) +p2 *-10) +be *(0 +be *(0 +be *(0 +be *-115)))) +b *(0 +b *(0 +be *(0 +be *-17)))))))))) +ae *(0 +ae *((((0 +p2 *(0 +p3 *-4)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *2))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-36) +p2 *-4))) +b *(0 +b *((((0 +p3 *4) +p2 *4) +be *(0 +be *(0 +be *(0 +be *50)))) +b *(0 +b *(0 +be *(0 +be *-4)))))))) +ae *(0 +ae *((0 +be *(0 +be *(0 +p3 *2))) +b *(0 +b *(((0 +p3 *-4) +be *(0 +be *(0 +be *(0 +be *-6)))) +b *(0 +b *(0 +be *(0 +be *4)))))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *(0 +p2 *-4))) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *(0 +p2 *-8)))))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *-64) +p2 *6)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-80)) +p2 *((0 +p3 *80) +p2 *-14)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-48))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *90) +p2 *-34))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-10))))))))))))))) +ae *(0 +ae *((0 +b *((0 +p2 *(0 +p2 *(0 +p2 *4))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *64) +p2 *-8)))) +b *(0 +b *((((0 +p3 *(0 +p3 *160)) +p2 *((0 +p3 *-222) +p2 *44)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *148))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-248) +p2 *60))) +b *(0 +b *((((0 +p3 *-34) +p2 *14) +be *(0 +be *(0 +be *(0 +be *106)))) +b *(0 +b *(0 +be *(0 +be *32))))))))))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-2)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-80)) +p2 *((0 +p3 *168) +p2 *-34)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-96))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *274) +p2 *-2))) +b *(0 +b *((((0 +p3 *67) +p2 *-40) +be *(0 +be *(0 +be *(0 +be *-264)))) +b *(0 +b *(0 +be *(0 +be *-55))))))))))) +ae *(0 +ae *((0 +b *(((0 +p2 *((0 +p3 *-26) +p2 *4)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *12))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-124) +p2 *-20))) +b *(0 +b *((((0 +p3 *-14) +p2 *30) +be *(0 +be *(0 +be *(0 +be *214)))) +b *(0 +b *(0 +be *(0 +be *-12))))))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *((0 +p3 *16) +p2 *4))) +b *(0 +b *((((0 +p3 *-17) +p2 *-4) +be *(0 +be *(0 +be *(0 +be *-58)))) +b *(0 +b *(0 +be *(0 +be *41))))))) +ae *(0 +ae *(0 +b *(((0 +p3 *2) +be *(0 +be *(0 +be *(0 +be *4)))) +b *(0 +b *(0 +be *(0 +be *-10))))))))))))))) +a *(((0 +b *(0 +b *((0 +p2 *(0 +p2 *(0 +p2 *4))) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *((0 +p3 *32) +p2 *4)))) +b *(0 +b *((((0 +p3 *(0 +p3 *80)) +p2 *((0 +p3 *-120) +p2 *36)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *64))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-120) +p2 *72))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *40)))))))))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-8)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-80)) +p2 *((0 +p3 *204) +p2 *-70)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-104))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *264) +p2 *-98))) +b *(0 +b *((((0 +p3 *72) +p2 *-38) +be *(0 +be *(0 +be *(0 +be *-248)))) +b *(0 +b *(0 +be *(0 +be *-56)))))))))))) +ae *(0 +ae *((0 +b *(0 +b *(((0 +p2 *((0 +p3 *-60) +p2 *24)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *24))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-212) +p2 *8))) +b *(0 +b *((((0 +p3 *-99) +p2 *74) +be *(0 +be *(0 +be *(0 +be *393)))) +b *(0 +b *((0 +be *(0 +be *23)) +b *(0 +b *2)))))))))) +ae *(0 +ae *(((0 +p2 *(0 +p2 *-2)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *52) +p2 *10))) +b *(0 +b *((((0 +p3 *14) +p2 *-34) +be *(0 +be *(0 +be *(0 +be *-199)))) +b *(0 +b *((0 +be *(0 +be *106)) +b *(0 +b *-8)))))))) +ae *(0 +ae *((0 +b *(0 +b *((((0 +p3 *1) +p2 *6) +be *(0 +be *(0 +be *(0 +be *31)))) +b *(0 +b *((0 +be *(0 +be *-69)) +b *(0 +b *10)))))) +ae *(0 +ae *((0 +be *(0 +be *(0 +be *(0 +be *-1)))) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *-4)))))))))))))) +a *(((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-8)))) +b *(0 +b *((((0 +p3 *(0 +p3 *-32)) +p2 *((0 +p3 *80) +p2 *-40)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *-32))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *112) +p2 *-96))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-80))))))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(((0 +p2 *((0 +p3 *-56) +p2 *40)) +be *(0 +be *(0 +be *(0 +be *(0 +p2 *16))))) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-192) +p2 *108))) +b *(0 +b *((((0 +p3 *-96) +p2 *54) +be *(0 +be *(0 +be *(0 +be *304)))) +b *(0 +b *(0 +be *(0 +be *50))))))))))) +ae *(0 +ae *((0 +b *((0 +p2 *(0 +p2 *-8)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *88) +p2 *-24))) +b *(0 +b *((((0 +p3 *106) +p2 *-80) +be *(0 +be *(0 +be *(0 +be *-294)))) +b *(0 +b *((0 +be *(0 +be *55)) +b *(0 +b *-14))))))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *(0 +p2 *4))) +b *(0 +b *((((0 +p3 *-32) +p2 *38) +be *(0 +be *(0 +be *(0 +be *84)))) +b *(0 +b *((0 +be *(0 +be *-130)) +b *(0 +b *40))))))) +ae *(0 +ae *((0 +b *((((0 +p3 *2) +p2 *-4) +be *(0 +be *(0 +be *(0 +be *-6)))) +b *(0 +b *((0 +be *(0 +be *39)) +b *(0 +b *-30))))) +ae *(0 +ae *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *4))))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *((0 +p3 *-16) +p2 *16)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *-80) +p2 *80))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *80)))))))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +p2 *(0 +p2 *-8)) +b *(0 +b *((0 +be *(0 +be *((0 +p3 *80) +p2 *-72))) +b *(0 +b *((((0 +p3 *80) +p2 *-52) +be *(0 +be *(0 +be *(0 +be *-176)))) +b *(0 +b *(0 +be *(0 +be *-32)))))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *16))) +b *(0 +b *((((0 +p3 *-68) +p2 *73) +be *(0 +be *(0 +be *(0 +be *92)))) +b *(0 +b *((0 +be *(0 +be *-33)) +b *(0 +b *36)))))))) +ae *(0 +ae *((0 +b *(0 +b *((((0 +p3 *8) +p2 *-22) +be *(0 +be *(0 +be *(0 +be *-12)))) +b *(0 +b *((0 +be *(0 +be *30)) +b *(0 +b *-65)))))) +ae *(0 +ae *(((0 +p2 *1) +b *(0 +b *((0 +be *(0 +be *-1)) +b *(0 +b *22)))) +ae *(0 +ae *(0 +b *(0 +b *-1)))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p3 *32) +p2 *-32))) +b *(0 +b *(0 +be *(0 +be *(0 +be *(0 +be *-32))))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *16))) +b *(0 +b *((((0 +p3 *-32) +p2 *40) +be *(0 +be *(0 +be *(0 +be *32)))) +b *(0 +b *(0 +be *(0 +be *48))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *((((0 +p3 *8) +p2 *-36) +be *(0 +be *(0 +be *(0 +be *-8)))) +b *(0 +b *((0 +be *(0 +be *-66)) +b *(0 +b *-40))))))) +ae *(0 +ae *((0 +b *((0 +p2 *4) +b *(0 +b *((0 +be *(0 +be *32)) +b *(0 +b *36))))) +ae *(0 +ae *(0 +b *((0 +be *(0 +be *-2)) +b *(0 +b *-4))))))))))) +a *((0 +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-16) +b *(0 +b *(0 +be *(0 +be *-64)))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +p2 *4) +b *(0 +b *((0 +be *(0 +be *68)) +b *(0 +b *16)))))) +ae *(0 +ae *(0 +b *(0 +b *((0 +be *(0 +be *-8)) +b *(0 +b *-4)))))))))) +a *(0 +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *32))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-8))))))))))))))))) =0) \/ ~(((0 +b *(0 +b *(0 +b *((0 +p2 *-1) +b *(0 +b *(0 +b *(0 +b *4))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-3))))))) +ae *(0 +ae *(((0 +b *((0 +p2 *1) +b *(0 +b *(0 +b *(0 +b *-11))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *7))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *8))) +ai *(0 +ai *(0 +b *-4))))))) +a *((((0 +b *(0 +b *((0 +p2 *2) +b *(0 +b *(0 +b *(0 +b *-12)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *11)))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *(0 +b *16)))) +ai *(0 +ai *(0 +b *(0 +b *-13)))))) +a *(((0 +ai *(0 +ai *(0 +b *(0 +b *(0 +b *-8))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *14))) +ai *(0 +ai *(0 +b *-2))) +ae *(0 +ae *(0 +b *-1))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *16)))) +ai *(0 +ai *(0 +b *(0 +b *-4)))) +ae *(0 +ae *(0 +b *(0 +b *-4)))))) =0 /\ (((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-1)))) +b *(0 +b *((0 +p2 *(0 +p3 *-1)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *1) +p1 *1))) +b *(0 +b *(0 +p3 *4)))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-2))) +b *(0 +b *((0 +p3 *-3) +b *(0 +b *(0 +be *(0 +be *-1))))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *2)))) +b *(0 +b *((0 +p2 *(0 +p3 *3)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-1) +p1 *-5))) +b *(0 +b *((0 +p3 *-19) +b *(0 +b *(0 +be *(0 +be *-1))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *6))) +b *(0 +b *((0 +p3 *13) +b *(0 +b *(0 +be *(0 +be *7))))))))))))) +ae *(0 +ae *(((0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-1)))) +b *(0 +b *((0 +p2 *(0 +p3 *-3)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-1) +p1 *9))) +b *(0 +b *((0 +p3 *34) +b *(0 +b *(0 +be *(0 +be *2))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-6))) +b *(0 +b *((0 +p3 *-21) +b *(0 +b *(0 +be *(0 +be *-15))))))))))) +ae *(0 +ae *(((0 +b *((0 +p2 *(0 +p3 *1)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *1) +p1 *-7))) +b *(0 +b *((0 +p3 *-27) +b *(0 +b *(0 +be *(0 +be *-1))))))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *(0 +p2 *2))) +b *(0 +b *((0 +p3 *15) +b *(0 +b *(0 +be *(0 +be *13))))))))) +ae *(0 +ae *((0 +b *((0 +be *(0 +be *(0 +p1 *2))) +b *(0 +b *(0 +p3 *8)))) +ai *(0 +ai *(0 +b *((0 +p3 *-4) +b *(0 +b *(0 +be *(0 +be *-4))))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *4)))) +b *(0 +b *(((0 +p2 *((0 +p3 *6) +p2 *2)) +p1 *(0 +p2 *-1)) +b *(0 +b *((0 +be *(0 +be *(0 +p1 *-9))) +b *(0 +b *((0 +p3 *-28) +p2 *4))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-1)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *10))) +b *(0 +b *(((0 +p3 *23) +p2 *-2) +b *(0 +b *(0 +be *(0 +be *9)))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-4)))) +b *(0 +b *(((0 +p2 *((0 +p3 *-12) +p2 *-4)) +p1 *(0 +p2 *3)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-16) +p1 *35))) +b *(0 +b *((((0 +p3 *100) +p2 *-18) +p1 *-1) +b *(0 +b *(0 +b *(0 +b *-4)))))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *(0 +p2 *2)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-18))) +b *(0 +b *(((0 +p3 *-75) +p2 *10) +b *(0 +b *((0 +be *(0 +be *-45)) +b *(0 +b *4)))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(((0 +p2 *((0 +p3 *6) +p2 *2)) +p1 *(0 +p2 *-3)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *24) +p1 *-45))) +b *(0 +b *((((0 +p3 *-120) +p2 *24) +p1 *4) +b *(0 +b *((0 +be *(0 +be *12)) +b *(0 +b *16)))))))))) +ai *(0 +ai *((0 +p2 *(0 +p2 *-1)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *6))) +b *(0 +b *(((0 +p3 *81) +p2 *-14) +b *(0 +b *((0 +be *(0 +be *63)) +b *(0 +b *-16)))))))))) +ae *(0 +ae *((((0 +p1 *(0 +p2 *1)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-8) +p1 *21))) +b *(0 +b *((((0 +p3 *48) +p2 *-10) +p1 *-5) +b *(0 +b *((0 +be *(0 +be *-20)) +b *(0 +b *-20)))))))) +ai *(0 +ai *((0 +be *(0 +be *(0 +p2 *2))) +b *(0 +b *(((0 +p3 *-29) +p2 *6) +b *(0 +b *((0 +be *(0 +be *-27)) +b *(0 +b *20)))))))) +ae *(0 +ae *(((0 +be *(0 +be *(0 +p1 *-2))) +b *(0 +b *((0 +p1 *2) +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *8)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-8)))))))))))))) +a *((((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *(0 +p2 *-4)))) +b *(0 +b *(((0 +p2 *((0 +p3 *-12) +p2 *-6)) +p1 *(0 +p2 *6)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-22) +p1 *32))) +b *(0 +b *(((0 +p3 *64) +p2 *-24) +b *(0 +b *(0 +be *(0 +be *-4))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *4)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-12))) +b *(0 +b *(((0 +p3 *-64) +p2 *14) +b *(0 +b *(0 +be *(0 +be *-29))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(((0 +p2 *((0 +p3 *12) +p2 *4)) +p1 *(0 +p2 *-12)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *72) +p1 *-90))) +b *(0 +b *((((0 +p3 *-142) +p2 *70) +p1 *8) +b *(0 +b *((0 +be *(0 +be *42)) +b *(0 +b *24))))))))))) +ai *(0 +ai *(0 +b *((0 +p2 *(0 +p2 *-4)) +b *(0 +b *(0 +b *(0 +b *(((0 +p3 *138) +p2 *-48) +b *(0 +b *((0 +be *(0 +be *89)) +b *(0 +b *-28))))))))))) +ae *(0 +ae *(((0 +b *(((0 +p2 *(0 +p2 *2)) +p1 *(0 +p2 *6)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-42) +p1 *72))) +b *(0 +b *((((0 +p3 *67) +p2 *-44) +p1 *-24) +b *(0 +b *((0 +be *(0 +be *-105)) +b *(0 +b *-64))))))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *(0 +p2 *12))) +b *(0 +b *(((0 +p3 *-72) +p2 *38) +b *(0 +b *((0 +be *(0 +be *-51)) +b *(0 +b *80))))))))) +ae *(0 +ae *(((0 +b *((0 +be *(0 +be *(0 +p1 *-14))) +b *(0 +b *((((0 +p3 *16) +p2 *-2) +p1 *20) +b *(0 +b *((0 +be *(0 +be *72)) +b *(0 +b *40))))))) +ai *(0 +ai *(0 +b *(((0 +p3 *-2) +p2 *-4) +b *(0 +b *((0 +be *(0 +be *-13)) +b *(0 +b *-60))))))) +ae *(0 +ae *((0 +b *(((0 +p3 *-1) +p1 *-4) +b *(0 +b *(0 +be *(0 +be *-9))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *4)) +b *(0 +b *8))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p3 *8)) +p1 *(0 +p2 *-12)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *52) +p1 *-56))) +b *(0 +b *(((0 +p3 *-32) +p2 *44) +b *(0 +b *(0 +be *(0 +be *28)))))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-4)) +b *(0 +b *((0 +be *(0 +be *(0 +p2 *-8))) +b *(0 +b *(((0 +p3 *72) +p2 *-35) +b *(0 +b *(0 +be *(0 +be *33)))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(((0 +p2 *(0 +p2 *8)) +p1 *(0 +p2 *12)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-64) +p1 *100))) +b *(0 +b *((((0 +p3 *-28) +p2 *-50) +p1 *-24) +b *(0 +b *((0 +be *(0 +be *-158)) +b *(0 +b *-44)))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *24))) +b *(0 +b *(((0 +p3 *-68) +p2 *69) +b *(0 +b *((0 +be *(0 +be *-17)) +b *(0 +b *71)))))))))) +ae *(0 +ae *(((0 +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-4) +p1 *-36))) +b *(0 +b *((((0 +p3 *84) +p2 *-24) +p1 *49) +b *(0 +b *((0 +be *(0 +be *196)) +b *(0 +b *50)))))))) +ai *(0 +ai *(0 +b *(0 +b *(((0 +p3 *-12) +p2 *-17) +b *(0 +b *((0 +be *(0 +be *-69)) +b *(0 +b *-126)))))))) +ae *(0 +ae *(((0 +b *(0 +b *((((0 +p3 *-8) +p2 *6) +p1 *-22) +b *(0 +b *((0 +be *(0 +be *-50)) +b *(0 +b *16)))))) +ai *(0 +ai *((0 +p2 *-1) +b *(0 +b *((0 +be *(0 +be *29)) +b *(0 +b *39)))))) +ae *(0 +ae *((0 +p1 *1) +b *(0 +b *(0 +b *(0 +b *-6)))))))))))) +a *((((0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *8)) +p1 *(0 +p2 *8)) +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-24) +p1 *48))) +b *(0 +b *(((0 +p3 *-64) +p2 *-8) +b *(0 +b *(0 +be *(0 +be *-64))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *(0 +p2 *16))) +b *(0 +b *(((0 +p3 *-16) +p2 *34) +b *(0 +b *(0 +be *(0 +be *16))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-16) +p1 *-40))) +b *(0 +b *((((0 +p3 *136) +p2 *-66) +p1 *32) +b *(0 +b *((0 +be *(0 +be *178)) +b *(0 +b *8))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(((0 +p3 *-24) +p2 *-20) +b *(0 +b *((0 +be *(0 +be *-114)) +b *(0 +b *-74))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *((((0 +p3 *-20) +p2 *36) +p1 *-36) +b *(0 +b *((0 +be *(0 +be *-63)) +b *(0 +b *58))))))) +ai *(0 +ai *(0 +b *((0 +p2 *-6) +b *(0 +b *((0 +be *(0 +be *72)) +b *(0 +b *56))))))) +ae *(0 +ae *(((0 +b *(((0 +p2 *-2) +p1 *4) +b *(0 +b *((0 +be *(0 +be *-16)) +b *(0 +b *-36))))) +ai *(0 +ai *(0 +b *((0 +be *(0 +be *2)) +b *(0 +b *2))))) +ae *(0 +ae *(0 +b *((0 +be *(0 +be *1)) +b *(0 +b *2))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *((0 +p2 *-16) +p1 *-16))) +b *(0 +b *(((0 +p3 *64) +p2 *-48) +b *(0 +b *(0 +be *(0 +be *32)))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p3 *-16) +p2 *-4) +b *(0 +b *(0 +be *(0 +be *-56)))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *((((0 +p3 *-16) +p2 *64) +p1 *-16) +b *(0 +b *((0 +be *(0 +be *36)) +b *(0 +b *48)))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *-12) +b *(0 +b *((0 +be *(0 +be *68)) +b *(0 +b *20)))))))) +ae *(0 +ae *(((0 +b *(0 +b *(((0 +p2 *-8) +p1 *4) +b *(0 +b *((0 +be *(0 +be *-84)) +b *(0 +b *-64)))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +be *(0 +be *12)) +b *(0 +b *8)))))) +ae *(0 +ae *(0 +b *(0 +b *((0 +be *(0 +be *8)) +b *(0 +b *8)))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *32) +b *(0 +b *(0 +be *(0 +be *64))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *-8) +b *(0 +b *(0 +be *(0 +be *16))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *((0 +p2 *-8) +b *(0 +b *((0 +be *(0 +be *-136)) +b *(0 +b *-32))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *24)) +b *(0 +b *8))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *((0 +be *(0 +be *20)) +b *(0 +b *8))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *-64)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *16)))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +be *(0 +be *16)))))))))))))) =0 /\ (((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *(0 +p2 *1))) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *4)) +p1 *((0 +p2 *-7) +p1 *1)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *4) +p1 *4))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-1)) +p1 *(0 +p2 *2)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-4) +p1 *-5) +b *(0 +b *(0 +b *(0 +b *-4)))))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *1)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *4) +b *(0 +b *(0 +b *(0 +b *4)))))))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *(0 +p2 *-2))) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-17)) +p1 *((0 +p2 *31) +p1 *-5)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-28) +p1 *-21) +b *(0 +b *(0 +b *(0 +b *-4)))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *4)) +p1 *(0 +p2 *-8)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *24) +p1 *27) +b *(0 +b *(0 +b *(0 +b *32)))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-3)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-20) +b *(0 +b *(0 +b *(0 +b *-28)))))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *((0 +p2 *(0 +p2 *(0 +p2 *1))) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *22)) +p1 *((0 +p2 *-51) +p1 *10)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *68) +p1 *46) +b *(0 +b *(0 +b *(0 +b *24)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-5)) +p1 *(0 +p2 *12)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-52) +p1 *-59) +b *(0 +b *(0 +b *(0 +b *-100)))))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *(0 +p2 *3)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *36) +b *(0 +b *(0 +b *(0 +b *76)))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-9)) +p1 *((0 +p2 *37) +p1 *-10)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-68) +p1 *-53) +b *(0 +b *(0 +b *(0 +b *-52)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p2 *(0 +p2 *2)) +p1 *(0 +p2 *-8)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *48) +p1 *65) +b *(0 +b *(0 +b *(0 +b *152)))))))))) +ai *(0 +ai *((0 +p2 *(0 +p2 *-1)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-28) +b *(0 +b *(0 +b *(0 +b *-100)))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *((0 +p1 *((0 +p2 *-10) +p1 *5)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *24) +p1 *32) +b *(0 +b *(0 +b *(0 +b *48)))))))))) +ai *(0 +ai *(((0 +p1 *(0 +p2 *2)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-16) +p1 *-36) +b *(0 +b *(0 +b *(0 +b *-112)))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *8) +b *(0 +b *(0 +b *(0 +b *64)))))))))) +ae *(0 +ae *(((0 +p1 *(0 +p1 *-1)) +b *(0 +b *(0 +b *(0 +b *((0 +p1 *-8) +b *(0 +b *(0 +b *(0 +b *-16)))))))) +ai *(0 +ai *((0 +b *(0 +b *((0 +p1 *8) +b *(0 +b *(0 +b *(0 +b *32)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-16)))))))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *(0 +p2 *-4))) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-22)) +p1 *((0 +p2 *53) +p1 *-10)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-28) +p1 *-32)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *5)) +p1 *(0 +p2 *-16)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *26) +p1 *46) +b *(0 +b *(0 +b *(0 +b *32))))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-6)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-30) +b *(0 +b *(0 +b *(0 +b *-36))))))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *(0 +p2 *4))) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *64)) +p1 *((0 +p2 *-177) +p1 *40)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *150) +p1 *129) +b *(0 +b *(0 +b *(0 +b *28))))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-14)) +p1 *(0 +p2 *48)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-120) +p1 *-198) +b *(0 +b *(0 +b *(0 +b *-208))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *12)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *114) +b *(0 +b *(0 +b *(0 +b *204))))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-42)) +p1 *((0 +p2 *195) +p1 *-60)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-248) +p1 *-204) +b *(0 +b *(0 +b *(0 +b *-128))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *9)) +p1 *(0 +p2 *-48)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *178) +p1 *324) +b *(0 +b *(0 +b *(0 +b *496))))))))))) +ai *(0 +ai *(0 +b *((0 +p2 *(0 +p2 *-6)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-138) +b *(0 +b *(0 +b *(0 +b *-420))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *((0 +p1 *((0 +p2 *-71) +p1 *40)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *126) +p1 *153) +b *(0 +b *(0 +b *(0 +b *188))))))))))) +ai *(0 +ai *((0 +b *((0 +p1 *(0 +p2 *16)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-84) +p1 *-238) +b *(0 +b *(0 +b *(0 +b *-512))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *54) +b *(0 +b *(0 +b *(0 +b *372))))))))))) +ae *(0 +ae *((0 +b *((0 +p1 *(0 +p1 *-10)) +b *(0 +b *(0 +b *(0 +b *((0 +p1 *-46) +b *(0 +b *(0 +b *(0 +b *-88))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *((0 +p1 *66) +b *(0 +b *(0 +b *(0 +b *192))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-120))))))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *(0 +p2 *4))) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *38)) +p1 *((0 +p2 *-144) +p1 *40)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *60) +p1 *84))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-6)) +p1 *(0 +p2 *48)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-45) +p1 *-161) +b *(0 +b *(0 +b *(0 +b *-84)))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *12)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *80) +b *(0 +b *(0 +b *(0 +b *121)))))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-58)) +p1 *((0 +p2 *318) +p1 *-120)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-210) +p1 *-204) +b *(0 +b *(0 +b *(0 +b *-60)))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *8)) +p1 *(0 +p2 *-96)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *127) +p1 *507) +b *(0 +b *(0 +b *(0 +b *393)))))))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-12)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-204) +b *(0 +b *(0 +b *(0 +b *-515)))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *2)) +p1 *((0 +p2 *-168) +p1 *120)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *146) +p1 *127) +b *(0 +b *(0 +b *(0 +b *172)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p2 *(0 +p2 *2)) +p1 *(0 +p2 *48)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-57) +p1 *-531) +b *(0 +b *(0 +b *(0 +b *-566)))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *120) +b *(0 +b *(0 +b *(0 +b *699)))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(((0 +p2 *(0 +p2 *-2)) +p1 *((0 +p2 *-6) +p1 *-40)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *42) +p1 *32) +b *(0 +b *(0 +b *(0 +b *-92)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-47) +p1 *173) +b *(0 +b *(0 +b *(0 +b *185)))))))) +ai *(0 +ai *(0 +b *(0 +b *((0 +p2 *4) +b *(0 +b *(0 +b *(0 +b *-289)))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-6) +p1 *-45) +b *(0 +b *(0 +b *(0 +b *-44)))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p2 *6) +p1 *12) +b *(0 +b *(0 +b *(0 +b *96)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-16)))))))) +ae *(0 +ae *((0 +b *(0 +b *((0 +p1 *2) +b *(0 +b *(0 +b *(0 +b *8)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-8)))))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-20)) +p1 *((0 +p2 *152) +p1 *-80)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-4) +p1 *-40)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-4)) +p1 *(0 +p2 *-64)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-39) +p1 *250) +b *(0 +b *(0 +b *(0 +b *40))))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *(0 +p2 *-8)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-80) +b *(0 +b *(0 +b *(0 +b *-170))))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *8)) +p1 *((0 +p2 *-140) +p1 *160)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-86) +p1 *-166) +b *(0 +b *(0 +b *(0 +b *4))))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *8)) +p1 *(0 +p2 *64)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *195) +p1 *-456) +b *(0 +b *(0 +b *(0 +b *53))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *88) +b *(0 +b *(0 +b *(0 +b *440))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-12)) +p1 *((0 +p2 *-36) +p1 *-80)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *200) +p1 *449) +b *(0 +b *(0 +b *(0 +b *106))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-241) +p1 *130) +b *(0 +b *(0 +b *(0 +b *-500))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *((0 +p2 *24) +b *(0 +b *(0 +b *(0 +b *-194))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-38) +p1 *-264) +b *(0 +b *(0 +b *(0 +b *-208))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p2 *45) +p1 *84) +b *(0 +b *(0 +b *(0 +b *533))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-108))))))))) +ae *(0 +ae *((0 +b *(0 +b *(0 +b *((0 +p1 *17) +b *(0 +b *(0 +b *(0 +b *50))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-62))))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *8)) +p1 *((0 +p2 *-16) +p1 *80)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-128) +p1 *-160))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *8)) +p1 *(0 +p2 *32)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *192) +p1 *-120) +b *(0 +b *(0 +b *(0 +b *160)))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *40)))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-24)) +p1 *((0 +p2 *-72) +p1 *-80)) +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *274) +p1 *608) +b *(0 +b *(0 +b *(0 +b *128)))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-378) +p1 *-72) +b *(0 +b *(0 +b *(0 +b *-784)))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *48) +b *(0 +b *(0 +b *(0 +b *120)))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-51) +p1 *-462) +b *(0 +b *(0 +b *(0 +b *-282)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *112) +p1 *204) +b *(0 +b *(0 +b *(0 +b *904)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-252)))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-16) +p1 *16) +b *(0 +b *(0 +b *(0 +b *75)))))))) +ai *(0 +ai *((0 +b *(0 +b *(((0 +p2 *2) +p1 *4) +b *(0 +b *(0 +b *(0 +b *-128)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))))) +ae *(0 +ae *(((0 +b *(0 +b *(((0 +p2 *1) +p1 *2) +b *(0 +b *(0 +b *(0 +b *16)))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *-4)))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *-1)))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *(0 +p2 *-16)) +p1 *((0 +p2 *-48) +p1 *-32)) +b *(0 +b *(0 +b *(0 +b *((0 +p2 *96) +p1 *192)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-168) +p1 *-80) +b *(0 +b *(0 +b *(0 +b *-192))))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *32) +b *(0 +b *(0 +b *(0 +b *112))))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *36) +p1 *-192) +b *(0 +b *(0 +b *(0 +b *-96))))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *100) +p1 *192) +b *(0 +b *(0 +b *(0 +b *408))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-224))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-84) +p1 *-116) +b *(0 +b *(0 +b *(0 +b *-20))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(((0 +p2 *12) +p1 *24) +b *(0 +b *(0 +b *(0 +b *16))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-24))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(((0 +p2 *8) +p1 *16) +b *(0 +b *(0 +b *(0 +b *84))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-28))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-8))))))))))))) +a *((((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *64) +p1 *64))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *16) +p1 *48) +b *(0 +b *(0 +b *(0 +b *-64)))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-48)))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *-136) +p1 *-256) +b *(0 +b *(0 +b *(0 +b *-64)))))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *24) +p1 *48) +b *(0 +b *(0 +b *(0 +b *240)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-48)))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *20) +p1 *40) +b *(0 +b *(0 +b *(0 +b *136)))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-64)))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-20)))))))))))) +a *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *((0 +p2 *-64) +p1 *-128)))))))) +ai *(0 +ai *((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *16) +p1 *32) +b *(0 +b *(0 +b *(0 +b *128))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-32))))))))))) +ae *(0 +ae *(((0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(((0 +p2 *16) +p1 *32) +b *(0 +b *(0 +b *(0 +b *64))))))))) +ai *(0 +ai *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-48))))))))) +ae *(0 +ae *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *(0 +b *-16))))))))))))))))) =0)>>"

    );
    (
        // idx 51
        // complex.p059
        @"exists b c.
        (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\ 
        (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\ 
        (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))",
        formula<fol>.False,
        @""
    );
    (
        // idx 52
        // complex.p060
        @"forall y.
            a * x^2 + b * x + c = 0 /\ 
            a * y^2 + b * y + c = 0 /\ 
            ~(x = y)
            ==> a * x * y = c /\ a * (x + y) + b = 0",
        formula<fol>.False,  // Dummy value used as place holder
        @"<<~((0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~0 +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *((0 +c *(0 +c *-1)) +b *(0 +c *(0 +x *-1)))) +a *((0 +c *(0 +c *(0 +x *-1))) +b *(0 +c *(0 +x *(0 +x *-1)))) =0) \/ ~0 +a *1 =0 /\ (~0 +a *(0 +a *(((0 +c *(0 +c *(0 +c *-1))) +b *((0 +c *(0 +c *(0 +x *-2))) +b *(0 +c *(0 +x *(0 +x *-1))))) +a *(((0 +c *(0 +c *(0 +x *(0 +x *-2)))) +b *(0 +c *(0 +x *(0 +x *(0 +x *-2))))) +a *(0 +c *(0 +x *(0 +x *(0 +x *(0 +x *-1)))))))) =0 \/ ~0 +a *(0 +a *((0 +b *((0 +c *(0 +c *-1)) +b *((0 +c *(0 +x *-2)) +b *(0 +x *(0 +x *-1))))) +a *((0 +b *((0 +c *(0 +x *(0 +x *-2))) +b *(0 +x *(0 +x *(0 +x *-2))))) +a *(0 +b *(0 +x *(0 +x *(0 +x *(0 +x *-1)))))))) =0)) /\ ((0 +c *1) +b *(0 +x *1)) +a *(0 +x *(0 +x *1)) =0 \/ (0 +a *1 =0 /\ (0 +b *1 =0 /\ 0 +c *1 =0 /\ ~(0 +b *1) +a *(0 +x *1) =0 \/ ~0 +b *1 =0 /\ ~(0 +b *(0 +b *((0 +c *1) +b *(0 +x *1)))) +a *((0 +c *(0 +c *-1)) +b *(0 +b *(0 +x *(0 +x *1)))) =0) \/ ~0 +a *1 =0 /\ ~0 +a *(0 +a *(0 +a *(((0 +c *(0 +c *1)) +b *((0 +c *(0 +x *2)) +b *(0 +x *(0 +x *1)))) +a *(((0 +c *(0 +x *(0 +x *2))) +b *(0 +x *(0 +x *(0 +x *2)))) +a *(0 +x *(0 +x *(0 +x *(0 +x *1)))))))) =0) /\ ((0 +c *1) +b *(0 +x *1)) +a *(0 +x *(0 +x *1)) =0)>>"
    );
    (
        // idx 53
        // complex.p061
        @"a * x^2 + b * x + c = 0 /\ 
            a * y^2 + b * y + c = 0 /\ 
            ~(x = y)
            ==> a * x * y = c /\ a * (x + y) + b = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 54
        // complex.p062
        @"(x_1 + x_3  = (x_2) \/ x_1 + x_3  = -(x_2)) /\ 
        (x_2 + x_4  = (x_3) \/ x_2 + x_4  = -(x_3)) /\ 
        (x_3 + x_5  = (x_4) \/ x_3 + x_5  = -(x_4)) /\ 
        (x_4 + x_6  = (x_5) \/ x_4 + x_6  = -(x_5)) /\ 
        (x_5 + x_7  = (x_6) \/ x_5 + x_7  = -(x_6)) /\ 
        (x_6 + x_8  = (x_7) \/ x_6 + x_8  = -(x_7)) /\ 
        (x_7 + x_9  = (x_8) \/ x_7 + x_9  = -(x_8)) /\ 
        (x_8 + x_10 = (x_9) \/ x_8 + x_10 = -(x_9)) /\ 
        (x_9 + x_11 = (x_10) \/ x_9 + x_11 = -(x_10))
        ==> x_1 = x_10 /\ x_2 = x_11",
        formula<fol>.False,
        @"<<false>>"
    );
    (
        // idx 55
        // complex.p063
        @"forall a b c.
        (exists x. a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0) \/ (a = 0) <=>
        (4*a^2*c-b^2*a = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 56
        // complex.p064
        @"forall a b c d e.
        (exists x. a * x^2 + b * x + c = 0 /\ d * x + e = 0) \/
        a = 0 /\ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 57
        // complex.p065
        @"forall a b c d e f.
        (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
        (a = 0) /\ (d = 0) <=>
        d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 58
        // complex.p066
        @"forall a b c d e f g.
        (exists x. a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0) \/
        (a = 0) /\ (e = 0) <=>
        e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
        g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 59
        // complex.p067
        @"forall x y. x^2 + y^2 = 1 ==> (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 60
        // complex.p068
        @"forall s c. s^2 + c^2 = 1
        ==> 2 * s - (2 * s * c * c - s^3) = 3 * s^3",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 61
        // complex.p069
        @"forall u v.
        -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
            (((7 * u^6) * v) * v - (u * u^7)) * 144 -
            (((5 * u^4) * v) * v - (u * u^5)) * 168 -
            (((3 * u^2) * v) * v - (u * u^3)) * 210 -
            (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
        (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
        (u^2 + v^2 - 1)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 62
        // complex.p070
        @"forall u v.
        u^2 + v^2 = 1
        ==> (((9 * u^8) * v) * v - (u * u^9)) * 128 +
            (((7 * u^6) * v) * v - (u * u^7)) * 144 +
            (((5 * u^4) * v) * v - (u * u^5)) * 168 +
            (((3 * u^2) * v) * v - (u * u^3)) * 210 +
            (v * v - (u * u)) * 315 + 1280 * u^10 = 315",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 63
        // complex.p071
        @"exists z. x * z^87 + y * z^44 + 1 = 0",
        Or
          (And
             (Atom
                (R ("=",
                    [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "x"; Fn ("1",[])])]);
                     Fn ("0",[])])),
              Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",[Fn ("0",[]); Fn ("*",[Var "y"; Fn ("1",[])])]);
                        Fn ("0",[])])))),
           Not
             (Atom
                (R ("=",
                    [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "x"; Fn ("1",[])])]);
                     Fn ("0",[])])))),
        @"<<0 +x *1 =0 /\ ~0 +y *1 =0 \/ ~0 +x *1 =0>>"
    );
    (
        // idx 64
        // complex.p072
        @"forall u. exists v. x * (u + v^2)^2 + y * (u + v^2) + z = 0",
        Not
          (And
             (Atom
                (R ("=",
                    [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "x"; Fn ("1",[])])]);
                     Fn ("0",[])])),
              Or
                (And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "x"; Fn ("2",[])])]);
                           Fn ("0",[])])),
                    And
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "y"; Fn ("1",[])])]);
                              Fn ("0",[])])),
                       Not
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "z"; Fn ("1",[])])]);
                                 Fn ("0",[])]))))),
                 And
                   (Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "x"; Fn ("2",[])])]);
                              Fn ("0",[])]))),
                    Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn
                                    ("*",
                                     [Var "x";
                                      Fn
                                        ("+",
                                         [Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn
                                                ("*",
                                                 [Var "y";
                                                  Fn
                                                    ("+",
                                                     [Fn ("0",[]);
                                                      Fn
                                                        ("*",
                                                         [Var "y";
                                                          Fn ("-1",[])])])])]);
                                          Fn
                                            ("*",
                                             [Var "x";
                                              Fn
                                                ("+",
                                                 [Fn ("0",[]);
                                                  Fn
                                                    ("*",
                                                     [Var "z"; Fn ("4",[])])])])])])]);
                              Fn ("0",[])]))))))),
        @"<<~(0 +x *1 =0 /\ (0 +x *2 =0 /\ 0 +y *1 =0 /\ ~0 +z *1 =0 \/ ~0 +x *2 =0 /\ ~0 +x *((0 +y *(0 +y *-1)) +x *(0 +z *4)) =0))>>"
    );
    (
        // idx 65
        // complex.p073
        @"forall x y. (exists z. x * z^87 + y * z^44 + 1 = 0)
                    <=> ~(x = 0) \/ ~(y = 0)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 66
        // complex.p074
        @"forall x y z. (forall u. exists v.
                            x * (u + v^2)^2 + y * (u + v^2) + z = 0)
                    <=> ~(x = 0) \/ ~(y = 0) \/ z = 0",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 67
        // complex.p075
        @"exists w x y z. (a * w + b * y = 1) /\ 
                        (a * x + b * z = 0) /\ 
                        (c * w + d * y = 0) /\ 
                        (c * x + d * z = 1)",
        And
          (Or
             (And
                (Not
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                           Fn ("0",[])]))),
                 Or
                   (And
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn
                                        ("*",
                                         [Var "b";
                                          Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn ("*",[Var "c"; Fn ("1",[])])])])]);
                                  Fn
                                    ("*",
                                     [Var "a";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "d"; Fn ("-1",[])])])])]);
                              Fn ("0",[])])),
                       Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "d"; Fn ("1",[])])]);
                              Fn ("0",[])]))),
                    Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn
                                        ("*",
                                         [Var "b";
                                          Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn ("*",[Var "c"; Fn ("1",[])])])])]);
                                  Fn
                                    ("*",
                                     [Var "a";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "d"; Fn ("-1",[])])])])]);
                              Fn ("0",[])]))))),
              Or
                (And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                           Fn ("0",[])])),
                    And
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "d"; Fn ("1",[])])]);
                              Fn ("0",[])])),
                       And
                         (Not
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn ("0",[]);
                                        Fn ("*",[Var "a"; Fn ("1",[])])]);
                                    Fn ("0",[])]))),
                          Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "c"; Fn ("1",[])])]);
                                 Fn ("0",[])]))))),
                 And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                           Fn ("0",[])])),
                    And
                      (Not
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "d"; Fn ("1",[])])]);
                                 Fn ("0",[])]))),
                       Not
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "a"; Fn ("1",[])])]);
                                 Fn ("0",[])]))))))),
           Or
             (And
                (Not
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "d"; Fn ("1",[])])]);
                           Fn ("0",[])]))),
                 Or
                   (And
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn
                                        ("*",
                                         [Var "b";
                                          Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn ("*",[Var "c"; Fn ("-1",[])])])])]);
                                  Fn
                                    ("*",
                                     [Var "a";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "d"; Fn ("1",[])])])])]);
                              Fn ("0",[])])),
                       Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                              Fn ("0",[])]))),
                    Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn
                                        ("*",
                                         [Var "b";
                                          Fn
                                            ("+",
                                             [Fn ("0",[]);
                                              Fn ("*",[Var "c"; Fn ("-1",[])])])])]);
                                  Fn
                                    ("*",
                                     [Var "a";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "d"; Fn ("1",[])])])])]);
                              Fn ("0",[])]))))),
              Or
                (And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                           Fn ("0",[])])),
                    And
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "d"; Fn ("1",[])])]);
                              Fn ("0",[])])),
                       And
                         (Not
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn ("0",[]);
                                        Fn ("*",[Var "c"; Fn ("1",[])])]);
                                    Fn ("0",[])]))),
                          Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "a"; Fn ("1",[])])]);
                                 Fn ("0",[])]))))),
                 And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "d"; Fn ("1",[])])]);
                           Fn ("0",[])])),
                    And
                      (Not
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "b"; Fn ("1",[])])]);
                                 Fn ("0",[])]))),
                       Not
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "c"; Fn ("1",[])])]);
                                 Fn ("0",[])])))))))),
        @"<<(~0 +b *1 =0 /\ ((0 +b *(0 +c *1)) +a *(0 +d *-1) =0 /\ 0 +d *1 =0 \/ ~(0 +b *(0 +c *1)) +a *(0 +d *-1) =0) \/ 0 +b *1 =0 /\ 0 +d *1 =0 /\ ~0 +a *1 =0 /\ 0 +c *1 =0 \/ 0 +b *1 =0 /\ ~0 +d *1 =0 /\ ~0 +a *1 =0) /\ (~0 +d *1 =0 /\ ((0 +b *(0 +c *-1)) +a *(0 +d *1) =0 /\ 0 +b *1 =0 \/ ~(0 +b *(0 +c *-1)) +a *(0 +d *1) =0) \/ 0 +b *1 =0 /\ 0 +d *1 =0 /\ ~0 +c *1 =0 /\ 0 +a *1 =0 \/ 0 +d *1 =0 /\ ~0 +b *1 =0 /\ ~0 +c *1 =0)>>"
    );
    (
        // idx 68
        // complex.p076
        @"forall a b c d.
        (exists w x y z. (a * w + b * y = 1) /\ 
                            (a * x + b * z = 0) /\ 
                            (c * w + d * y = 0) /\ 
                            (c * x + d * z = 1))
            <=> ~(a * d = b * c)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 69
        // complex.p077
        @"forall m n x u t cu ct.
        t - u = n /\ 27 * t * u = m^3 /\ 
        ct^3 = t /\ cu^3 = u /\ 
        x = ct - cu
        ==> x^3 + m * x = n",
        formula<fol>.False,
        @"<<false>>"
    );
    (
        // idx 70
        // complex.p078
        @"forall m n x u t.
        t - u = n /\ 27 * t * u = m^3
        ==> exists ct cu. ct^3 = t /\ cu^3 = u /\ 
                            (x = ct - cu ==> x^3 + m * x = n)",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 71
        // complex.p079
        @"forall x y z.
        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
            x^2 * y^2 * (x^2 + y^2 + 1) * (x^2 + y^2 - 2)^2 + (x^2 - y^2)^2",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 72
        // complex.p080
        @"forall x y z.
        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
        x^2 * y^2 * x^2  * (x^2 + y^2 - 2)^2 +
        x^2 * y^2 * y^2 * (x^2 + y^2 - 2)^2 +
        x^2 * y^2 * (x^2 + y^2 - 2)^2 +
        (x^2 - y^2)^2",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 73
        // complex.p081
        @"forall x y z.
        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
        x^4 * y^2 * (x^2 + y^2 - 2)^2 +
        x^2 * y^4 * (x^2 + y^2 - 2)^2 +
        x^2 * y^2 * (x^2 + y^2 - 2)^2 +
        (x^2 - y^2)^2",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 74
        // complex.p082
        @"forall x y z.
        (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
        (x^2 * y * (x^2 + y^2 - 2))^2 +
        (x * y^2 * (x^2 + y^2 - 2))^2 +
        (x * y * (x^2 + y^2 - 2))^2 +
        (x^2 - y^2)^2",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 75
        // complex.p084
        @"forall x y. (a * x + b * y = u * x - v * y) /\ 
                (c * x + d * y = u * y + v * x)
                ==> (a = d)",
        Not
          (And
             (Or
                (And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn
                                 ("+",
                                  [Fn ("0",[]);
                                   Fn ("*",[Var "u"; Fn ("-1",[])])]);
                               Fn ("*",[Var "d"; Fn ("1",[])])]); Fn ("0",[])])),
                    And
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "v"; Fn ("1",[])])]);
                                  Fn ("*",[Var "b"; Fn ("1",[])])]);
                              Fn ("0",[])])),
                       Or
                         (And
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn ("*",[Var "u"; Fn ("-1",[])])]);
                                        Fn ("*",[Var "a"; Fn ("1",[])])]);
                                    Fn ("0",[])])),
                             Or
                               (Atom
                                  (R ("=",
                                      [Fn
                                         ("+",
                                          [Fn
                                             ("+",
                                              [Fn ("0",[]);
                                               Fn
                                                 ("*",[Var "v"; Fn ("-1",[])])]);
                                           Fn ("*",[Var "c"; Fn ("1",[])])]);
                                       Fn ("0",[])])),
                                Not
                                  (Atom
                                     (R ("=",
                                         [Fn
                                            ("+",
                                             [Fn
                                                ("+",
                                                 [Fn ("0",[]);
                                                  Fn
                                                    ("*",
                                                     [Var "v"; Fn ("-1",[])])]);
                                              Fn ("*",[Var "c"; Fn ("1",[])])]);
                                          Fn ("0",[])]))))),
                          Not
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn ("*",[Var "u"; Fn ("-1",[])])]);
                                        Fn ("*",[Var "a"; Fn ("1",[])])]);
                                    Fn ("0",[])])))))),
                 Or
                   (And
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "v"; Fn ("1",[])])]);
                                  Fn ("*",[Var "b"; Fn ("1",[])])]);
                              Fn ("0",[])])),
                       And
                         (Not
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn ("*",[Var "u"; Fn ("-1",[])])]);
                                        Fn ("*",[Var "d"; Fn ("1",[])])]);
                                    Fn ("0",[])]))),
                          Or
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn
                                          ("+",
                                           [Fn ("0",[]);
                                            Fn ("*",[Var "u"; Fn ("-1",[])])]);
                                        Fn ("*",[Var "a"; Fn ("1",[])])]);
                                    Fn ("0",[])])),
                             Not
                               (Atom
                                  (R ("=",
                                      [Fn
                                         ("+",
                                          [Fn
                                             ("+",
                                              [Fn ("0",[]);
                                               Fn
                                                 ("*",[Var "u"; Fn ("-1",[])])]);
                                           Fn ("*",[Var "a"; Fn ("1",[])])]);
                                       Fn ("0",[])])))))),
                    And
                      (Not
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn
                                       ("+",
                                        [Fn ("0",[]);
                                         Fn ("*",[Var "v"; Fn ("1",[])])]);
                                     Fn ("*",[Var "b"; Fn ("1",[])])]);
                                 Fn ("0",[])]))),
                       Or
                         (Atom
                            (R ("=",
                                [Fn
                                   ("+",
                                    [Fn
                                       ("+",
                                        [Fn
                                           ("+",
                                            [Fn
                                               ("+",
                                                [Fn
                                                   ("+",
                                                    [Fn
                                                       ("+",
                                                        [Fn ("0",[]);
                                                         Fn
                                                           ("*",
                                                            [Var "v";
                                                             Fn
                                                               ("+",
                                                                [Fn ("0",[]);
                                                                 Fn
                                                                   ("*",
                                                                    [Var "v";
                                                                     Fn
                                                                       ("-1",
                                                                        [])])])])]);
                                                     Fn
                                                       ("*",
                                                        [Var "u";
                                                         Fn
                                                           ("+",
                                                            [Fn ("0",[]);
                                                             Fn
                                                               ("*",
                                                                [Var "u";
                                                                 Fn ("-1",[])])])])]);
                                                 Fn
                                                   ("*",
                                                    [Var "d";
                                                     Fn
                                                       ("+",
                                                        [Fn ("0",[]);
                                                         Fn
                                                           ("*",
                                                            [Var "u";
                                                             Fn ("1",[])])])])]);
                                             Fn
                                               ("*",
                                                [Var "c";
                                                 Fn
                                                   ("+",
                                                    [Fn ("0",[]);
                                                     Fn
                                                       ("*",
                                                        [Var "v"; Fn ("1",[])])])])]);
                                         Fn
                                           ("*",
                                            [Var "b";
                                             Fn
                                               ("+",
                                                [Fn
                                                   ("+",
                                                    [Fn ("0",[]);
                                                     Fn
                                                       ("*",
                                                        [Var "v"; Fn ("-1",[])])]);
                                                 Fn
                                                   ("*",[Var "c"; Fn ("1",[])])])])]);
                                     Fn
                                       ("*",
                                        [Var "a";
                                         Fn
                                           ("+",
                                            [Fn
                                               ("+",
                                                [Fn ("0",[]);
                                                 Fn
                                                   ("*",[Var "u"; Fn ("1",[])])]);
                                             Fn ("*",[Var "d"; Fn ("-1",[])])])])]);
                                 Fn ("0",[])])),
                          Not
                            (Atom
                               (R ("=",
                                   [Fn
                                      ("+",
                                       [Fn
                                          ("+",
                                           [Fn
                                              ("+",
                                               [Fn
                                                  ("+",
                                                   [Fn
                                                      ("+",
                                                       [Fn
                                                          ("+",
                                                           [Fn ("0",[]);
                                                            Fn
                                                              ("*",
                                                               [Var "v";
                                                                Fn
                                                                  ("+",
                                                                   [Fn
                                                                      ("0",[]);
                                                                    Fn
                                                                      ("*",
                                                                       [Var
                                                                          "v";
                                                                        Fn
                                                                          ("-1",
                                                                           [])])])])]);
                                                        Fn
                                                          ("*",
                                                           [Var "u";
                                                            Fn
                                                              ("+",
                                                               [Fn ("0",[]);
                                                                Fn
                                                                  ("*",
                                                                   [Var "u";
                                                                    Fn
                                                                      ("-1",[])])])])]);
                                                    Fn
                                                      ("*",
                                                       [Var "d";
                                                        Fn
                                                          ("+",
                                                           [Fn ("0",[]);
                                                            Fn
                                                              ("*",
                                                               [Var "u";
                                                                Fn ("1",[])])])])]);
                                                Fn
                                                  ("*",
                                                   [Var "c";
                                                    Fn
                                                      ("+",
                                                       [Fn ("0",[]);
                                                        Fn
                                                          ("*",
                                                           [Var "v";
                                                            Fn ("1",[])])])])]);
                                            Fn
                                              ("*",
                                               [Var "b";
                                                Fn
                                                  ("+",
                                                   [Fn
                                                      ("+",
                                                       [Fn ("0",[]);
                                                        Fn
                                                          ("*",
                                                           [Var "v";
                                                            Fn ("-1",[])])]);
                                                    Fn
                                                      ("*",
                                                       [Var "c"; Fn ("1",[])])])])]);
                                        Fn
                                          ("*",
                                           [Var "a";
                                            Fn
                                              ("+",
                                               [Fn
                                                  ("+",
                                                   [Fn ("0",[]);
                                                    Fn
                                                      ("*",
                                                       [Var "u"; Fn ("1",[])])]);
                                                Fn
                                                  ("*",[Var "d"; Fn ("-1",[])])])])]);
                                    Fn ("0",[])]))))))),
              Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",
                           [Fn
                              ("+",
                               [Fn ("0",[]); Fn ("*",[Var "d"; Fn ("-1",[])])]);
                            Fn ("*",[Var "a"; Fn ("1",[])])]); Fn ("0",[])]))))),
        @"<<~(((0 +u *-1) +d *1 =0 /\ (0 +v *1) +b *1 =0 /\ ((0 +u *-1) +a *1 =0 /\ ((0 +v *-1) +c *1 =0 \/ ~(0 +v *-1) +c *1 =0) \/ ~(0 +u *-1) +a *1 =0) \/ (0 +v *1) +b *1 =0 /\ ~(0 +u *-1) +d *1 =0 /\ ((0 +u *-1) +a *1 =0 \/ ~(0 +u *-1) +a *1 =0) \/ ~(0 +v *1) +b *1 =0 /\ ((((((0 +v *(0 +v *-1)) +u *(0 +u *-1)) +d *(0 +u *1)) +c *(0 +v *1)) +b *((0 +v *-1) +c *1)) +a *((0 +u *1) +d *-1) =0 \/ ~(((((0 +v *(0 +v *-1)) +u *(0 +u *-1)) +d *(0 +u *1)) +c *(0 +v *1)) +b *((0 +v *-1) +c *1)) +a *((0 +u *1) +d *-1) =0)) /\ ~(0 +d *-1) +a *1 =0)>>"
    );
    (
        // idx 76
        // complex.p085
        @"forall a b c d.
        (forall x y. (a * x + b * y = u * x - v * y) /\ 
                    (c * x + d * y = u * y + v * x))
                    ==> (a = d) /\ (b = -(c))",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 77
        // complex.p086
        @"forall a b c d.
        (exists u v. forall x y. (a * x + b * y = u * x - v * y) /\ 
                                    (c * x + d * y = u * y + v * x))
        <=> (a = d) /\ (b = -(c))",
        formula<fol>.True,
        @"<<true>>"
    );
    (
        // idx 78
        // complex.p087
        @"forall x1 y1 x2 y2. exists a b.
        ~(a = 0 /\ b = 0) /\ a * x1 + b * y1 = 0 /\ a * x2 + b * y2 = 0",
        formula<fol>.False,
        @"<<false>>"
    );
    |]

[<TestCase(0, TestName = "complex.p002")>]
[<TestCase(1, TestName = "complex.p003")>]
[<TestCase(2, TestName = "complex.p004")>]
[<TestCase(3, TestName = "complex.p005")>]
[<TestCase(4, TestName = "complex.p012")>]
[<TestCase(5, TestName = "complex.p013")>]
[<TestCase(6, TestName = "complex.p014")>]
[<TestCase(7, TestName = "complex.p015")>]
[<TestCase(8, TestName = "complex.p016")>]
[<TestCase(9, TestName = "complex.p017")>]
[<TestCase(10, TestName = "complex.p018")>]
[<TestCase(11, TestName = "complex.p019")>]
[<TestCase(12, TestName = "complex.p020")>]
[<TestCase(13, TestName = "complex.p021")>]
[<TestCase(14, TestName = "complex.p022")>]
[<TestCase(15, TestName = "complex.p023")>]
[<TestCase(16, TestName = "complex.p024")>]
[<TestCase(17, TestName = "complex.p025", Category = "LongRunning")>]
[<TestCase(18, TestName = "complex.p026")>]
[<TestCase(19, TestName = "complex.p027")>]
[<TestCase(20, TestName = "complex.p028")>]
[<TestCase(21, TestName = "complex.p029")>]
[<TestCase(22, TestName = "complex.p030")>]
[<TestCase(23, TestName = "complex.p031")>]
[<TestCase(24, TestName = "complex.p032")>]
[<TestCase(25, TestName = "complex.p033")>]
[<TestCase(26, TestName = "complex.p034")>]
[<TestCase(27, TestName = "complex.p035")>]
[<TestCase(28, TestName = "complex.p036")>]
[<TestCase(29, TestName = "complex.p037")>]
[<TestCase(30, TestName = "complex.p038")>]
[<TestCase(31, TestName = "complex.p039")>]
[<TestCase(32, TestName = "complex.p040")>]
[<TestCase(34, TestName = "complex.p042", Category = "LongRunning")>]
[<TestCase(35, TestName = "complex.p043", Category = "LongRunning")>]
[<TestCase(36, TestName = "complex.p044", Category = "LongRunning")>]
[<TestCase(37, TestName = "complex.p045")>]
[<TestCase(38, TestName = "complex.p046")>]
[<TestCase(39, TestName = "complex.p047")>]
[<TestCase(40, TestName = "complex.p048")>]
[<TestCase(41, TestName = "complex.p049")>]
[<TestCase(43, TestName = "complex.p051")>]
[<TestCase(51, TestName = "complex.p059", Category = "LongRunning")>]
[<TestCase(55, TestName = "complex.p063")>]
[<TestCase(56, TestName = "complex.p064")>]
[<TestCase(57, TestName = "complex.p065")>]
[<TestCase(58, TestName = "complex.p066", Category = "LongRunning")>]
[<TestCase(59, TestName = "complex.p067")>]
[<TestCase(60, TestName = "complex.p068")>]
[<TestCase(61, TestName = "complex.p069")>]
[<TestCase(62, TestName = "complex.p070")>]
[<TestCase(63, TestName = "complex.p071")>]
[<TestCase(64, TestName = "complex.p072")>]
[<TestCase(65, TestName = "complex.p073")>]
[<TestCase(66, TestName = "complex.p074")>]
[<TestCase(67, TestName = "complex.p075")>]
[<TestCase(68, TestName = "complex.p076")>]
[<TestCase(69, TestName = "complex.p077")>]
[<TestCase(70, TestName = "complex.p078")>]
[<TestCase(71, TestName = "complex.p079")>]
[<TestCase(72, TestName = "complex.p080")>]
[<TestCase(73, TestName = "complex.p081")>]
[<TestCase(74, TestName = "complex.p082")>]
[<TestCase(75, TestName = "complex.p084")>]
[<TestCase(76, TestName = "complex.p085")>]
[<TestCase(77, TestName = "complex.p086")>]
[<TestCase(78, TestName = "complex.p087")>]

[<Test>]
let ``complex_qelim tests`` idx = 
    let (formula, _, _) = complex_qelimValues.[idx]
    let (_, astResult, _) = complex_qelimValues.[idx]
    let (_, _, stringResult) = complex_qelimValues.[idx]
    let result = complex_qelim (parse formula)
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult

[<TestCase(33, TestName = "complex.p041")>]
[<TestCase(50, TestName = "complex.p058")>]
[<TestCase(52, TestName = "complex.p060")>]

[<Test>]
let ``complex_qelim 1 tests`` idx = 
    let (formula, _, _) = complex_qelimValues.[idx]
    let (_, astResult, _) = complex_qelimValues.[idx]
    let (_, _, stringResult) = complex_qelimValues.[idx]
    let result = complex_qelim (parse formula)
    let result1 = sprint_fol_formula result
    result1
    |> should equal stringResult

[<TestCase(42, TestName = "complex.p050")>]
[<TestCase(44, TestName = "complex.p052", Category = "LongRunning")>]
[<TestCase(45, TestName = "complex.p053", Category = "LongRunning")>]
[<TestCase(46, TestName = "complex.p054")>]
[<TestCase(47, TestName = "complex.p055")>]
[<TestCase(48, TestName = "complex.p056")>]
[<TestCase(49, TestName = "complex.p057", Category = "LongRunning")>]
[<TestCase(53, TestName = "complex.p061")>]
[<TestCase(54, TestName = "complex.p062", Category = "LongRunning")>]

[<Test>]
let ``complex_qelim_all tests`` idx = 
    let complex_qelim_all =
        time complex_qelim << generalize
    let (formula, _, _) = complex_qelimValues.[idx]
    let (_, astResult, _) = complex_qelimValues.[idx]
    let (_, _, stringResult) = complex_qelimValues.[idx]
    let result = complex_qelim_all (parse formula)
    result
    |> should equal astResult
    let result1 = sprint_fol_formula result
    result1
    |> should equal stringResult
    
let polytestValues : (string * term  * string)[] = [|
    (
        // idx 
        // complex.p006
        @"(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
            ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
        ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2)  +
            (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2)  +
            (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2)  +
            (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))",
        Fn ("0",[]),
        @"<<|0|>>"
    );
    (
        // idx 
        // complex.p007
        @"((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
        (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
        ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
        (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
        (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
        (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
        (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
        (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
        (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
        (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)",
        Fn ("0",[]),
        @"<<|0|>>"
    );
    (
        // idx 
        // complex.p008
        @"6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
        (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
            (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
            ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
            (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))",
        Fn ("0",[]),
        @"<<|0|>>"
    );
    (
        // idx 
        // complex.p009
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
            36 * (x1^6 + x2^6 + x3^6 + x4^6))",
        Fn ("0",[]),
        @"<<|0|>>"
    );
    (
        // idx 
        // complex.p010
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
            6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))",
        Fn ("0",[]),
        @"<<|0|>>"
    );
    (
        // idx 
        // complex.p011
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
                (x1 - x2 - x3 - x4)^10))",
        Fn ("0",[]),
        @"<<|0|>>"
    );
    (
        // idx 
        // complex.p083
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
        (0 - x_9 * y_8 + x_8 * y_9 + x_7 * y_10 - x_6 * y_11 - x_5 * y_12 + x_4 * y_13 + x_3 * y_14 - x_2 * y_15 + x_1 * y_16)^2)",
        Fn ("0",[]),
        @"<<|0|>>"
    );
    |]

[<TestCase(0, TestName = "complex.p006")>]
[<TestCase(1, TestName = "complex.p007")>]
[<TestCase(2, TestName = "complex.p008")>]
[<TestCase(3, TestName = "complex.p009")>]
[<TestCase(4, TestName = "complex.p010")>]
[<TestCase(5, TestName = "complex.p011")>]
[<TestCase(0, TestName = "complex.p083")>]

[<Test>]
let ``polytest tests`` idx = 
    let polytest tm =
        time (polynate (fvt tm)) tm
    let (formula, _, _) = polytestValues.[idx]
    let (_, astResult, _) = polytestValues.[idx]
    let (_, _, stringResult) = polytestValues.[idx]
    let result = polytest (parset formula)
    result
    |> should equal astResult
    let result1 = sprint_term result
    result1
    |> should equal stringResult

// ===============================================================================
//
//let private example_results_1 : formula<fol>[] = [|
//    formula<fol>.True;
//    Atom
//     (R ("=",
//       [Fn ("+",
//         [Fn ("1", []);
//          Fn ("*",
//           [Var "c";
//            Fn ("+",
//             [Fn ("-4", []);
//              Fn ("*",
//               [Var "c";
//                Fn ("+",
//                 [Fn ("6", []);
//                  Fn ("*",
//                   [Var "c";
//                    Fn ("+",
//                     [Fn ("-4", []); Fn ("*", [Var "c"; Fn ("1", [])])])])])])])])]);
//        Fn ("0", [])]));
//    formula<fol>.True;
//    formula<fol>.True;
//    |]
//
//// complex.p002
//[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0", 0)>]
//
//// complex.p003
//[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0", 1)>]
//
//// complex.p004
//[<TestCase(@"forall c. (forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0) <=> c = 1", 2)>]
//
//// complex.p005
//[<TestCase(@"forall a b c x y.
//              a * x^2 + b * x + c = 0 /\ a * y^2 + b * y + c = 0 /\ ~(x = y)
//              ==> a * x * y = c /\ a * (x + y) + b = 0", 3)>]
//
//let ``examples 1`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_1.[idx]
//
//
//(* ------------------------------------------------------------------------- *)
//(* More tests, not in the main text.                                         *)
//(* ------------------------------------------------------------------------- *)
//
//// Helper function
//let private polytest tm =
//    polynate (fvt tm) tm
//
//// complex.p006
//[<Test>]
//let ``lagrange_4``() =
//    parset @"(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
//     ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
//    ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2) +
//     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2) +
//     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2) +
//     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))"
//    |> polytest
//    |> should equal
//    <| Fn ("0", [])
//
//// complex.p007
//[<Test>]
//let ``lagrange_8``() =
//    parset @"((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
//     (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
//     ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
//      (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
//      (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
//      (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
//      (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
//      (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
//      (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
//      (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)"
//    |> polytest
//    |> should equal
//    <| Fn ("0", [])
//
//// complex.p008
//[<Test>]
//let ``liouville``() =
//    parset @"6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
//    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
//      (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
//     ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
//      (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))"
//    |> polytest
//    |> should equal
//    <| Fn ("0", [])
//
//// complex.p009
//[<Test>]
//let ``fleck``() =
//    parset @"60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
//    (((x1 + x2 + x3)^6 + (x1 + x2 - x3)^6 +
//      (x1 - x2 + x3)^6 + (x1 - x2 - x3)^6 +
//      (x1 + x2 + x4)^6 + (x1 + x2 - x4)^6 +
//      (x1 - x2 + x4)^6 + (x1 - x2 - x4)^6 +
//      (x1 + x3 + x4)^6 + (x1 + x3 - x4)^6 +
//      (x1 - x3 + x4)^6 + (x1 - x3 - x4)^6 +
//      (x2 + x3 + x4)^6 + (x2 + x3 - x4)^6 +
//      (x2 - x3 + x4)^6 + (x2 - x3 - x4)^6) +
//     2 * ((x1 + x2)^6 + (x1 - x2)^6 +
//          (x1 + x3)^6 + (x1 - x3)^6 +
//          (x1 + x4)^6 + (x1 - x4)^6 +
//          (x2 + x3)^6 + (x2 - x3)^6 +
//          (x2 + x4)^6 + (x2 - x4)^6 +
//          (x3 + x4)^6 + (x3 - x4)^6) +
//     36 * (x1^6 + x2^6 + x3^6 + x4^6))"
//    |> polytest
//    |> should equal
//    <| Fn ("0", [])
//
//// complex.p010
//[<Test>]
//let ``hurwitz``() =
//    parset @"5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
//    (6 * ((x1 + x2 + x3 + x4)^8 +
//          (x1 + x2 + x3 - x4)^8 +
//          (x1 + x2 - x3 + x4)^8 +
//          (x1 + x2 - x3 - x4)^8 +
//          (x1 - x2 + x3 + x4)^8 +
//          (x1 - x2 + x3 - x4)^8 +
//          (x1 - x2 - x3 + x4)^8 +
//          (x1 - x2 - x3 - x4)^8) +
//     ((2 * x1 + x2 + x3)^8 +
//      (2 * x1 + x2 - x3)^8 +
//      (2 * x1 - x2 + x3)^8 +
//      (2 * x1 - x2 - x3)^8 +
//      (2 * x1 + x2 + x4)^8 +
//      (2 * x1 + x2 - x4)^8 +
//      (2 * x1 - x2 + x4)^8 +
//      (2 * x1 - x2 - x4)^8 +
//      (2 * x1 + x3 + x4)^8 +
//      (2 * x1 + x3 - x4)^8 +
//      (2 * x1 - x3 + x4)^8 +
//      (2 * x1 - x3 - x4)^8 +
//      (2 * x2 + x3 + x4)^8 +
//      (2 * x2 + x3 - x4)^8 +
//      (2 * x2 - x3 + x4)^8 +
//      (2 * x2 - x3 - x4)^8 +
//      (x1 + 2 * x2 + x3)^8 +
//      (x1 + 2 * x2 - x3)^8 +
//      (x1 - 2 * x2 + x3)^8 +
//      (x1 - 2 * x2 - x3)^8 +
//      (x1 + 2 * x2 + x4)^8 +
//      (x1 + 2 * x2 - x4)^8 +
//      (x1 - 2 * x2 + x4)^8 +
//      (x1 - 2 * x2 - x4)^8 +
//      (x1 + 2 * x3 + x4)^8 +
//      (x1 + 2 * x3 - x4)^8 +
//      (x1 - 2 * x3 + x4)^8 +
//      (x1 - 2 * x3 - x4)^8 +
//      (x2 + 2 * x3 + x4)^8 +
//      (x2 + 2 * x3 - x4)^8 +
//      (x2 - 2 * x3 + x4)^8 +
//      (x2 - 2 * x3 - x4)^8 +
//      (x1 + x2 + 2 * x3)^8 +
//      (x1 + x2 - 2 * x3)^8 +
//      (x1 - x2 + 2 * x3)^8 +
//      (x1 - x2 - 2 * x3)^8 +
//      (x1 + x2 + 2 * x4)^8 +
//      (x1 + x2 - 2 * x4)^8 +
//      (x1 - x2 + 2 * x4)^8 +
//      (x1 - x2 - 2 * x4)^8 +
//      (x1 + x3 + 2 * x4)^8 +
//      (x1 + x3 - 2 * x4)^8 +
//      (x1 - x3 + 2 * x4)^8 +
//      (x1 - x3 - 2 * x4)^8 +
//      (x2 + x3 + 2 * x4)^8 +
//      (x2 + x3 - 2 * x4)^8 +
//      (x2 - x3 + 2 * x4)^8 +
//      (x2 - x3 - 2 * x4)^8) +
//     60 * ((x1 + x2)^8 + (x1 - x2)^8 +
//           (x1 + x3)^8 + (x1 - x3)^8 +
//           (x1 + x4)^8 + (x1 - x4)^8 +
//           (x2 + x3)^8 + (x2 - x3)^8 +
//           (x2 + x4)^8 + (x2 - x4)^8 +
//           (x3 + x4)^8 + (x3 - x4)^8) +
//     6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))"
//    |> polytest
//    |> should equal
//    <| Fn ("0", [])
//
//// complex.p011
//[<Test>]
//let ``schur``() =
//    parset @"22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
//    (9 * ((2 * x1)^10 +
//          (2 * x2)^10 +
//          (2 * x3)^10 +
//          (2 * x4)^10) +
//     180 * ((x1 + x2)^10 + (x1 - x2)^10 +
//            (x1 + x3)^10 + (x1 - x3)^10 +
//            (x1 + x4)^10 + (x1 - x4)^10 +
//            (x2 + x3)^10 + (x2 - x3)^10 +
//            (x2 + x4)^10 + (x2 - x4)^10 +
//            (x3 + x4)^10 + (x3 - x4)^10) +
//     ((2 * x1 + x2 + x3)^10 +
//      (2 * x1 + x2 - x3)^10 +
//      (2 * x1 - x2 + x3)^10 +
//      (2 * x1 - x2 - x3)^10 +
//      (2 * x1 + x2 + x4)^10 +
//      (2 * x1 + x2 - x4)^10 +
//      (2 * x1 - x2 + x4)^10 +
//      (2 * x1 - x2 - x4)^10 +
//      (2 * x1 + x3 + x4)^10 +
//      (2 * x1 + x3 - x4)^10 +
//      (2 * x1 - x3 + x4)^10 +
//      (2 * x1 - x3 - x4)^10 +
//      (2 * x2 + x3 + x4)^10 +
//      (2 * x2 + x3 - x4)^10 +
//      (2 * x2 - x3 + x4)^10 +
//      (2 * x2 - x3 - x4)^10 +
//      (x1 + 2 * x2 + x3)^10 +
//      (x1 + 2 * x2 - x3)^10 +
//      (x1 - 2 * x2 + x3)^10 +
//      (x1 - 2 * x2 - x3)^10 +
//      (x1 + 2 * x2 + x4)^10 +
//      (x1 + 2 * x2 - x4)^10 +
//      (x1 - 2 * x2 + x4)^10 +
//      (x1 - 2 * x2 - x4)^10 +
//      (x1 + 2 * x3 + x4)^10 +
//      (x1 + 2 * x3 - x4)^10 +
//      (x1 - 2 * x3 + x4)^10 +
//      (x1 - 2 * x3 - x4)^10 +
//      (x2 + 2 * x3 + x4)^10 +
//      (x2 + 2 * x3 - x4)^10 +
//      (x2 - 2 * x3 + x4)^10 +
//      (x2 - 2 * x3 - x4)^10 +
//      (x1 + x2 + 2 * x3)^10 +
//      (x1 + x2 - 2 * x3)^10 +
//      (x1 - x2 + 2 * x3)^10 +
//      (x1 - x2 - 2 * x3)^10 +
//      (x1 + x2 + 2 * x4)^10 +
//      (x1 + x2 - 2 * x4)^10 +
//      (x1 - x2 + 2 * x4)^10 +
//      (x1 - x2 - 2 * x4)^10 +
//      (x1 + x3 + 2 * x4)^10 +
//      (x1 + x3 - 2 * x4)^10 +
//      (x1 - x3 + 2 * x4)^10 +
//      (x1 - x3 - 2 * x4)^10 +
//      (x2 + x3 + 2 * x4)^10 +
//      (x2 + x3 - 2 * x4)^10 +
//      (x2 - x3 + 2 * x4)^10 +
//      (x2 - x3 - 2 * x4)^10) +
//     9 * ((x1 + x2 + x3 + x4)^10 +
//          (x1 + x2 + x3 - x4)^10 +
//          (x1 + x2 - x3 + x4)^10 +
//          (x1 + x2 - x3 - x4)^10 +
//          (x1 - x2 + x3 + x4)^10 +
//          (x1 - x2 + x3 - x4)^10 +
//          (x1 - x2 - x3 + x4)^10 +
//          (x1 - x2 - x3 - x4)^10))"
//    |> polytest
//    |> should equal
//    <| Fn ("0", [])
//
//let private example_results_2 : formula<fol>[] = [|
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.False;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.False;
//    formula<fol>.True;
//    And
//     (Or
//       (Not
//         (Atom
//           (R ("=",
//             [Fn ("+",
//               [Fn ("9", []);
//                Fn ("*",
//                 [Var "a";
//                  Fn ("+",
//                   [Fn ("0", []);
//                    Fn ("*",
//                     [Var "a";
//                      Fn ("+",
//                       [Fn ("-10", []);
//                        Fn ("*",
//                         [Var "a";
//                          Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*",
//                             [Var "a";
//                              Fn ("+",
//                               [Fn ("5", []);
//                                Fn ("*",
//                                 [Var "a";
//                                  Fn ("+",
//                                   [Fn ("0", []);
//                                    Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])]);
//              Fn ("0", [])]))),
//       Not
//        (Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("0", []);
//               Fn ("*",
//                [Var "a";
//                 Fn ("+",
//                  [Fn ("12", []);
//                   Fn ("*",
//                    [Var "a";
//                     Fn ("+",
//                      [Fn ("0", []);
//                       Fn ("*",
//                        [Var "a";
//                         Fn ("+",
//                          [Fn ("-14", []);
//                           Fn ("*",
//                            [Var "a";
//                             Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*",
//                                [Var "a";
//                                 Fn ("+",
//                                  [Fn ("6", []);
//                                   Fn ("*",
//                                    [Var "a";
//                                     Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])])])]);
//             Fn ("0", [])])))),
//     Atom
//      (R ("=",
//        [Fn ("+",
//          [Fn ("-2", []);
//           Fn ("*",
//            [Var "a";
//             Fn ("+", [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])])])]);
//         Fn ("0", [])])));
//    Not
//     (Or
//       (Not
//         (Atom
//           (R ("=",
//             [Fn ("+",
//               [Fn ("9", []);
//                Fn ("*",
//                 [Var "a";
//                  Fn ("+",
//                   [Fn ("0", []);
//                    Fn ("*",
//                     [Var "a";
//                      Fn ("+",
//                       [Fn ("-10", []);
//                        Fn ("*",
//                         [Var "a";
//                          Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*",
//                             [Var "a";
//                              Fn ("+",
//                               [Fn ("5", []);
//                                Fn ("*",
//                                 [Var "a";
//                                  Fn ("+",
//                                   [Fn ("0", []);
//                                    Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])]);
//              Fn ("0", [])]))),
//       Not
//        (Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("0", []);
//               Fn ("*",
//                [Var "a";
//                 Fn ("+",
//                  [Fn ("12", []);
//                   Fn ("*",
//                    [Var "a";
//                     Fn ("+",
//                      [Fn ("0", []);
//                       Fn ("*",
//                        [Var "a";
//                         Fn ("+",
//                          [Fn ("-14", []);
//                           Fn ("*",
//                            [Var "a";
//                             Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*",
//                                [Var "a";
//                                 Fn ("+",
//                                  [Fn ("6", []);
//                                   Fn ("*",
//                                    [Var "a";
//                                     Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*", [Var "a"; Fn ("-1", [])])])])])])])])])])])])])])]);
//             Fn ("0", [])])))));
//    Not
//     (And
//       (Or
//         (And
//           (Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
//                Fn ("0", [])])),
//           Atom
//            (R ("=",
//              [Fn ("+",
//                [Fn ("1", []);
//                 Fn ("*",
//                  [Var "x";
//                   Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//               Fn ("0", [])]))),
//         And
//          (Not
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
//                 Fn ("0", [])]))),
//          Atom
//           (R ("=",
//             [Fn ("+",
//               [Fn ("1", []);
//                Fn ("*",
//                 [Var "x";
//                  Fn ("+",
//                   [Fn ("0", []);
//                    Fn ("*",
//                     [Var "x";
//                      Fn ("+",
//                       [Fn ("0", []);
//                        Fn ("*",
//                         [Var "x";
//                          Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])]);
//              Fn ("0", [])])))),
//       Not
//        (Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("2", []);
//               Fn ("*",
//                [Var "x";
//                 Fn ("+",
//                  [Fn ("0", []);
//                   Fn ("*",
//                    [Var "x";
//                     Fn ("+",
//                      [Fn ("0", []);
//                       Fn ("*",
//                        [Var "x";
//                         Fn ("+",
//                          [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])]);
//             Fn ("0", [])])))));
//    formula<fol>.False;
//    formula<fol>.False;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    |]
//
//// complex.p012
//[<TestCase(@"exists x. x + 2 = 3", 0)>]
//
//// complex.p013
//[<TestCase(@"exists x. x^2 + a = 3", 1)>]
//
//// complex.p014
//[<TestCase(@"exists x. x^2 + x + 1 = 0", 2)>]
//
//// complex.p015
//[<TestCase(@"exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0", 3)>]
//
//// complex.p016
//[<TestCase(@"exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0", 4)>]
//
//// complex.p017
//[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0", 5)>]
//
//// complex.p018
//[<TestCase(@"forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 6)>]
//
//// complex.p019
//[<TestCase(@"exists a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)", 7)>]
//
//// complex.p020
//[<TestCase(@"exists x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)", 8)>]
//
//// complex.p021
//[<TestCase(@"forall x. x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 9)>]
//
//// complex.p022
//[<TestCase(@"forall a. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0", 10)>]
//
//// complex.p023
//[<TestCase(@"exists a b c x y.
//                a * x^2 + b * x + c = 0 /\
//                a * y^2 + b * y + c = 0 /\
//                ~(x = y) /\
//                ~(a * x * y = c)", 11)>]
//
//// complex.p026
//[<TestCase(@"forall a b c x.
//            (forall z. a * z^2 + b * z + c = 0 <=> z = x)
//            ==> a * x * x = c /\ a * (x + x) + b = 0", 12)>]
//
//// complex.p027
//[<TestCase(@"forall x y.
//            (forall a b c. (a * x^2 + b * x + c = 0) /\
//                   (a * y^2 + b * y + c = 0)
//                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
//                    <=> ~(x = y)", 13)>]
//
//// complex.p028
//[<TestCase(@"forall y_1 y_2 y_3 y_4.
//             (y_1 = 2 * y_3) /\
//             (y_2 = 2 * y_4) /\
//             (y_1 * y_3 = y_2 * y_4)
//             ==> (y_1^2 = y_2^2)", 14)>]
//
//// complex.p029
//[<TestCase(@"forall x y. x^2 = 2 /\ y^2 = 3
//                ==> (x * y)^2 = 6", 15)>]
//// complex.p030
//[<TestCase(@"forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
//                ==> (x^4 + 1 = 0)", 16)>]
//
//// complex.p031
//[<TestCase(@"forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
//                ==> (x^4 + 1 = 0)", 17)>]
//
//// complex.p032
//[<TestCase(@"~(exists a x y. (a^2 = 2) /\
//             (x^2 + a * x + 1 = 0) /\
//             (y * (x^4 + 1) + 1 = 0))", 18)>]
//
//// complex.p033
//[<TestCase(@"forall x. exists y. x^2 = y^3", 19)>]
//
//// complex.p034
//[<TestCase(@"forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
//               2 * (b * x + b * z - a * y)", 20)>]
//
//// complex.p035
//[<TestCase(@"forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)", 21)>]
//
//// complex.p036
//[<TestCase(@"forall a b c x y. (a * x^2 + b * x + c = 0) /\
//               (a * y^2 + b * y + c = 0) /\
//               ~(x = y)
//               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", 22)>]
//
//// complex.p037
//[<TestCase(@"~(forall a b c x y. (a * x^2 + b * x + c = 0) /\
//                 (a * y^2 + b * y + c = 0)
//                 ==> (a * x * y = c) /\ (a * (x + y) + b = 0))", 23)>]
//
//// complex.p038
//[<TestCase(@"forall y_1 y_2 y_3 y_4.
//     (y_1 = 2 * y_3) /\
//     (y_2 = 2 * y_4) /\
//     (y_1 * y_3 = y_2 * y_4)
//     ==> (y_1^2 = y_2^2)", 24)>]
//
//// complex.p039
//[<TestCase(@"forall a1 b1 c1 a2 b2 c2.
//            ~(a1 * b2 = a2 * b1)
//            ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)", 25)>]
//
//let ``examples 2`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_2.[idx]
//
//
//(* ------------------------------------------------------------------------- *)
//(* This seems harder, so see how many quantifiers are feasible.              *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_3 : formula<fol>[] = [|
//    Imp
//     (And
//       (Atom
//         (R ("=",
//           [Fn ("+",
//             [Fn ("+",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                Fn ("*",
//                 [Var "b";
//                  Fn ("+",
//                   [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//              Fn ("*",
//               [Var "a";
//                Fn ("+",
//                 [Fn ("0", []);
//                  Fn ("*",
//                   [Var "x";
//                    Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])]);
//            Fn ("0", [])])),
//       And
//        (Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("+",
//                [Fn ("+",
//                  [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                 Fn ("*",
//                  [Var "b";
//                   Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])]);
//               Fn ("*",
//                [Var "a";
//                 Fn ("+",
//                  [Fn ("0", []);
//                   Fn ("*",
//                    [Var "y";
//                     Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])])])]);
//             Fn ("0", [])])),
//        Not
//         (Or
//           (And
//             (Atom
//               (R ("=",
//                 [Fn ("+",
//                   [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                  Fn ("0", [])])),
//             Or
//              (And
//                (Atom
//                  (R ("=",
//                    [Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                     Fn ("0", [])])),
//                Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                    Fn ("0", [])]))),
//              And
//               (Not
//                 (Atom
//                   (R ("=",
//                     [Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                      Fn ("0", [])]))),
//               Not
//                (Atom
//                  (R ("=",
//                    [Fn ("+",
//                      [Fn ("+",
//                        [Fn ("0", []);
//                         Fn ("*",
//                          [Var "c";
//                           Fn ("+",
//                            [Fn ("0", []);
//                             Fn ("*", [Var "c"; Fn ("1", [])])])])]);
//                       Fn ("*",
//                        [Var "b";
//                         Fn ("+",
//                          [Fn ("+",
//                            [Fn ("0", []);
//                             Fn ("*",
//                              [Var "c";
//                               Fn ("+",
//                                [Fn ("+",
//                                  [Fn ("0", []);
//                                   Fn ("*", [Var "y"; Fn ("1", [])])]);
//                                 Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//                           Fn ("*",
//                            [Var "b";
//                             Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*",
//                                [Var "x";
//                                 Fn ("+",
//                                  [Fn ("0", []);
//                                   Fn ("*", [Var "y"; Fn ("1", [])])])])])])])])]);
//                     Fn ("0", [])])))))),
//           And
//            (Not
//              (Atom
//                (R ("=",
//                  [Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                   Fn ("0", [])]))),
//            Or
//             (Not
//               (Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("+",
//                       [Fn ("0", []);
//                        Fn ("*",
//                         [Var "b";
//                          Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*",
//                             [Var "b";
//                              Fn ("+",
//                               [Fn ("0", []);
//                                Fn ("*", [Var "c"; Fn ("-1", [])])])])])])]);
//                      Fn ("*",
//                       [Var "a";
//                        Fn ("+",
//                         [Fn ("+",
//                           [Fn ("+",
//                             [Fn ("0", []);
//                              Fn ("*",
//                               [Var "c";
//                                Fn ("+",
//                                 [Fn ("0", []);
//                                  Fn ("*", [Var "c"; Fn ("1", [])])])])]);
//                            Fn ("*",
//                             [Var "b";
//                              Fn ("+",
//                               [Fn ("0", []);
//                                Fn ("*",
//                                 [Var "c";
//                                  Fn ("+",
//                                   [Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*", [Var "y"; Fn ("-2", [])])]);
//                                    Fn ("*", [Var "x"; Fn ("-2", [])])])])])])]);
//                          Fn ("*",
//                           [Var "a";
//                            Fn ("+",
//                             [Fn ("+",
//                               [Fn ("0", []);
//                                Fn ("*",
//                                 [Var "c";
//                                  Fn ("+",
//                                   [Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*",
//                                       [Var "y";
//                                        Fn ("+",
//                                         [Fn ("0", []);
//                                          Fn ("*",
//                                           [Var "y"; Fn ("-1", [])])])])]);
//                                    Fn ("*",
//                                     [Var "x";
//                                      Fn ("+",
//                                       [Fn ("+",
//                                         [Fn ("0", []);
//                                          Fn ("*",
//                                           [Var "y"; Fn ("-4", [])])]);
//                                        Fn ("*", [Var "x"; Fn ("-1", [])])])])])])]);
//                              Fn ("*",
//                               [Var "a";
//                                Fn ("+",
//                                 [Fn ("0", []);
//                                  Fn ("*",
//                                   [Var "x";
//                                    Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*",
//                                       [Var "x";
//                                        Fn ("+",
//                                         [Fn ("0", []);
//                                          Fn ("*",
//                                           [Var "y";
//                                            Fn ("+",
//                                             [Fn ("0", []);
//                                              Fn ("*",
//                                               [Var "y"; Fn ("1", [])])])])])])])])])])])])])])]);
//                    Fn ("0", [])]))),
//             Not
//              (Atom
//                (R ("=",
//                  [Fn ("+",
//                    [Fn ("+",
//                      [Fn ("0", []);
//                       Fn ("*",
//                        [Var "b";
//                         Fn ("+",
//                          [Fn ("0", []);
//                           Fn ("*",
//                            [Var "b";
//                             Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*", [Var "b"; Fn ("-1", [])])])])])])]);
//                     Fn ("*",
//                      [Var "a";
//                       Fn ("+",
//                        [Fn ("+",
//                          [Fn ("0", []);
//                           Fn ("*",
//                            [Var "b";
//                             Fn ("+",
//                              [Fn ("+",
//                                [Fn ("0", []);
//                                 Fn ("*", [Var "c"; Fn ("2", [])])]);
//                               Fn ("*",
//                                [Var "b";
//                                 Fn ("+",
//                                  [Fn ("+",
//                                    [Fn ("0", []);
//                                     Fn ("*", [Var "y"; Fn ("-2", [])])]);
//                                   Fn ("*", [Var "x"; Fn ("-2", [])])])])])])]);
//                         Fn ("*",
//                          [Var "a";
//                           Fn ("+",
//                            [Fn ("+",
//                              [Fn ("+",
//                                [Fn ("0", []);
//                                 Fn ("*",
//                                  [Var "c";
//                                   Fn ("+",
//                                    [Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*", [Var "y"; Fn ("2", [])])]);
//                                     Fn ("*", [Var "x"; Fn ("2", [])])])])]);
//                               Fn ("*",
//                                [Var "b";
//                                 Fn ("+",
//                                  [Fn ("+",
//                                    [Fn ("0", []);
//                                     Fn ("*",
//                                      [Var "y";
//                                       Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*", [Var "y"; Fn ("-1", [])])])])]);
//                                   Fn ("*",
//                                    [Var "x";
//                                     Fn ("+",
//                                      [Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*", [Var "y"; Fn ("-4", [])])]);
//                                       Fn ("*", [Var "x"; Fn ("-1", [])])])])])])]);
//                             Fn ("*",
//                              [Var "a";
//                               Fn ("+",
//                                [Fn ("0", []);
//                                 Fn ("*",
//                                  [Var "x";
//                                   Fn ("+",
//                                    [Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*",
//                                        [Var "y";
//                                         Fn ("+",
//                                          [Fn ("0", []);
//                                           Fn ("*",
//                                            [Var "y"; Fn ("-2", [])])])])]);
//                                     Fn ("*",
//                                      [Var "x";
//                                       Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*", [Var "y"; Fn ("-2", [])])])])])])])])])])])])]);
//                   Fn ("0", [])]))))))))),
//     And
//      (Atom
//        (R ("=",
//          [Fn ("+",
//            [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("-1", [])])]);
//             Fn ("*",
//              [Var "a";
//               Fn ("+",
//                [Fn ("0", []);
//                 Fn ("*",
//                  [Var "x";
//                   Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])])])]);
//           Fn ("0", [])])),
//      Atom
//       (R ("=",
//         [Fn ("+",
//           [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//            Fn ("*",
//             [Var "a";
//              Fn ("+",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
//                Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//          Fn ("0", [])]))));
//    formula<fol>.True;   // CPU time (user): 0.100007
//    formula<fol>.True;   // CPU time (user): 0.240015
//    formula<fol>.True;   // CPU time (user): 9.888617
//    Not     // CPU time (user): 0.004
//     (And
//       (And
//         (Atom
//           (R ("=",
//             [Fn ("+",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
//                Fn ("*", [Var "x"; Fn ("-1", [])])]);
//              Fn ("0", [])])),
//         Or
//          (Atom
//            (R ("=",
//              [Fn ("+",
//                [Fn ("+",
//                  [Fn ("0", []);
//                   Fn ("*",
//                    [Var "y";
//                     Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])]);
//                 Fn ("*",
//                  [Var "x";
//                   Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-1", [])])])])]);
//               Fn ("0", [])])),
//          Not
//           (Atom
//             (R ("=",
//               [Fn ("+",
//                 [Fn ("+",
//                   [Fn ("0", []);
//                    Fn ("*",
//                     [Var "y";
//                      Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])])])]);
//                  Fn ("*",
//                   [Var "x";
//                    Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-1", [])])])])]);
//                Fn ("0", [])]))))),
//       Not
//        (Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("-1", [])])]);
//               Fn ("*", [Var "x"; Fn ("1", [])])]);
//             Fn ("0", [])])))));
//    Not     // CPU time (user): 0.008001
//     (And
//       (And
//         (Atom
//           (R ("=",
//             [Fn ("+",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("2", [])])]);
//                Fn ("*", [Var "x"; Fn ("-2", [])])]);
//              Fn ("0", [])])),
//         Or
//          (Atom
//            (R ("=",
//              [Fn ("+",
//                [Fn ("+",
//                  [Fn ("0", []);
//                   Fn ("*",
//                    [Var "y";
//                     Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "y"; Fn ("2", [])])])])]);
//                 Fn ("*",
//                  [Var "x";
//                   Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-2", [])])])])]);
//               Fn ("0", [])])),
//          Not
//           (Atom
//             (R ("=",
//               [Fn ("+",
//                 [Fn ("+",
//                   [Fn ("0", []);
//                    Fn ("*",
//                     [Var "y";
//                      Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "y"; Fn ("2", [])])])])]);
//                  Fn ("*",
//                   [Var "x";
//                    Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("-2", [])])])])]);
//                Fn ("0", [])]))))),
//       Not
//        (Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("-1", [])])]);
//               Fn ("*", [Var "x"; Fn ("1", [])])]);
//             Fn ("0", [])])))));
//    formula<fol>.True;   // CPU time (user): 0.008
//    Not     // CPU time (user): 0.032002
//     (Or
//       (And
//         (Or
//           (And
//             (Atom
//               (R ("=",
//                 [Fn ("+",
//                   [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                  Fn ("0", [])])),
//             Or
//              (And
//                (Atom
//                  (R ("=",
//                    [Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                     Fn ("0", [])])),
//                And
//                 (Atom
//                   (R ("=",
//                     [Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                      Fn ("0", [])])),
//                 Not
//                  (Atom
//                    (R ("=",
//                      [Fn ("+",
//                        [Fn ("0", []);
//                         Fn ("*",
//                          [Var "a";
//                           Fn ("+",
//                            [Fn ("0", []);
//                             Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//                       Fn ("0", [])]))))),
//              And
//               (Not
//                 (Atom
//                   (R ("=",
//                     [Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                      Fn ("0", [])]))),
//               Not
//                (Atom
//                  (R ("=",
//                    [Fn ("+",
//                      [Fn ("+",
//                        [Fn ("0", []);
//                         Fn ("*",
//                          [Var "b";
//                           Fn ("+",
//                            [Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*",
//                                [Var "c";
//                                 Fn ("+",
//                                  [Fn ("0", []);
//                                   Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
//                             Fn ("*",
//                              [Var "b";
//                               Fn ("+",
//                                [Fn ("0", []);
//                                 Fn ("*",
//                                  [Var "c";
//                                   Fn ("+",
//                                    [Fn ("0", []);
//                                     Fn ("*", [Var "x"; Fn ("-1", [])])])])])])])])]);
//                       Fn ("*",
//                        [Var "a";
//                         Fn ("+",
//                          [Fn ("+",
//                            [Fn ("0", []);
//                             Fn ("*",
//                              [Var "c";
//                               Fn ("+",
//                                [Fn ("0", []);
//                                 Fn ("*",
//                                  [Var "c";
//                                   Fn ("+",
//                                    [Fn ("0", []);
//                                     Fn ("*", [Var "x"; Fn ("-1", [])])])])])])]);
//                           Fn ("*",
//                            [Var "b";
//                             Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*",
//                                [Var "c";
//                                 Fn ("+",
//                                  [Fn ("0", []);
//                                   Fn ("*",
//                                    [Var "x";
//                                     Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*", [Var "x"; Fn ("-1", [])])])])])])])])])])]);
//                     Fn ("0", [])])))))),
//           And
//            (Not
//              (Atom
//                (R ("=",
//                  [Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                   Fn ("0", [])]))),
//            Or
//             (Not
//               (Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("0", []);
//                      Fn ("*",
//                       [Var "a";
//                        Fn ("+",
//                         [Fn ("0", []);
//                          Fn ("*",
//                           [Var "a";
//                            Fn ("+",
//                             [Fn ("+",
//                               [Fn ("+",
//                                 [Fn ("0", []);
//                                  Fn ("*",
//                                   [Var "c";
//                                    Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*",
//                                       [Var "c";
//                                        Fn ("+",
//                                         [Fn ("0", []);
//                                          Fn ("*",
//                                           [Var "c"; Fn ("-1", [])])])])])])]);
//                                Fn ("*",
//                                 [Var "b";
//                                  Fn ("+",
//                                   [Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*",
//                                       [Var "c";
//                                        Fn ("+",
//                                         [Fn ("0", []);
//                                          Fn ("*",
//                                           [Var "c";
//                                            Fn ("+",
//                                             [Fn ("0", []);
//                                              Fn ("*",
//                                               [Var "x"; Fn ("-2", [])])])])])])]);
//                                    Fn ("*",
//                                     [Var "b";
//                                      Fn ("+",
//                                       [Fn ("0", []);
//                                        Fn ("*",
//                                         [Var "c";
//                                          Fn ("+",
//                                           [Fn ("0", []);
//                                            Fn ("*",
//                                             [Var "x";
//                                              Fn ("+",
//                                               [Fn ("0", []);
//                                                Fn ("*",
//                                                 [Var "x"; Fn ("-1", [])])])])])])])])])])]);
//                              Fn ("*",
//                               [Var "a";
//                                Fn ("+",
//                                 [Fn ("+",
//                                   [Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*",
//                                       [Var "c";
//                                        Fn ("+",
//                                         [Fn ("0", []);
//                                          Fn ("*",
//                                           [Var "c";
//                                            Fn ("+",
//                                             [Fn ("0", []);
//                                              Fn ("*",
//                                               [Var "x";
//                                                Fn ("+",
//                                                 [Fn ("0", []);
//                                                  Fn ("*",
//                                                   [Var "x"; Fn ("-2", [])])])])])])])])]);
//                                    Fn ("*",
//                                     [Var "b";
//                                      Fn ("+",
//                                       [Fn ("0", []);
//                                        Fn ("*",
//                                         [Var "c";
//                                          Fn ("+",
//                                           [Fn ("0", []);
//                                            Fn ("*",
//                                             [Var "x";
//                                              Fn ("+",
//                                               [Fn ("0", []);
//                                                Fn ("*",
//                                                 [Var "x";
//                                                  Fn ("+",
//                                                   [Fn ("0", []);
//                                                    Fn ("*",
//                                                     [Var "x";
//                                                      Fn ("-2", [])])])])])])])])])])]);
//                                  Fn ("*",
//                                   [Var "a";
//                                    Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*",
//                                       [Var "c";
//                                        Fn ("+",
//                                         [Fn ("0", []);
//                                          Fn ("*",
//                                           [Var "x";
//                                            Fn ("+",
//                                             [Fn ("0", []);
//                                              Fn ("*",
//                                               [Var "x";
//                                                Fn ("+",
//                                                 [Fn ("0", []);
//                                                  Fn ("*",
//                                                   [Var "x";
//                                                    Fn ("+",
//                                                     [Fn ("0", []);
//                                                      Fn ("*",
//                                                       [Var "x";
//                                                        Fn ("-1", [])])])])])])])])])])])])])])])])])])]);
//                    Fn ("0", [])]))),
//             Not
//              (Atom
//                (R ("=",
//                  [Fn ("+",
//                    [Fn ("0", []);
//                     Fn ("*",
//                      [Var "a";
//                       Fn ("+",
//                        [Fn ("0", []);
//                         Fn ("*",
//                          [Var "a";
//                           Fn ("+",
//                            [Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*",
//                                [Var "b";
//                                 Fn ("+",
//                                  [Fn ("+",
//                                    [Fn ("0", []);
//                                     Fn ("*",
//                                      [Var "c";
//                                       Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
//                                   Fn ("*",
//                                    [Var "b";
//                                     Fn ("+",
//                                      [Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*",
//                                          [Var "c";
//                                           Fn ("+",
//                                            [Fn ("0", []);
//                                             Fn ("*",
//                                              [Var "x"; Fn ("-2", [])])])])]);
//                                       Fn ("*",
//                                        [Var "b";
//                                         Fn ("+",
//                                          [Fn ("0", []);
//                                           Fn ("*",
//                                            [Var "x";
//                                             Fn ("+",
//                                              [Fn ("0", []);
//                                               Fn ("*",
//                                                [Var "x"; Fn ("-1", [])])])])])])])])])])]);
//                             Fn ("*",
//                              [Var "a";
//                               Fn ("+",
//                                [Fn ("+",
//                                  [Fn ("0", []);
//                                   Fn ("*",
//                                    [Var "b";
//                                     Fn ("+",
//                                      [Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*",
//                                          [Var "c";
//                                           Fn ("+",
//                                            [Fn ("0", []);
//                                             Fn ("*",
//                                              [Var "x";
//                                               Fn ("+",
//                                                [Fn ("0", []);
//                                                 Fn ("*",
//                                                  [Var "x"; Fn ("-2", [])])])])])])]);
//                                       Fn ("*",
//                                        [Var "b";
//                                         Fn ("+",
//                                          [Fn ("0", []);
//                                           Fn ("*",
//                                            [Var "x";
//                                             Fn ("+",
//                                              [Fn ("0", []);
//                                               Fn ("*",
//                                                [Var "x";
//                                                 Fn ("+",
//                                                  [Fn ("0", []);
//                                                   Fn ("*",
//                                                    [Var "x";
//                                                     Fn ("-2", [])])])])])])])])])])]);
//                                 Fn ("*",
//                                  [Var "a";
//                                   Fn ("+",
//                                    [Fn ("0", []);
//                                     Fn ("*",
//                                      [Var "b";
//                                       Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*",
//                                          [Var "x";
//                                           Fn ("+",
//                                            [Fn ("0", []);
//                                             Fn ("*",
//                                              [Var "x";
//                                               Fn ("+",
//                                                [Fn ("0", []);
//                                                 Fn ("*",
//                                                  [Var "x";
//                                                   Fn ("+",
//                                                    [Fn ("0", []);
//                                                     Fn ("*",
//                                                      [Var "x";
//                                                       Fn ("-1", [])])])])])])])])])])])])])])])])])])]);
//                   Fn ("0", [])])))))),
//         Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("+",
//                [Fn ("+",
//                  [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                 Fn ("*",
//                  [Var "b";
//                   Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//               Fn ("*",
//                [Var "a";
//                 Fn ("+",
//                  [Fn ("0", []);
//                   Fn ("*",
//                    [Var "x";
//                     Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])]);
//             Fn ("0", [])]))),
//       And
//        (Or
//          (And
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                 Fn ("0", [])])),
//            Or
//             (And
//               (Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                    Fn ("0", [])])),
//               And
//                (Atom
//                  (R ("=",
//                    [Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                     Fn ("0", [])])),
//                Not
//                 (Atom
//                   (R ("=",
//                     [Fn ("+",
//                       [Fn ("+",
//                         [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                        Fn ("*",
//                         [Var "a";
//                          Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//                      Fn ("0", [])]))))),
//             And
//              (Not
//                (Atom
//                  (R ("=",
//                    [Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                     Fn ("0", [])]))),
//              Not
//               (Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("+",
//                       [Fn ("0", []);
//                        Fn ("*",
//                         [Var "b";
//                          Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*",
//                             [Var "b";
//                              Fn ("+",
//                               [Fn ("+",
//                                 [Fn ("0", []);
//                                  Fn ("*", [Var "c"; Fn ("1", [])])]);
//                                Fn ("*",
//                                 [Var "b";
//                                  Fn ("+",
//                                   [Fn ("0", []);
//                                    Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])]);
//                      Fn ("*",
//                       [Var "a";
//                        Fn ("+",
//                         [Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*",
//                             [Var "c";
//                              Fn ("+",
//                               [Fn ("0", []);
//                                Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
//                          Fn ("*",
//                           [Var "b";
//                            Fn ("+",
//                             [Fn ("0", []);
//                              Fn ("*",
//                               [Var "b";
//                                Fn ("+",
//                                 [Fn ("0", []);
//                                  Fn ("*",
//                                   [Var "x";
//                                    Fn ("+",
//                                     [Fn ("0", []);
//                                      Fn ("*", [Var "x"; Fn ("1", [])])])])])])])])])])]);
//                    Fn ("0", [])])))))),
//          And
//           (Not
//             (Atom
//               (R ("=",
//                 [Fn ("+",
//                   [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                  Fn ("0", [])]))),
//           Not
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("0", []);
//                   Fn ("*",
//                    [Var "a";
//                     Fn ("+",
//                      [Fn ("0", []);
//                       Fn ("*",
//                        [Var "a";
//                         Fn ("+",
//                          [Fn ("0", []);
//                           Fn ("*",
//                            [Var "a";
//                             Fn ("+",
//                              [Fn ("+",
//                                [Fn ("+",
//                                  [Fn ("0", []);
//                                   Fn ("*",
//                                    [Var "c";
//                                     Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*", [Var "c"; Fn ("1", [])])])])]);
//                                 Fn ("*",
//                                  [Var "b";
//                                   Fn ("+",
//                                    [Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*",
//                                        [Var "c";
//                                         Fn ("+",
//                                          [Fn ("0", []);
//                                           Fn ("*",
//                                            [Var "x"; Fn ("2", [])])])])]);
//                                     Fn ("*",
//                                      [Var "b";
//                                       Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*",
//                                          [Var "x";
//                                           Fn ("+",
//                                            [Fn ("0", []);
//                                             Fn ("*",
//                                              [Var "x"; Fn ("1", [])])])])])])])])]);
//                               Fn ("*",
//                                [Var "a";
//                                 Fn ("+",
//                                  [Fn ("+",
//                                    [Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*",
//                                        [Var "c";
//                                         Fn ("+",
//                                          [Fn ("0", []);
//                                           Fn ("*",
//                                            [Var "x";
//                                             Fn ("+",
//                                              [Fn ("0", []);
//                                               Fn ("*",
//                                                [Var "x"; Fn ("2", [])])])])])])]);
//                                     Fn ("*",
//                                      [Var "b";
//                                       Fn ("+",
//                                        [Fn ("0", []);
//                                         Fn ("*",
//                                          [Var "x";
//                                           Fn ("+",
//                                            [Fn ("0", []);
//                                             Fn ("*",
//                                              [Var "x";
//                                               Fn ("+",
//                                                [Fn ("0", []);
//                                                 Fn ("*",
//                                                  [Var "x"; Fn ("2", [])])])])])])])])]);
//                                   Fn ("*",
//                                    [Var "a";
//                                     Fn ("+",
//                                      [Fn ("0", []);
//                                       Fn ("*",
//                                        [Var "x";
//                                         Fn ("+",
//                                          [Fn ("0", []);
//                                           Fn ("*",
//                                            [Var "x";
//                                             Fn ("+",
//                                              [Fn ("0", []);
//                                               Fn ("*",
//                                                [Var "x";
//                                                 Fn ("+",
//                                                  [Fn ("0", []);
//                                                   Fn ("*",
//                                                    [Var "x"; Fn ("1", [])])])])])])])])])])])])])])])])])])]);
//                 Fn ("0", [])]))))),
//        Atom
//         (R ("=",
//           [Fn ("+",
//             [Fn ("+",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                Fn ("*",
//                 [Var "b";
//                  Fn ("+",
//                   [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])]);
//              Fn ("*",
//               [Var "a";
//                Fn ("+",
//                 [Fn ("0", []);
//                  Fn ("*",
//                   [Var "x";
//                    Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])])])])])]);
//            Fn ("0", [])])))));
//    |]
//
//// complex.p040
//[<TestCase(@"(a * x^2 + b * x + c = 0) /\
//  (a * y^2 + b * y + c = 0) /\
//  (forall z. (a * z^2 + b * z + c = 0)
//       ==> (z = x) \/ (z = y))
//  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", 0)>]
//
//// complex.p041
//[<TestCase(@"~(forall x1 y1 x2 y2 x3 y3.
//      exists x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\
//                    (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2)", 1)>]
//
//// complex.p046
//[<TestCase(@"forall a b c.
//      (exists x y. (a * x^2 + b * x + c = 0) /\
//             (a * y^2 + b * y + c = 0) /\
//             ~(x = y)) <=>
//      (a = 0) /\ (b = 0) /\ (c = 0) \/
//      ~(a = 0) /\ ~(b^2 = 4 * a * c)", 2)>]
//
//// complex.p047
//[<TestCase(@"~(forall x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
//        (x1 - x0)^2 + (y1 - y0)^2 =
//        (x2 - x0)^2 + (y2 - y0)^2 /\
//        (x2 - x0)^2 + (y2 - y0)^2 =
//        (x3 - x0)^2 + (y3 - y0)^2 /\
//        (x1 - x0')^2 + (y1 - y0')^2 =
//        (x2 - x0')^2 + (y2 - y0')^2 /\
//        (x2 - x0')^2 + (y2 - y0')^2 =
//        (x3 - x0')^2 + (y3 - y0')^2
//        ==> x0 = x0' /\ y0 = y0')", 3)>]
//
//// complex.p048
//[<TestCase(@"forall a b c.
//        a * x^2 + b * x + c = 0 /\
//        a * y^2 + b * y + c = 0 /\
//        ~(x = y)
//        ==> a * (x + y) + b = 0", 4)>]
//
//// complex.p049
//[<TestCase(@"forall a b c.
//        (a * x^2 + b * x + c = 0) /\
//        (2 * a * y^2 + 2 * b * y + 2 * c = 0) /\
//        ~(x = y)
//        ==> (a * (x + y) + b = 0)", 5)>]
//
//// complex.p051
//[<TestCase(@"forall y_1 y_2 y_3 y_4.
//       (y_1 = 2 * y_3) /\
//       (y_2 = 2 * y_4) /\
//       (y_1 * y_3 = y_2 * y_4)
//       ==> (y_1^2 = y_2^2)", 6)>]
//
//// complex.p060
//[<TestCase(@"forall y.
//         a * x^2 + b * x + c = 0 /\
//         a * y^2 + b * y + c = 0 /\
//         ~(x = y)
//         ==> a * x * y = c /\ a * (x + y) + b = 0", 7)>]
//
//let ``examples 3`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_3.[idx]
//
//(* NOTE : This test case, originally from ``examples 3``, cannot be used
//            because it's printed form (from the OCaml toplevel) is over 15k lines!
//
//// complex.p041
//[<TestCase(@"forall y. (a * x^2 + b * x + c = 0) /\
//        (a * y^2 + b * y + c = 0) /\
//        (forall z. (a * z^2 + b * z + c = 0)
//                    ==> (z = x) \/ (z = y))
//        ==> (a * x * y = c) /\ (a * (x + y) + b = 0)", 1)>]
//*)
//
//let private example_results_3a : formula<fol>[] = [|
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    |]
//
//// complex.p061
//[<TestCase(@"a * x^2 + b * x + c = 0 /\
//    a * y^2 + b * y + c = 0 /\
//    ~(x = y)
//    ==> a * x * y = c /\ a * (x + y) + b = 0", 0)>]
//
//// complex.p054
//[<TestCase(@"(x1 = u3) /\
//  (x1 * (u2 - u1) = x2 * u3) /\
//  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
//  (x3 * u3 = x4 * u2) /\
//  ~(u1 = 0) /\
//  ~(u3 = 0)
//  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)", 1)>]
//
//// complex.p055
//[<TestCase(@"(u1 * x1 - u1 * u3 = 0) /\
//  (u3 * x2 - (u2 - u1) * x1 = 0) /\
//  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
//  (u3 * x4 - u2 * x3 = 0) /\
//  ~(u1 = 0) /\
//  ~(u3 = 0)
//  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)", 2)>]
//
//// complex.p056
//[<TestCase(@"(y1 * y3 + x1 * x3 = 0) /\
//  (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) /\
//  ~(x3 = 0) /\
//  ~(y3 = 0)
//  ==> (y1 * (x2 - x3) = x1 * (y2 - y3))", 3)>]
//
//// complex.p060
//[<TestCase(@"a * x^2 + b * x + c = 0 /\
//    a * y^2 + b * y + c = 0 /\
//    ~(x = y)
//    ==> a * x * y = c /\ a * (x + y) + b = 0", 4)>]
//
//let ``examples 3a`` (f, idx) =
//    parse f
//    |> generalize
//    |> complex_qelim
//    |> should equal example_results_3a.[idx]
//
//(* ------------------------------------------------------------------------- *)
//(* Checking resultants from Maple.                                           *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_4 : formula<fol>[] = [|
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    |]
//
//// complex.p063
//[<TestCase(@"forall a b c.
//           (exists x. a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0) \/ (a = 0) <=>
//           (4*a^2*c-b^2*a = 0)", 0)>]
//
//// complex.p064
//[<TestCase(@"forall a b c d e.
//            (exists x. a * x^2 + b * x + c = 0 /\ d * x + e = 0) \/
//            a = 0 /\ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0", 1)>]
//
//// complex.p065
//[<TestCase(@"forall a b c d e f.
//           (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
//           (a = 0) /\ (d = 0) <=>
//           d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0", 2)>]
//
//let ``examples 4`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_4.[idx]
//
//
//(* ------------------------------------------------------------------------- *)
//(* Some trigonometric addition formulas (checking stuff from Maple).         *)
//(* ------------------------------------------------------------------------- *)
//
//// complex.p066
//[<Test>]
//let ``examples 5``() =
//    @"forall x y. x^2 + y^2 = 1 ==> (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1"
//    |> parse
//    |> complex_qelim
//    |> should equal formula<fol>.True
//
//(* ------------------------------------------------------------------------- *)
//(* The examples from my thesis.                                              *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_6 : formula<fol>[] = [|
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    |]
//
//// complex.p068
//[<TestCase(@"forall s c. s^2 + c^2 = 1
//            ==> 2 * s - (2 * s * c * c - s^3) = 3 * s^3", 0)>]
//
//// complex.p069
//[<TestCase(@"forall u v.
//  -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
//     (((7 * u^6) * v) * v - (u * u^7)) * 144 -
//     (((5 * u^4) * v) * v - (u * u^5)) * 168 -
//     (((3 * u^2) * v) * v - (u * u^3)) * 210 -
//     (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
//   (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
//   (u^2 + v^2 - 1)", 1)>]
//
//// complex.p070
//[<TestCase(@"forall u v.
//        u^2 + v^2 = 1
//        ==> (((9 * u^8) * v) * v - (u * u^9)) * 128 +
//            (((7 * u^6) * v) * v - (u * u^7)) * 144 +
//            (((5 * u^4) * v) * v - (u * u^5)) * 168 +
//            (((3 * u^2) * v) * v - (u * u^3)) * 210 +
//            (v * v - (u * u)) * 315 + 1280 * u^10 = 315", 2)>]
//
//let ``examples 6`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_6.[idx]
//
//
//(* ------------------------------------------------------------------------- *)
//(* Deliberately silly examples from Poizat's model theory book (6.6).        *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_7 : formula<fol>[] = [|
//    Or
//     (And
//       (Atom
//         (R ("=",
//           [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
//            Fn ("0", [])])),
//       Not
//        (Atom
//          (R ("=",
//            [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
//             Fn ("0", [])])))),
//     Not
//      (Atom
//        (R ("=",
//          [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
//           Fn ("0", [])]))));
//    Not
//     (And
//       (Atom
//         (R ("=",
//           [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("1", [])])]);
//            Fn ("0", [])])),
//       Or
//        (And
//          (Atom
//            (R ("=",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("2", [])])]);
//               Fn ("0", [])])),
//          And
//           (Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "y"; Fn ("1", [])])]);
//                Fn ("0", [])])),
//           Not
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("0", []); Fn ("*", [Var "z"; Fn ("1", [])])]);
//                 Fn ("0", [])]))))),
//        And
//         (Not
//           (Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "x"; Fn ("2", [])])]);
//                Fn ("0", [])]))),
//         Not
//          (Atom
//            (R ("=",
//              [Fn ("+",
//                [Fn ("0", []);
//                 Fn ("*",
//                  [Var "x";
//                   Fn ("+",
//                    [Fn ("+",
//                      [Fn ("0", []);
//                       Fn ("*",
//                        [Var "y";
//                         Fn ("+",
//                          [Fn ("0", []);
//                           Fn ("*", [Var "y"; Fn ("-1", [])])])])]);
//                     Fn ("*",
//                      [Var "x";
//                       Fn ("+",
//                        [Fn ("0", []); Fn ("*", [Var "z"; Fn ("4", [])])])])])])]);
//               Fn ("0", [])])))))));
//    |]
//
//// complex.p071
//[<TestCase(@"exists z. x * z^87 + y * z^44 + 1 = 0", 0)>]
//
//// complex.p072
//[<TestCase(@"forall u. exists v. x * (u + v^2)^2 + y * (u + v^2) + z = 0", 1)>]
//
//let ``examples 7`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_7.[idx]
//
//
//(* ------------------------------------------------------------------------- *)
//(* Actually prove simple equivalences.                                       *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_8 : formula<fol>[] = [|
//    formula<fol>.True;
//    formula<fol>.True;
//    |]
//
//// complex.p073
//[<TestCase(@"forall x y. (exists z. x * z^87 + y * z^44 + 1 = 0)
//                  <=> ~(x = 0) \/ ~(y = 0)", 0)>]
//
//// complex.p074
//[<TestCase(@"forall x y z. (forall u. exists v.
//                         x * (u + v^2)^2 + y * (u + v^2) + z = 0)
//                    <=> ~(x = 0) \/ ~(y = 0) \/ z = 0", 1)>]
//
//let ``examples 8`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_8.[idx]
//
//(* ------------------------------------------------------------------------- *)
//(* Invertibility of 2x2 matrix in terms of nonzero determinant.              *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_9 : formula<fol>[] = [|
//    // CPU time (user): 0.004
//    And
//     (Or
//       (And
//         (Not
//           (Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                Fn ("0", [])]))),
//         Or
//          (And
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("+",
//                    [Fn ("0", []);
//                     Fn ("*",
//                      [Var "b";
//                       Fn ("+",
//                        [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])])])]);
//                   Fn ("*",
//                    [Var "a";
//                     Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
//                 Fn ("0", [])])),
//            Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
//                Fn ("0", [])]))),
//          Not
//           (Atom
//             (R ("=",
//               [Fn ("+",
//                 [Fn ("+",
//                   [Fn ("0", []);
//                    Fn ("*",
//                     [Var "b";
//                      Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])])])]);
//                  Fn ("*",
//                   [Var "a";
//                    Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
//                Fn ("0", [])]))))),
//       Or
//        (And
//          (Atom
//            (R ("=",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//               Fn ("0", [])])),
//          And
//           (Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
//                Fn ("0", [])])),
//           And
//            (Not
//              (Atom
//                (R ("=",
//                  [Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                   Fn ("0", [])]))),
//            Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                Fn ("0", [])]))))),
//        And
//         (Atom
//           (R ("=",
//             [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//              Fn ("0", [])])),
//         And
//          (Not
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
//                 Fn ("0", [])]))),
//          Not
//           (Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//                Fn ("0", [])]))))))),
//     Or
//      (And
//        (Not
//          (Atom
//            (R ("=",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
//               Fn ("0", [])]))),
//        Or
//         (And
//           (Atom
//             (R ("=",
//               [Fn ("+",
//                 [Fn ("+",
//                   [Fn ("0", []);
//                    Fn ("*",
//                     [Var "b";
//                      Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
//                  Fn ("*",
//                   [Var "a";
//                    Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])])])]);
//                Fn ("0", [])])),
//           Atom
//            (R ("=",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//               Fn ("0", [])]))),
//         Not
//          (Atom
//            (R ("=",
//              [Fn ("+",
//                [Fn ("+",
//                  [Fn ("0", []);
//                   Fn ("*",
//                    [Var "b";
//                     Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "c"; Fn ("-1", [])])])])]);
//                 Fn ("*",
//                  [Var "a";
//                   Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])])])]);
//               Fn ("0", [])]))))),
//      Or
//       (And
//         (Atom
//           (R ("=",
//             [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//              Fn ("0", [])])),
//         And
//          (Atom
//            (R ("=",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
//               Fn ("0", [])])),
//          And
//           (Not
//             (Atom
//               (R ("=",
//                 [Fn ("+",
//                   [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//                  Fn ("0", [])]))),
//           Atom
//            (R ("=",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "a"; Fn ("1", [])])]);
//               Fn ("0", [])]))))),
//       And
//        (Atom
//          (R ("=",
//            [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("1", [])])]);
//             Fn ("0", [])])),
//        And
//         (Not
//           (Atom
//             (R ("=",
//               [Fn ("+", [Fn ("0", []); Fn ("*", [Var "b"; Fn ("1", [])])]);
//                Fn ("0", [])]))),
//         Not
//          (Atom
//            (R ("=",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "c"; Fn ("1", [])])]);
//               Fn ("0", [])]))))))));
//    // CPU time (user): 0.060004
//    formula<fol>.True;
//    |]
//
//// complex.p075
//[<TestCase(@"exists w x y z. (a * w + b * y = 1) /\
//                      (a * x + b * z = 0) /\
//                      (c * w + d * y = 0) /\
//                      (c * x + d * z = 1)", 0)>]
//
//// complex.p076
//[<TestCase(@"forall a b c d.
//        (exists w x y z. (a * w + b * y = 1) /\
//                         (a * x + b * z = 0) /\
//                         (c * w + d * y = 0) /\
//                         (c * x + d * z = 1))
//        <=> ~(a * d = b * c)", 1)>]
//
//let ``examples 9`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_9.[idx]
//
//(* ------------------------------------------------------------------------- *)
//(* Inspired by Cardano's formula for a cubic. Not all complex cbrts work.    *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_10 : formula<fol>[] = [|
//    formula<fol>.False;
//    formula<fol>.True;
//    |]
//
//// complex.p077
//[<TestCase(@"forall m n x u t cu ct.
//   t - u = n /\ 27 * t * u = m^3 /\
//   ct^3 = t /\ cu^3 = u /\
//   x = ct - cu
//   ==> x^3 + m * x = n", 0)>]
//
//// complex.p078
//[<TestCase(@"forall m n x u t.
//   t - u = n /\ 27 * t * u = m^3
//   ==> exists ct cu. ct^3 = t /\ cu^3 = u /\
//                     (x = ct - cu ==> x^3 + m * x = n)", 1)>]
//
//[<Category("LongRunning")>]
//let ``examples 10`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_10.[idx]
//
//(* ------------------------------------------------------------------------- *)
//(* SOS in rational functions for Motzkin polynomial (dehomogenized).         *)
//(* Of course these are just trivial normalization, nothing deep.             *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_11 : formula<fol>[] = [|
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    formula<fol>.True;
//    |]
//
//// complex.p079
//[<TestCase(@"forall x y z.
//    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//     x^2 * y^2 * (x^2 + y^2 + 1) * (x^2 + y^2 - 2)^2 + (x^2 - y^2)^2", 0)>]
//
//// complex.p080
//[<TestCase(@"forall x y z.
//    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//    x^2 * y^2 * x^2  * (x^2 + y^2 - 2)^2 +
//    x^2 * y^2 * y^2 * (x^2 + y^2 - 2)^2 +
//    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
//    (x^2 - y^2)^2", 1)>]
//
//// complex.p081
//[<TestCase(@"forall x y z.
//    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//    x^4 * y^2 * (x^2 + y^2 - 2)^2 +
//    x^2 * y^4 * (x^2 + y^2 - 2)^2 +
//    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
//    (x^2 - y^2)^2", 2)>]
//
//// complex.p082
//[<TestCase(@"forall x y z.
//    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
//    (x^2 * y * (x^2 + y^2 - 2))^2 +
//    (x * y^2 * (x^2 + y^2 - 2))^2 +
//    (x * y * (x^2 + y^2 - 2))^2 +
//    (x^2 - y^2)^2", 3)>]
//
//let ``examples 11`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_11.[idx]
//
//(* ------------------------------------------------------------------------- *)
//(* A cute bilinear identity -- see ch14 of Rajwade's "Squares" for more.     *)
//(* ------------------------------------------------------------------------- *)
//
//// complex.p083
//[<Test>]
//let ``examples 12``() =
//    @"(x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_6^2 + x_7^2 + x_8^2 + x_9^2) *
//    (y_1^2 + y_2^2 + y_3^2 + y_4^2 + y_5^2 + y_6^2 + y_7^2 + y_8^2 +
//    y_9^2 + y_10^2 + y_11^2 + y_12^2 + y_13^2 + y_14^2 + y_15^2 + y_16^2) -
//    ((0 + x_1 * y_1 + x_2 * y_2 + x_3 * y_3 + x_4 * y_4 + x_5 * y_5 + x_6 * y_6 + x_7 * y_7 + x_8 * y_8 + x_9 * y_9)^2 +
//    (0 - x_2 * y_1 + x_1 * y_2 + x_4 * y_3 - x_3 * y_4 + x_6 * y_5 - x_5 * y_6 - x_8 * y_7 + x_7 * y_8 + x_9 * y_10)^2 +
//    (0 - x_3 * y_1 - x_4 * y_2 + x_1 * y_3 + x_2 * y_4 + x_7 * y_5 + x_8 * y_6 - x_5 * y_7 - x_6 * y_8 + x_9 * y_11)^2 +
//    (0 - x_4 * y_1 + x_3 * y_2 - x_2 * y_3 + x_1 * y_4 + x_8 * y_5 - x_7 * y_6 + x_6 * y_7 - x_5 * y_8 + x_9 * y_12)^2 +
//    (0 - x_5 * y_1 - x_6 * y_2 - x_7 * y_3 - x_8 * y_4 + x_1 * y_5 + x_2 * y_6 + x_3 * y_7 + x_4 * y_8 + x_9 * y_13)^2 +
//    (0 - x_6 * y_1 + x_5 * y_2 - x_8 * y_3 + x_7 * y_4 - x_2 * y_5 + x_1 * y_6 - x_4 * y_7 + x_3 * y_8 + x_9 * y_14)^2 +
//    (0 - x_7 * y_1 + x_8 * y_2 + x_5 * y_3 - x_6 * y_4 - x_3 * y_5 + x_4 * y_6 + x_1 * y_7 - x_2 * y_8 + x_9 * y_15)^2 +
//    (0 - x_8 * y_1 - x_7 * y_2 + x_6 * y_3 + x_5 * y_4 - x_4 * y_5 - x_3 * y_6 + x_2 * y_7 + x_1 * y_8 + x_9 * y_16)^2 +
//    (0 - x_9 * y_1 + x_1 * y_9 - x_2 * y_10 - x_3 * y_11 - x_4 * y_12 - x_5 * y_13 - x_6 * y_14 - x_7 * y_15 - x_8 * y_16)^2 +
//    (0 - x_9 * y_2 + x_2 * y_9 + x_1 * y_10 - x_4 * y_11 + x_3 * y_12 - x_6 * y_13 + x_5 * y_14 + x_8 * y_15 - x_7 * y_16)^2 +
//    (0 - x_9 * y_3 + x_3 * y_9 + x_4 * y_10 + x_1 * y_11 - x_2 * y_12 - x_7 * y_13 - x_8 * y_14 + x_5 * y_15 + x_6 * y_16)^2 +
//    (0 - x_9 * y_4 + x_4 * y_9 - x_3 * y_10 + x_2 * y_11 + x_1 * y_12 - x_8 * y_13 + x_7 * y_14 - x_6 * y_15 + x_5 * y_16)^2 +
//    (0 - x_9 * y_5 + x_5 * y_9 + x_6 * y_10 + x_7 * y_11 + x_8 * y_12 + x_1 * y_13 - x_2 * y_14 - x_3 * y_15 - x_4 * y_16)^2 +
//    (0 - x_9 * y_6 + x_6 * y_9 - x_5 * y_10 + x_8 * y_11 - x_7 * y_12 + x_2 * y_13 + x_1 * y_14 + x_4 * y_15 - x_3 * y_16)^2 +
//    (0 - x_9 * y_7 + x_7 * y_9 - x_8 * y_10 - x_5 * y_11 + x_6 * y_12 + x_3 * y_13 - x_4 * y_14 + x_1 * y_15 + x_2 * y_16)^2 +
//    (0 - x_9 * y_8 + x_8 * y_9 + x_7 * y_10 - x_6 * y_11 - x_5 * y_12 + x_4 * y_13 + x_3 * y_14 - x_2 * y_15 + x_1 * y_16)^2)"
//    |> parset
//    |> polytest
//    |> should equal
//    <| Fn ("0", [])
//
//(* ------------------------------------------------------------------------- *)
//(* This is essentially the Cauchy-Riemann conditions for a differential.     *)
//(* ------------------------------------------------------------------------- *)
//
//let private example_results_13 : formula<fol>[] = [|
//    // CPU time (user): 0.004
//    Not
//     (And
//       (Or
//         (And
//           (Atom
//             (R ("=",
//               [Fn ("+",
//                 [Fn ("+",
//                   [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
//                  Fn ("*", [Var "d"; Fn ("1", [])])]);
//                Fn ("0", [])])),
//           And
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])]);
//                   Fn ("*", [Var "b"; Fn ("1", [])])]);
//                 Fn ("0", [])])),
//            Or
//             (And
//               (Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
//                      Fn ("*", [Var "a"; Fn ("1", [])])]);
//                    Fn ("0", [])])),
//               Or
//                (Atom
//                  (R ("=",
//                    [Fn ("+",
//                      [Fn ("+",
//                        [Fn ("0", []); Fn ("*", [Var "v"; Fn ("-1", [])])]);
//                       Fn ("*", [Var "c"; Fn ("1", [])])]);
//                     Fn ("0", [])])),
//                Not
//                 (Atom
//                   (R ("=",
//                     [Fn ("+",
//                       [Fn ("+",
//                         [Fn ("0", []); Fn ("*", [Var "v"; Fn ("-1", [])])]);
//                        Fn ("*", [Var "c"; Fn ("1", [])])]);
//                      Fn ("0", [])]))))),
//             Not
//              (Atom
//                (R ("=",
//                  [Fn ("+",
//                    [Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
//                     Fn ("*", [Var "a"; Fn ("1", [])])]);
//                   Fn ("0", [])])))))),
//         Or
//          (And
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("+",
//                    [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])]);
//                   Fn ("*", [Var "b"; Fn ("1", [])])]);
//                 Fn ("0", [])])),
//            And
//             (Not
//               (Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
//                      Fn ("*", [Var "d"; Fn ("1", [])])]);
//                    Fn ("0", [])]))),
//             Or
//              (Atom
//                (R ("=",
//                  [Fn ("+",
//                    [Fn ("+",
//                      [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
//                     Fn ("*", [Var "a"; Fn ("1", [])])]);
//                   Fn ("0", [])])),
//              Not
//               (Atom
//                 (R ("=",
//                   [Fn ("+",
//                     [Fn ("+",
//                       [Fn ("0", []); Fn ("*", [Var "u"; Fn ("-1", [])])]);
//                      Fn ("*", [Var "a"; Fn ("1", [])])]);
//                    Fn ("0", [])])))))),
//          And
//           (Not
//             (Atom
//               (R ("=",
//                 [Fn ("+",
//                   [Fn ("+",
//                     [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])]);
//                    Fn ("*", [Var "b"; Fn ("1", [])])]);
//                  Fn ("0", [])]))),
//           Or
//            (Atom
//              (R ("=",
//                [Fn ("+",
//                  [Fn ("+",
//                    [Fn ("+",
//                      [Fn ("+",
//                        [Fn ("+",
//                          [Fn ("+",
//                            [Fn ("0", []);
//                             Fn ("*",
//                              [Var "v";
//                               Fn ("+",
//                                [Fn ("0", []);
//                                 Fn ("*", [Var "v"; Fn ("-1", [])])])])]);
//                           Fn ("*",
//                            [Var "u";
//                             Fn ("+",
//                              [Fn ("0", []);
//                               Fn ("*", [Var "u"; Fn ("-1", [])])])])]);
//                         Fn ("*",
//                          [Var "d";
//                           Fn ("+",
//                            [Fn ("0", []);
//                             Fn ("*", [Var "u"; Fn ("1", [])])])])]);
//                       Fn ("*",
//                        [Var "c";
//                         Fn ("+",
//                          [Fn ("0", []); Fn ("*", [Var "v"; Fn ("1", [])])])])]);
//                     Fn ("*",
//                      [Var "b";
//                       Fn ("+",
//                        [Fn ("+",
//                          [Fn ("0", []);
//                           Fn ("*", [Var "v"; Fn ("-1", [])])]);
//                         Fn ("*", [Var "c"; Fn ("1", [])])])])]);
//                   Fn ("*",
//                    [Var "a";
//                     Fn ("+",
//                      [Fn ("+",
//                        [Fn ("0", []); Fn ("*", [Var "u"; Fn ("1", [])])]);
//                       Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
//                 Fn ("0", [])])),
//            Not
//             (Atom
//               (R ("=",
//                 [Fn ("+",
//                   [Fn ("+",
//                     [Fn ("+",
//                       [Fn ("+",
//                         [Fn ("+",
//                           [Fn ("+",
//                             [Fn ("0", []);
//                              Fn ("*",
//                               [Var "v";
//                                Fn ("+",
//                                 [Fn ("0", []);
//                                  Fn ("*", [Var "v"; Fn ("-1", [])])])])]);
//                            Fn ("*",
//                             [Var "u";
//                              Fn ("+",
//                               [Fn ("0", []);
//                                Fn ("*", [Var "u"; Fn ("-1", [])])])])]);
//                          Fn ("*",
//                           [Var "d";
//                            Fn ("+",
//                             [Fn ("0", []);
//                              Fn ("*", [Var "u"; Fn ("1", [])])])])]);
//                        Fn ("*",
//                         [Var "c";
//                          Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*", [Var "v"; Fn ("1", [])])])])]);
//                      Fn ("*",
//                       [Var "b";
//                        Fn ("+",
//                         [Fn ("+",
//                           [Fn ("0", []);
//                            Fn ("*", [Var "v"; Fn ("-1", [])])]);
//                          Fn ("*", [Var "c"; Fn ("1", [])])])])]);
//                    Fn ("*",
//                     [Var "a";
//                      Fn ("+",
//                       [Fn ("+",
//                         [Fn ("0", []); Fn ("*", [Var "u"; Fn ("1", [])])]);
//                        Fn ("*", [Var "d"; Fn ("-1", [])])])])]);
//                  Fn ("0", [])]))))))),
//       Not
//        (Atom
//          (R ("=",
//            [Fn ("+",
//              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "d"; Fn ("-1", [])])]);
//               Fn ("*", [Var "a"; Fn ("1", [])])]);
//             Fn ("0", [])])))));
//    // CPU time (user): 0.004
//    formula<fol>.True;
//    // CPU time (user): 0.008001
//    formula<fol>.True;
//    |]
//
//// complex.p084
//[<TestCase(@"forall x y. (a * x + b * y = u * x - v * y) /\
//                (c * x + d * y = u * y + v * x)
//                ==> (a = d)", 0)>]
//
//// complex.p085
//[<TestCase(@"forall a b c d.
//      (forall x y. (a * x + b * y = u * x - v * y) /\
//                   (c * x + d * y = u * y + v * x))
//                   ==> (a = d) /\ (b = -(c))", 1)>]
//
//// complex.p086
//[<TestCase(@"forall a b c d.
//        (exists u v. forall x y. (a * x + b * y = u * x - v * y) /\
//                                 (c * x + d * y = u * y + v * x))
//        <=> (a = d) /\ (b = -(c))", 2)>]
//
//let ``examples 13`` (f, idx) =
//    parse f
//    |> complex_qelim
//    |> should equal example_results_13.[idx]
//
//(* ------------------------------------------------------------------------- *)
//(* Finding non-trivial perpendiculars to lines.                              *)
//(* ------------------------------------------------------------------------- *)
//
//// complex.p087
//let ``examples 14``() =
//    @"forall x1 y1 x2 y2. exists a b.
//      ~(a = 0 /\ b = 0) /\ a * x1 + b * y1 = 0 /\ a * x2 + b * y2 = 0"
//    |> parse
//    |> complex_qelim
//    |> should equal formula<fol>.False
