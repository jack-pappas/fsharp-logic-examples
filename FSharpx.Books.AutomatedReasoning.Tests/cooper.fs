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

let private integer_qelimValues1 : (string * formula<fol>)[] = [|
    (
        // idx 0
        // cooper.p001
        // cooper.p016
        @"forall x y. ~(2 * x + 1 = 2 * y)",
        formula<fol>.True
    );
    (
        // idx 1
        // cooper.p002
        @"forall x. exists y. 2 * y <= x /\ x < 2 * (y + 1)",
        formula<fol>.True
    );
    (
        // idx 2
        // cooper.p003
        @"exists x y. 4 * x - 6 * y = 1",
        formula<fol>.False
    );
    (
        // idx 3
        // cooper.p004
        // cooper.p042
        @"forall x. ~divides(2,x) /\ divides(3,x-1) <=> divides(12,x-1) \/ divides(12,x-7)",
        formula<fol>.True
    );
    (
        // idx 4
        // cooper.p005
        @"forall x. b < x ==> a <= x",
        Not
         (Atom
           (R ("<",
             [Fn ("0", []);
              Fn ("+",
               [Fn ("*", [Fn ("1", []); Var "a"]);
                Fn ("+", [Fn ("*", [Fn ("-1", []); Var "b"]); Fn ("-1", [])])])])))
    );
    (
        // idx 5
        // cooper.p007
        @"forall d. exists x y. 3 * x + 5 * y = d",
        formula<fol>.True
    );
    (
        // idx 6
        // cooper.p010
        @"exists x y. x > 0 /\ y >= 0 /\ 3 * x - 5 * y = 1",
        formula<fol>.True
    );
    (
        // idx 7
        // cooper.p011
        @"exists x y z. 4 * x - 6 * y = 1",
        formula<fol>.False
    );
    (
        // idx 8
        // cooper.p012
        @"forall x. a < 3 * x ==> b < 3 * x",
        Not
          (Or
             (And
                (Atom
                   (R ("divides",
                       [Fn ("3",[]);
                        Fn
                          ("+",[Fn ("*",[Fn ("1",[]); Var "a"]); Fn ("1",[])])])),
                 Atom
                   (R ("<",
                       [Fn ("0",[]);
                        Fn
                          ("+",
                           [Fn ("*",[Fn ("-1",[]); Var "a"]);
                            Fn
                              ("+",
                               [Fn ("*",[Fn ("1",[]); Var "b"]); Fn ("0",[])])])]))),
              Or
                (And
                   (Atom
                      (R ("divides",
                          [Fn ("3",[]);
                           Fn
                             ("+",
                              [Fn ("*",[Fn ("1",[]); Var "a"]); Fn ("2",[])])])),
                    Atom
                      (R ("<",
                          [Fn ("0",[]);
                           Fn
                             ("+",
                              [Fn ("*",[Fn ("-1",[]); Var "a"]);
                               Fn
                                 ("+",
                                  [Fn ("*",[Fn ("1",[]); Var "b"]);
                                   Fn ("-1",[])])])]))),
                 And
                   (Atom
                      (R ("divides",
                          [Fn ("3",[]);
                           Fn
                             ("+",
                              [Fn ("*",[Fn ("1",[]); Var "a"]); Fn ("3",[])])])),
                    Atom
                      (R ("<",
                          [Fn ("0",[]);
                           Fn
                             ("+",
                              [Fn ("*",[Fn ("-1",[]); Var "a"]);
                               Fn
                                 ("+",
                                  [Fn ("*",[Fn ("1",[]); Var "b"]);
                                   Fn ("-2",[])])])]))))))

    );
    (
        // idx 9
        // cooper.p013
        @"forall x y. x <= y ==> 2 * x + 1 < 2 * y",
        formula<fol>.False
    );
    (
        // idx 10
        // cooper.p014
        @"(exists d. y = 65 * d) ==> (exists d. y = 5 * d)",
        Imp
          (Atom
             (R ("divides",
                 [Fn ("65",[]);
                  Fn ("+",[Fn ("*",[Fn ("1",[]); Var "y"]); Fn ("0",[])])])),
           Atom
             (R ("divides",
                 [Fn ("5",[]);
                  Fn ("+",[Fn ("*",[Fn ("1",[]); Var "y"]); Fn ("0",[])])])))
    );
    (
        // idx 11
        // cooper.p015
        @"forall y. (exists d. y = 65 * d) ==> (exists d. y = 5 * d)",
        formula<fol>.True
    );
    (
        // idx 12
        // cooper.p016
        @"forall x y. ~(2 * x + 1 = 2 * y)",
        formula<fol>.True
    );
    (
        // idx 13
        // cooper.p017
        @"forall x y z. (2 * x + 1 = 2 * y) ==> x + y + z > 129",
        formula<fol>.True
    );
    (
        // idx 14
        // cooper.p018
        @"forall x. a < x ==> b < x",
        Not
          (Atom
             (R ("<",
                 [Fn ("0",[]);
                  Fn
                    ("+",
                     [Fn ("*",[Fn ("-1",[]); Var "a"]);
                      Fn ("+",[Fn ("*",[Fn ("1",[]); Var "b"]); Fn ("0",[])])])])))
    );
    (
        // idx 15
        // cooper.p019
        @"forall x. a <= x ==> b < x",
        Not
          (Atom
             (R ("<",
                 [Fn ("0",[]);
                  Fn
                    ("+",
                     [Fn ("*",[Fn ("-1",[]); Var "a"]);
                      Fn ("+",[Fn ("*",[Fn ("1",[]); Var "b"]); Fn ("1",[])])])])))
    );
    (
        // idx 16
        // cooper.p020
        @"forall a b. exists x. a < 20 * x /\ 20 * x < b",
        formula<fol>.False
    );
    (
        // idx 17
        // cooper.p021
        @"exists x. a < 20 * x /\ 20 * x < b",
        Or
          (And
             (Atom
                (R ("divides",
                    [Fn ("20",[]);
                     Fn ("+",[Fn ("*",[Fn ("1",[]); Var "a"]); Fn ("1",[])])])),
              Atom
                (R ("<",
                    [Fn ("0",[]);
                     Fn
                       ("+",
                        [Fn ("*",[Fn ("-1",[]); Var "a"]);
                         Fn
                           ("+",
                            [Fn ("*",[Fn ("1",[]); Var "b"]); Fn ("-1",[])])])]))),
           Or
             (And
                (Atom
                   (R ("divides",
                       [Fn ("20",[]);
                        Fn
                          ("+",[Fn ("*",[Fn ("1",[]); Var "a"]); Fn ("2",[])])])),
                 Atom
                   (R ("<",
                       [Fn ("0",[]);
                        Fn
                          ("+",
                           [Fn ("*",[Fn ("-1",[]); Var "a"]);
                            Fn
                              ("+",
                               [Fn ("*",[Fn ("1",[]); Var "b"]); Fn ("-2",[])])])]))),
              Or
                (And
                   (Atom
                      (R ("divides",
                          [Fn ("20",[]);
                           Fn
                             ("+",
                              [Fn ("*",[Fn ("1",[]); Var "a"]); Fn ("3",[])])])),
                    Atom
                      (R ("<",
                          [Fn ("0",[]);
                           Fn
                             ("+",
                              [Fn ("*",[Fn ("-1",[]); Var "a"]);
                               Fn
                                 ("+",
                                  [Fn ("*",[Fn ("1",[]); Var "b"]);
                                   Fn ("-3",[])])])]))),
                 Or
                   (And
                      (Atom
                         (R ("divides",
                             [Fn ("20",[]);
                              Fn
                                ("+",
                                 [Fn ("*",[Fn ("1",[]); Var "a"]); Fn ("4",[])])])),
                       Atom
                         (R ("<",
                             [Fn ("0",[]);
                              Fn
                                ("+",
                                 [Fn ("*",[Fn ("-1",[]); Var "a"]);
                                  Fn
                                    ("+",
                                     [Fn ("*",[Fn ("1",[]); Var "b"]);
                                      Fn ("-4",[])])])]))),
                    Or
                      (And
                         (Atom
                            (R ("divides",
                                [Fn ("20",[]);
                                 Fn
                                   ("+",
                                    [Fn ("*",[Fn ("1",[]); Var "a"]);
                                     Fn ("5",[])])])),
                          Atom
                            (R ("<",
                                [Fn ("0",[]);
                                 Fn
                                   ("+",
                                    [Fn ("*",[Fn ("-1",[]); Var "a"]);
                                     Fn
                                       ("+",
                                        [Fn ("*",[Fn ("1",[]); Var "b"]);
                                         Fn ("-5",[])])])]))),
                       Or
                         (And
                            (Atom
                               (R ("divides",
                                   [Fn ("20",[]);
                                    Fn
                                      ("+",
                                       [Fn ("*",[Fn ("1",[]); Var "a"]);
                                        Fn ("6",[])])])),
                             Atom
                               (R ("<",
                                   [Fn ("0",[]);
                                    Fn
                                      ("+",
                                       [Fn ("*",[Fn ("-1",[]); Var "a"]);
                                        Fn
                                          ("+",
                                           [Fn ("*",[Fn ("1",[]); Var "b"]);
                                            Fn ("-6",[])])])]))),
                          Or
                            (And
                               (Atom
                                  (R ("divides",
                                      [Fn ("20",[]);
                                       Fn
                                         ("+",
                                          [Fn ("*",[Fn ("1",[]); Var "a"]);
                                           Fn ("7",[])])])),
                                Atom
                                  (R ("<",
                                      [Fn ("0",[]);
                                       Fn
                                         ("+",
                                          [Fn ("*",[Fn ("-1",[]); Var "a"]);
                                           Fn
                                             ("+",
                                              [Fn ("*",[Fn ("1",[]); Var "b"]);
                                               Fn ("-7",[])])])]))),
                             Or
                               (And
                                  (Atom
                                     (R ("divides",
                                         [Fn ("20",[]);
                                          Fn
                                            ("+",
                                             [Fn ("*",[Fn ("1",[]); Var "a"]);
                                              Fn ("8",[])])])),
                                   Atom
                                     (R ("<",
                                         [Fn ("0",[]);
                                          Fn
                                            ("+",
                                             [Fn ("*",[Fn ("-1",[]); Var "a"]);
                                              Fn
                                                ("+",
                                                 [Fn
                                                    ("*",
                                                     [Fn ("1",[]); Var "b"]);
                                                  Fn ("-8",[])])])]))),
                                Or
                                  (And
                                     (Atom
                                        (R ("divides",
                                            [Fn ("20",[]);
                                             Fn
                                               ("+",
                                                [Fn
                                                   ("*",[Fn ("1",[]); Var "a"]);
                                                 Fn ("9",[])])])),
                                      Atom
                                        (R ("<",
                                            [Fn ("0",[]);
                                             Fn
                                               ("+",
                                                [Fn
                                                   ("*",
                                                    [Fn ("-1",[]); Var "a"]);
                                                 Fn
                                                   ("+",
                                                    [Fn
                                                       ("*",
                                                        [Fn ("1",[]); Var "b"]);
                                                     Fn ("-9",[])])])]))),
                                   Or
                                     (And
                                        (Atom
                                           (R ("divides",
                                               [Fn ("20",[]);
                                                Fn
                                                  ("+",
                                                   [Fn
                                                      ("*",
                                                       [Fn ("1",[]); Var "a"]);
                                                    Fn ("10",[])])])),
                                         Atom
                                           (R ("<",
                                               [Fn ("0",[]);
                                                Fn
                                                  ("+",
                                                   [Fn
                                                      ("*",
                                                       [Fn ("-1",[]); Var "a"]);
                                                    Fn
                                                      ("+",
                                                       [Fn
                                                          ("*",
                                                           [Fn ("1",[]);
                                                            Var "b"]);
                                                        Fn ("-10",[])])])]))),
                                      Or
                                        (And
                                           (Atom
                                              (R ("divides",
                                                  [Fn ("20",[]);
                                                   Fn
                                                     ("+",
                                                      [Fn
                                                         ("*",
                                                          [Fn ("1",[]);
                                                           Var "a"]);
                                                       Fn ("11",[])])])),
                                            Atom
                                              (R ("<",
                                                  [Fn ("0",[]);
                                                   Fn
                                                     ("+",
                                                      [Fn
                                                         ("*",
                                                          [Fn ("-1",[]);
                                                           Var "a"]);
                                                       Fn
                                                         ("+",
                                                          [Fn
                                                             ("*",
                                                              [Fn ("1",[]);
                                                               Var "b"]);
                                                           Fn ("-11",[])])])]))),
                                         Or
                                           (And
                                              (Atom
                                                 (R ("divides",
                                                     [Fn ("20",[]);
                                                      Fn
                                                        ("+",
                                                         [Fn
                                                            ("*",
                                                             [Fn ("1",[]);
                                                              Var "a"]);
                                                          Fn ("12",[])])])),
                                               Atom
                                                 (R ("<",
                                                     [Fn ("0",[]);
                                                      Fn
                                                        ("+",
                                                         [Fn
                                                            ("*",
                                                             [Fn ("-1",[]);
                                                              Var "a"]);
                                                          Fn
                                                            ("+",
                                                             [Fn
                                                                ("*",
                                                                 [Fn ("1",[]);
                                                                  Var "b"]);
                                                              Fn ("-12",[])])])]))),
                                            Or
                                              (And
                                                 (Atom
                                                    (R ("divides",
                                                        [Fn ("20",[]);
                                                         Fn
                                                           ("+",
                                                            [Fn
                                                               ("*",
                                                                [Fn ("1",[]);
                                                                 Var "a"]);
                                                             Fn ("13",[])])])),
                                                  Atom
                                                    (R ("<",
                                                        [Fn ("0",[]);
                                                         Fn
                                                           ("+",
                                                            [Fn
                                                               ("*",
                                                                [Fn ("-1",[]);
                                                                 Var "a"]);
                                                             Fn
                                                               ("+",
                                                                [Fn
                                                                   ("*",
                                                                    [Fn
                                                                       ("1",[]);
                                                                     Var "b"]);
                                                                 Fn ("-13",[])])])]))),
                                               Or
                                                 (And
                                                    (Atom
                                                       (R ("divides",
                                                           [Fn ("20",[]);
                                                            Fn
                                                              ("+",
                                                               [Fn
                                                                  ("*",
                                                                   [Fn
                                                                      ("1",[]);
                                                                    Var "a"]);
                                                                Fn ("14",[])])])),
                                                     Atom
                                                       (R ("<",
                                                           [Fn ("0",[]);
                                                            Fn
                                                              ("+",
                                                               [Fn
                                                                  ("*",
                                                                   [Fn
                                                                      ("-1",[]);
                                                                    Var "a"]);
                                                                Fn
                                                                  ("+",
                                                                   [Fn
                                                                      ("*",
                                                                       [Fn
                                                                          ("1",
                                                                           []);
                                                                        Var
                                                                          "b"]);
                                                                    Fn
                                                                      ("-14",
                                                                       [])])])]))),
                                                  Or
                                                    (And
                                                       (Atom
                                                          (R ("divides",
                                                              [Fn ("20",[]);
                                                               Fn
                                                                 ("+",
                                                                  [Fn
                                                                     ("*",
                                                                      [Fn
                                                                         ("1",
                                                                          []);
                                                                       Var "a"]);
                                                                   Fn
                                                                     ("15",[])])])),
                                                        Atom
                                                          (R ("<",
                                                              [Fn ("0",[]);
                                                               Fn
                                                                 ("+",
                                                                  [Fn
                                                                     ("*",
                                                                      [Fn
                                                                         ("-1",
                                                                          []);
                                                                       Var "a"]);
                                                                   Fn
                                                                     ("+",
                                                                      [Fn
                                                                         ("*",
                                                                          [Fn
                                                                             ("1",
                                                                              []);
                                                                           Var
                                                                             "b"]);
                                                                       Fn
                                                                         ("-15",
                                                                          [])])])]))),
                                                     Or
                                                       (And
                                                          (Atom
                                                             (R ("divides",
                                                                 [Fn ("20",[]);
                                                                  Fn
                                                                    ("+",
                                                                     [Fn
                                                                        ("*",
                                                                         [Fn
                                                                            ("1",
                                                                             []);
                                                                          Var
                                                                            "a"]);
                                                                      Fn
                                                                        ("16",
                                                                         [])])])),
                                                           Atom
                                                             (R ("<",
                                                                 [Fn ("0",[]);
                                                                  Fn
                                                                    ("+",
                                                                     [Fn
                                                                        ("*",
                                                                         [Fn
                                                                            ("-1",
                                                                             []);
                                                                          Var
                                                                            "a"]);
                                                                      Fn
                                                                        ("+",
                                                                         [Fn
                                                                            ("*",
                                                                             [Fn
                                                                                ("1",
                                                                                 []);
                                                                              Var
                                                                                "b"]);
                                                                          Fn
                                                                            ("-16",
                                                                             [])])])]))),
                                                        Or
                                                          (And
                                                             (Atom
                                                                (R ("divides",
                                                                    [Fn
                                                                       ("20",
                                                                        []);
                                                                     Fn
                                                                       ("+",
                                                                        [Fn
                                                                           ("*",
                                                                            [Fn
                                                                               ("1",
                                                                                []);
                                                                             Var
                                                                               "a"]);
                                                                         Fn
                                                                           ("17",
                                                                            [])])])),
                                                              Atom
                                                                (R ("<",
                                                                    [Fn
                                                                       ("0",[]);
                                                                     Fn
                                                                       ("+",
                                                                        [Fn
                                                                           ("*",
                                                                            [Fn
                                                                               ("-1",
                                                                                []);
                                                                             Var
                                                                               "a"]);
                                                                         Fn
                                                                           ("+",
                                                                            [Fn
                                                                               ("*",
                                                                                [Fn
                                                                                   ("1",
                                                                                    []);
                                                                                 Var
                                                                                   "b"]);
                                                                             Fn
                                                                               ("-17",
                                                                                [])])])]))),
                                                           Or
                                                             (And
                                                                (Atom
                                                                   (R ("divides",
                                                                       [Fn
                                                                          ("20",
                                                                           []);
                                                                        Fn
                                                                          ("+",
                                                                           [Fn
                                                                              ("*",
                                                                               [Fn
                                                                                  ("1",
                                                                                   []);
                                                                                Var
                                                                                  "a"]);
                                                                            Fn
                                                                              ("18",
                                                                               [])])])),
                                                                 Atom
                                                                   (R ("<",
                                                                       [Fn
                                                                          ("0",
                                                                           []);
                                                                        Fn
                                                                          ("+",
                                                                           [Fn
                                                                              ("*",
                                                                               [Fn
                                                                                  ("-1",
                                                                                   []);
                                                                                Var
                                                                                  "a"]);
                                                                            Fn
                                                                              ("+",
                                                                               [Fn
                                                                                  ("*",
                                                                                   [Fn
                                                                                      ("1",
                                                                                       []);
                                                                                    Var
                                                                                      "b"]);
                                                                                Fn
                                                                                  ("-18",
                                                                                   [])])])]))),
                                                              Or
                                                                (And
                                                                   (Atom
                                                                      (R ("divides",
                                                                          [Fn
                                                                             ("20",
                                                                              []);
                                                                           Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("*",
                                                                                  [Fn
                                                                                     ("1",
                                                                                      []);
                                                                                   Var
                                                                                     "a"]);
                                                                               Fn
                                                                                 ("19",
                                                                                  [])])])),
                                                                    Atom
                                                                      (R ("<",
                                                                          [Fn
                                                                             ("0",
                                                                              []);
                                                                           Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("*",
                                                                                  [Fn
                                                                                     ("-1",
                                                                                      []);
                                                                                   Var
                                                                                     "a"]);
                                                                               Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("*",
                                                                                      [Fn
                                                                                         ("1",
                                                                                          []);
                                                                                       Var
                                                                                         "b"]);
                                                                                   Fn
                                                                                     ("-19",
                                                                                      [])])])]))),
                                                                 And
                                                                   (Atom
                                                                      (R ("divides",
                                                                          [Fn
                                                                             ("20",
                                                                              []);
                                                                           Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("*",
                                                                                  [Fn
                                                                                     ("1",
                                                                                      []);
                                                                                   Var
                                                                                     "a"]);
                                                                               Fn
                                                                                 ("20",
                                                                                  [])])])),
                                                                    Atom
                                                                      (R ("<",
                                                                          [Fn
                                                                             ("0",
                                                                              []);
                                                                           Fn
                                                                             ("+",
                                                                              [Fn
                                                                                 ("*",
                                                                                  [Fn
                                                                                     ("-1",
                                                                                      []);
                                                                                   Var
                                                                                     "a"]);
                                                                               Fn
                                                                                 ("+",
                                                                                  [Fn
                                                                                     ("*",
                                                                                      [Fn
                                                                                         ("1",
                                                                                          []);
                                                                                       Var
                                                                                         "b"]);
                                                                                   Fn
                                                                                     ("-20",
                                                                                      [])])])]))))))))))))))))))))))

    );
    (
        // idx 18
        // cooper.p022
        @"forall b. exists x. a < 20 * x /\ 20 * x < b",
        formula<fol>.False
    );
    (
        // idx 19
        // cooper.p023
        @"forall a. exists b. a < 4 * b + 3 * a \/ (~(a < b) /\ a > b + 1)",
        formula<fol>.True
    );
    (
        // idx 20
        // cooper.p024
        @"exists y. forall x. x + 5 * y > 1 /\ 13 * x - y > 1 /\ x + 2 < 0",
        formula<fol>.False
    );
    (
        // idx 21
        // cooper.p025
        @"forall x y. x >= 0 /\ y >= 0 ==> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2",
        formula<fol>.False
    );
    (
        // idx 22
        // cooper.p026
        @"exists x y. 5 * x + 3 * y = 1",
        formula<fol>.True
    );
    (
        // idx 23
        // cooper.p027
        @"exists x y. 5 * x + 10 * y = 1",
        formula<fol>.False
    );
    (
        // idx 24
        // cooper.p028
        @"exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 6 * y = 1",
        formula<fol>.True
    );
    (
        // idx 25
        // cooper.p029
        @"exists w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1",
        formula<fol>.True
    );
    (
        // idx 26
        // cooper.p030
        @"exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 3 * y = 1",
        formula<fol>.True
    );
    (
        // idx 27
        // cooper.p031
        @"exists x y. x >= 0 /\ y >= 0 /\ 3 * x - 5 * y = 1",
        formula<fol>.True
    );
    (
        // idx 28
        // cooper.p032
        @"exists x y. x >= 0 /\ y >= 0 /\ 6 * x - 3 * y = 1",
        formula<fol>.False
    );
    (
        // idx 29
        // cooper.p033
        @"forall x y. ~(x = 0) ==> 5 * y < 6 * x \/ 5 * y > 6 * x",
        formula<fol>.False
    );
    (
        // idx 30
        // cooper.p034
       @"forall x y. ~divides(5,x) /\ ~divides(6,y) ==> ~(6 * x = 5 * y)",
        formula<fol>.True
    );
    (
        // idx 31
        // cooper.p035
        @"forall x y. ~divides(5,x) ==> ~(6 * x = 5 * y)",
        formula<fol>.True
    );
    (
        // idx 32
        // cooper.p036
        @"forall x y. ~(6 * x = 5 * y)",
        formula<fol>.False
    );
    (
        // idx 33
        // cooper.p037
        @"forall x y. 6 * x = 5 * y ==> exists d. y = 3 * d",
        formula<fol>.True
    );
    (
        // idx 34
        // cooper.p038
        @"6 * x = 5 * y ==> exists d. y = 3 * d",
        Imp
          (Atom
             (R ("=",
                 [Fn ("0",[]);
                  Fn
                    ("+",
                     [Fn ("*",[Fn ("-6",[]); Var "x"]);
                      Fn ("+",[Fn ("*",[Fn ("5",[]); Var "y"]); Fn ("0",[])])])])),
           Atom
             (R ("divides",
                 [Fn ("3",[]);
                  Fn ("+",[Fn ("*",[Fn ("1",[]); Var "y"]); Fn ("0",[])])])))
    );
    (
        // idx 35
        // cooper.p039
        @"forall z. z > 7 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z",
        formula<fol>.True
    );
    (
        // idx 36
        // cooper.p040
        @"forall z. z > 2 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z",
        formula<fol>.False
    );
    (
        // idx 37
        // cooper.p041
        @"forall z.
            z <= 7
            ==> ((exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z) <=>
                ~(exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = 7 - z))",
        formula<fol>.True
    );
    (
        // idx 38
        // cooper.p043
        @"forall x. ~(exists m. x = 2 * m) /\ (exists m. x = 3 * m + 1) <=>
            (exists m. x = 12 * m + 1) \/ (exists m. x = 12 * m + 7)",
        formula<fol>.True
    );
    (
        // idx 39
        // cooper.p044
        @"forall x.
            ~(divides(2,x))
            ==> divides(4,x-1) \/
                divides(8,x-1) \/
                divides(8,x-3) \/
                divides(6,x-1) \/
                divides(14,x-1) \/
                divides(14,x-9) \/
                divides(14,x-11) \/
                divides(24,x-5) \/
                divides(24,x-11)",
        formula<fol>.False
    );
    (
        // idx 40
        // cooper.p046
        @"exists a b. ~(a = 1) /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)",
        formula<fol>.True
    );
    (
        // idx 41
        // cooper.p047
        @"exists a b. a > 1 /\ b > 1 /\
            ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
            (a = b)",
        formula<fol>.False
    );
    (
        // idx 42
        // cooper.p048
        @"exists a b. a > 1 /\ b > 1 /\ 
            ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ 
                ((2 * a = b) \/ (2 * a = 3 * b + 1))",
        formula<fol>.False
    );
    (
        // idx 43
        // cooper.p050
        @"forall x. x >= 8 ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v",
        formula<fol>.True
    );
    (
        // idx 44
        // cooper.p051
        @"exists l.  forall x. x >= l
            ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v",
        formula<fol>.True
    );
    (
        // idx 45
        // cooper.p052
        @"exists l.
            forall x. x >= l
                ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 7 * v",
        formula<fol>.True
    );
    (
        // idx 46
        // cooper.p053
        @"exists l.
            forall x. x >= l
                ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 8 * v",
        formula<fol>.True
    );
    (
        // idx 47
        // cooper.p054
        @"exists l.
            forall x. x >= l
                ==> exists u v. u >= 0 /\ v >= 0 /\ x = 7 * u + 8 * v",
        formula<fol>.False
    );
    (
        // idx 48
        // cooper.p055
        @"forall x q1 q2 r1 r2.
            x < 4699 /\ 
            2622 * x = 65536 * q1 + r1 /\ 0 <= q1 /\ 0 <= r1 /\ r1 < 65536 /\ 
            x = 100 * q2 + r2 /\ 0 <= q2 /\ 0 <= r2 /\ r2 < 100
            ==> q1 = q2",
        formula<fol>.False
    );
    (
        // idx 49
        // cooper.p056
        @"forall x y.
            (exists d. x + y = 2 * d) <=>
            ((exists d. x = 2 * d) <=> (exists d. y = 2 * d))",
        formula<fol>.True
    );
    (
        // idx 50
        // cooper.p057
        @"forall n.
          0 < n /\ n < 2400
            ==> n <= 2 /\ 2 <= 2 * n \/
                n <= 3 /\ 3 <= 2 * n \/
                n <= 5 /\ 5 <= 2 * n \/
                n <= 7 /\ 7 <= 2 * n \/
                n <= 13 /\ 13 <= 2 * n \/
                n <= 23 /\ 23 <= 2 * n \/
                n <= 43 /\ 43 <= 2 * n \/
                n <= 83 /\ 83 <= 2 * n \/
                n <= 163 /\ 163 <= 2 * n \/
                n <= 317 /\ 317 <= 2 * n \/
                n <= 631 /\ 631 <= 2 * n \/
                n <= 1259 /\ 1259 <= 2 * n \/
                n <= 2503 /\ 2503 <= 2 * n",
        formula<fol>.False
    );
    |]

[<Test>]
[<TestCase(0, TestName = "cooper.p001")>]
[<TestCase(1, TestName = "cooper.p002")>]
[<TestCase(2, TestName = "cooper.p003")>]
[<TestCase(3, TestName = "cooper.p004")>]
[<TestCase(4, TestName = "cooper.p005")>]
[<TestCase(5, TestName = "cooper.p007")>]
[<TestCase(6, TestName = "cooper.p010")>]
[<TestCase(7, TestName = "cooper.p011")>]
[<TestCase(8, TestName = "cooper.p012")>]
[<TestCase(9, TestName = "cooper.p013")>]
[<TestCase(10, TestName = "cooper.p014")>]
[<TestCase(11, TestName = "cooper.p015")>]
[<TestCase(12, TestName = "cooper.p016")>]
[<TestCase(13, TestName = "cooper.p017")>]
[<TestCase(14, TestName = "cooper.p018")>]
[<TestCase(15, TestName = "cooper.p019")>]
[<TestCase(16, TestName = "cooper.p020")>]
[<TestCase(17, TestName = "cooper.p021")>]
[<TestCase(18, TestName = "cooper.p022")>]
[<TestCase(19, TestName = "cooper.p023")>]
[<TestCase(20, TestName = "cooper.p024")>]
[<TestCase(21, TestName = "cooper.p025")>]
[<TestCase(22, TestName = "cooper.p026")>]
[<TestCase(23, TestName = "cooper.p027")>]
[<TestCase(24, TestName = "cooper.p028")>]
[<TestCase(25, TestName = "cooper.p029")>]
[<TestCase(26, TestName = "cooper.p030")>]
[<TestCase(27, TestName = "cooper.p031")>]
[<TestCase(28, TestName = "cooper.p032")>]
[<TestCase(29, TestName = "cooper.p033")>]
[<TestCase(30, TestName = "cooper.p034")>]
[<TestCase(31, TestName = "cooper.p035")>]
[<TestCase(32, TestName = "cooper.p036")>]
[<TestCase(33, TestName = "cooper.p037")>]
[<TestCase(34, TestName = "cooper.p038")>]
[<TestCase(35, TestName = "cooper.p039")>]
[<TestCase(36, TestName = "cooper.p040")>]
[<TestCase(37, TestName = "cooper.p041")>]
[<TestCase(38, TestName = "cooper.p043")>]
[<TestCase(39, TestName = "cooper.p044")>]
[<TestCase(40, TestName = "cooper.p046")>]
[<TestCase(41, TestName = "cooper.p047")>]
[<TestCase(42, TestName = "cooper.p048")>]
[<TestCase(43, TestName = "cooper.p050")>]
[<TestCase(44, TestName = "cooper.p051")>]
[<TestCase(45, TestName = "cooper.p052")>]
[<TestCase(46, TestName = "cooper.p053")>]
[<TestCase(47, TestName = "cooper.p054", Category = "LongRunning")>]
[<TestCase(48, TestName = "cooper.p055", Category = "LongRunning")>]
[<TestCase(49, TestName = "cooper.p056")>]
[<TestCase(50, TestName = "cooper.p057", Category = "LongRunning")>]
let ``integer_qelim tests`` idx =
    let (formula, _) = integer_qelimValues1.[idx]
    let (_, result) = integer_qelimValues1.[idx]
    integer_qelim (parse formula)
    |> should equal result
        
let private natural_qelimValues1 : (string * formula<fol>)[] = [|
    (
        // idx 0
        // cooper.p006
        @"forall d. exists x y. 3 * x + 5 * y = d",
        formula<fol>.False
    );
    (
        // idx 1
        // cooper.p008
        @"forall d. d >= 8 ==> exists x y. 3 * x + 5 * y = d",
        formula<fol>.False
    );
    (
        // idx 2
        // cooper.p009
        @"forall d. exists x y. 3 * x - 5 * y = d",
        formula<fol>.False
    );
    |]

[<Test>]
[<TestCase(0, TestName = "cooper.p006")>]
[<TestCase(1, TestName = "cooper.p008")>]
[<TestCase(2, TestName = "cooper.p009")>]
let ``natural_qelim tests`` idx =
    let (formula, _) = integer_qelimValues1.[idx]
    let (_, result) = integer_qelimValues1.[idx]
    natural_qelim (parse formula)
    |> should equal result
