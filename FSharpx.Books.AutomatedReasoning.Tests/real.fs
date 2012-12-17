// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.real

open FSharpx.Books.AutomatedReasoning.initialization
open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.completion
open FSharpx.Books.AutomatedReasoning.qelim
open FSharpx.Books.AutomatedReasoning.cooper
open FSharpx.Books.AutomatedReasoning.complex
open FSharpx.Books.AutomatedReasoning.real

open NUnit.Framework
open FsUnit

let private real_qelimValues : (StackSize * formula<fol> * formula<fol>)[] = [|
    (
        // idx 0
        // real.p001
        Standard,
        parse @"exists x. x^4 + x^2 + 1 = 0",
        formula<fol>.False
    );
    (
        // idx 1
        // real.p002
        Standard,
        parse @"exists x. x^3 - x^2 + x - 1 = 0",
        formula<fol>.True
    );
    (
        // idx 2
        // real.p003
        Standard,
        parse @"exists x y. x^3 - x^2 + x - 1 = 0 /\
                         y^3 - y^2 + y - 1 = 0 /\ ~(x = y)",
        formula<fol>.False
    );
    (
        // idx 3
        // real.p004
        Standard,
        parse @"exists x. x^2 - 3 * x + 2 = 0 /\ 2 * x - 3 = 0",
        formula<fol>.False
    );
    (
        // idx 4
        // real.p005
        Standard,
        parse @"forall a f k. (forall e. k < e ==> f < a * e) ==> f <= a * k",
        formula<fol>.True
    );
    (
        // idx 5
        // real.p006
        Standard,
        parse @"exists x. a * x^2 + b * x + c = 0",
        Or
          (And
             (Atom
                (R ("=",
                    [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "a"; Fn ("1",[])])]);
                     Fn ("0",[])])),
              Or
                (And
                   (Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                           Fn ("0",[])])),
                    Atom
                      (R ("=",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "c"; Fn ("1",[])])]);
                           Fn ("0",[])]))),
                 And
                   (Not
                      (Atom
                         (R ("=",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                              Fn ("0",[])]))),
                    Or
                      (Atom
                         (R (">",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "b"; Fn ("1",[])])]);
                              Fn ("0",[])])),
                       Not
                         (Atom
                            (R (">",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "b"; Fn ("1",[])])]);
                                 Fn ("0",[])]))))))),
           And
             (Not
                (Atom
                   (R ("=",
                       [Fn
                          ("+",[Fn ("0",[]); Fn ("*",[Var "a"; Fn ("1",[])])]);
                        Fn ("0",[])]))),
              Or
                (And
                   (Atom
                      (R (">",
                          [Fn
                             ("+",
                              [Fn ("0",[]); Fn ("*",[Var "a"; Fn ("1",[])])]);
                           Fn ("0",[])])),
                    Or
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
                                                          Fn ("-1",[])])])])]);
                                          Fn
                                            ("*",
                                             [Var "a";
                                              Fn
                                                ("+",
                                                 [Fn ("0",[]);
                                                  Fn
                                                    ("*",
                                                     [Var "c"; Fn ("4",[])])])])])])]);
                              Fn ("0",[])])),
                       And
                         (Not
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
                                                                Fn ("-1",[])])])])]);
                                                Fn
                                                  ("*",
                                                   [Var "a";
                                                    Fn
                                                      ("+",
                                                       [Fn ("0",[]);
                                                        Fn
                                                          ("*",
                                                           [Var "c";
                                                            Fn ("4",[])])])])])])]);
                                    Fn ("0",[])]))),
                          Not
                            (Atom
                               (R (">",
                                   [Fn
                                      ("+",
                                       [Fn ("0",[]);
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
                                                           [Fn ("0",[]);
                                                            Fn
                                                              ("*",
                                                               [Var "b";
                                                                Fn ("-1",[])])])])]);
                                                Fn
                                                  ("*",
                                                   [Var "a";
                                                    Fn
                                                      ("+",
                                                       [Fn ("0",[]);
                                                        Fn
                                                          ("*",
                                                           [Var "c";
                                                            Fn ("4",[])])])])])])]);
                                    Fn ("0",[])])))))),
                 And
                   (Not
                      (Atom
                         (R (">",
                             [Fn
                                ("+",
                                 [Fn ("0",[]); Fn ("*",[Var "a"; Fn ("1",[])])]);
                              Fn ("0",[])]))),
                    Or
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
                                                          Fn ("-1",[])])])])]);
                                          Fn
                                            ("*",
                                             [Var "a";
                                              Fn
                                                ("+",
                                                 [Fn ("0",[]);
                                                  Fn
                                                    ("*",
                                                     [Var "c"; Fn ("4",[])])])])])])]);
                              Fn ("0",[])])),
                       And
                         (Not
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
                                                                Fn ("-1",[])])])])]);
                                                Fn
                                                  ("*",
                                                   [Var "a";
                                                    Fn
                                                      ("+",
                                                       [Fn ("0",[]);
                                                        Fn
                                                          ("*",
                                                           [Var "c";
                                                            Fn ("4",[])])])])])])]);
                                    Fn ("0",[])]))),
                          Atom
                            (R (">",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
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
                                                        [Fn ("0",[]);
                                                         Fn
                                                           ("*",
                                                            [Var "b";
                                                             Fn ("-1",[])])])])]);
                                             Fn
                                               ("*",
                                                [Var "a";
                                                 Fn
                                                   ("+",
                                                    [Fn ("0",[]);
                                                     Fn
                                                       ("*",
                                                        [Var "c"; Fn ("4",[])])])])])])]);
                                 Fn ("0",[])]))))))))
    );
    (
        // idx 6
        // real.p007
        Standard,
        parse @"forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           b^2 >= 4 * a * c",
        formula<fol>.False
    );
    (
        // idx 7
        // real.p008
        Standard,
        parse @"forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           a = 0 /\ (b = 0 ==> c = 0) \/
                           ~(a = 0) /\ b^2 >= 4 * a * c",
        formula<fol>.True
    )
    (
        // idx 8
        // real.p009
        Standard,
        parse @"1 < 2 /\ (forall x. 1 < x ==> 1 < x^2) /\ (forall x y. 1 < x /\ 1 < y ==> 1 < x * (1 + 2 * y))",
        formula<fol>.True
    )
    (
        // idx 9
        // real.p012
        Large,
        list_conj (List.map grpform (complete_and_simplify ["1"; "*"; "i"] [(parse @"1 * x = x"); (parse @"i(x) * x = 1"); (parse @"(x * y) * z = x * y * z")])),
        formula<fol>.True
    )
    |]

[<TestCase(0, TestName = "real.p001")>]
[<TestCase(1, TestName = "real.p002")>]
[<TestCase(2, TestName = "real.p003")>]
[<TestCase(3, TestName = "real.p004")>]
[<TestCase(4, TestName = "real.p005")>]
[<TestCase(5, TestName = "real.p006")>]
[<TestCase(6, TestName = "real.p007")>]
[<TestCase(7, TestName = "real.p008")>]
[<TestCase(8, TestName = "real.p009")>]
[<TestCase(9, TestName = "real.p012")>]

let ``real_qelim tests`` idx =
    let (stackSize, _,  _) = real_qelimValues.[idx]
    let (_, formula, _) = real_qelimValues.[idx]
    let (_, _, result) = real_qelimValues.[idx]
    match stackSize with
    | Standard -> 
        real_qelim formula
    | Large ->
        runWithEnlargedStack (fun () -> real_qelim formula)
    |> should equal result

let private real_qelim001Values : (string * formula<fol>)[] = [|
    (
        // idx 0
        // real.p001
        @"forall d.
            (exists c. forall a b. (a = d /\ b = c) \/ (a = c /\ b = 1)
                                ==> a^2 = b)
            <=> d^4 = 1",
        formula<fol>.True
    );
    |]

[<TestCase(0, TestName = "real.p013")>]

[<Test>]
let ``real_qelim' tests`` idx =
    let (formula, _) = real_qelim001Values.[idx]
    let (_, result) = real_qelim001Values.[idx]
    real_qelim' (parse formula)
    |> should equal result
