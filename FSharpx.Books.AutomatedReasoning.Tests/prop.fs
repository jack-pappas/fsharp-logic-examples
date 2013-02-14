// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.prop

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop

open NUnit.Framework
open FsUnit

let private evalPropFormula_1_Values : (string * (formula<prop> -> formula<prop>) * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p001
        @"p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)",
        (fun x -> And(x,x)),
        And
          (Iff
             (Imp (Atom (P "p"),Atom (P "q")),
              Or
                (And (Atom (P "r"),Atom (P "s")),
                 Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v"))))),
           Iff
             (Imp (Atom (P "p"),Atom (P "q")),
              Or
                (And (Atom (P "r"),Atom (P "s")),
                 Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v")))))),
        @"<<(p ==> q <=> r /\ s \/ (t <=> ~(~u) /\ v)) /\" + 
          " (p ==> q <=> r /\ s \/ (t <=> ~(~u) /\ v))>>"
    );
    (
        // idx 1
        // prop.p002
        @"p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)",
        (fun x -> And (Or (x, x), x)),
        And
          (Or
             (Iff
                (Imp (Atom (P "p"),Atom (P "q")),
                 Or
                   (And (Atom (P "r"),Atom (P "s")),
                    Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v"))))),
              Iff
                (Imp (Atom (P "p"),Atom (P "q")),
                 Or
                   (And (Atom (P "r"),Atom (P "s")),
                    Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v")))))),
           Iff
             (Imp (Atom (P "p"),Atom (P "q")),
              Or
                (And (Atom (P "r"),Atom (P "s")),
                 Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v")))))),
        @"<<((p ==> q <=> r /\ s \/ (t <=> ~(~u) /\ v)) \/ " + 
            "(p ==> q <=> r /\ s \/ (t <=> ~(~u) /\ v))) /\ " + 
            "(p ==> q <=> r /\ s \/ (t <=> ~(~u) /\ v))>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p001")>]
[<TestCase(1, TestName = "prop.p002")>]
let ``eval prop formula 1`` idx = 
    let (prop_formula_1, _, _, _) = evalPropFormula_1_Values.[idx]
    let (_, prop_formula_2, _, _) = evalPropFormula_1_Values.[idx]
    let (_, _, astResult, _) = evalPropFormula_1_Values.[idx]
    let (_, _, _, stringResult) = evalPropFormula_1_Values.[idx]
    let result = 
        parse_prop_formula prop_formula_1
        |> prop_formula_2
    result
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private eavlBoolOperatorValues : ((bool -> bool -> bool) * bool * bool * bool)[] = [| 
    (
        // idx 0
        // prop.p003
        (&&),
        false, false,
        false
    );
    (
        // idx 
        // prop.p004
        (&&),
        false, true,
        false
    );
    (
        // idx 
        // prop.p005
        (&&),
        true, false,
        false
    );
    (
        // idx 
        // prop.p006
        (&&),
        true, true,
        true
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p003")>]
[<TestCase(1, TestName = "prop.p004")>]
[<TestCase(2, TestName = "prop.p005")>]
[<TestCase(3, TestName = "prop.p006")>]
let ``eval bool operator`` idx = 
    let (boolOperator, _, _, _) = eavlBoolOperatorValues.[idx]
    let (_, boolValue_1, _, _) = eavlBoolOperatorValues.[idx]
    let (_, _, boolValue_2, _) = eavlBoolOperatorValues.[idx]
    let (_, _, _, result) = eavlBoolOperatorValues.[idx]
    (boolOperator boolValue_1 boolValue_2)
    |> should equal result

let private evalPropFormula_2_Values : ((bool -> bool -> bool -> prop -> bool) * string * bool * bool * bool * bool)[] = [| 
    (
        // idx 0
        // prop.p007
        // Harrison #01 
        (fun p q r -> function
        | P "p" -> p
        | P "q" -> q
        | P "r" -> r
        | _ -> failwith "Invalid property name"),
        @"p /\ q ==> q /\ r",
        true, false, false,
        true
    );
    (
        // idx 1
        // prop.p008
        // Harrison #01 
        (fun p q r -> function
        | P "p" -> p
        | P "q" -> q
        | P "r" -> r
        | _ -> failwith "Invalid property name"),
        @"p /\ q ==> q /\ r",
        true, true, false,
        false
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p007")>]
[<TestCase(1, TestName = "prop.p008")>]
let ``eval prop formula 2`` idx = 
    let (func, _, _, _, _, _) = evalPropFormula_2_Values.[idx]
    let (_, propFormula, _, _, _, _) = evalPropFormula_2_Values.[idx]
    let (_, _, boolValue_1, _, _, _) = evalPropFormula_2_Values.[idx]
    let (_, _, _, boolValue_2, _, _) = evalPropFormula_2_Values.[idx]
    let (_, _, _, _, boolValue_3, _) = evalPropFormula_2_Values.[idx]
    let (_, _, _, _, _, result) = evalPropFormula_2_Values.[idx]
    (func boolValue_1 boolValue_2 boolValue_3)
    |> eval (parse_prop_formula propFormula)
    |> should equal result

let private atomValues : (string * prop list)[] = [| 
    (
        // idx 0
        // prop.p009
        "p /\ q \/ s ==> ~p \/ (r <=> s)",
        [P "p"; P "q"; P "r"; P "s"]
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p009")>]
let ``atom tests`` idx = 
    let (prop_formula, _) = atomValues.[idx]
    let (_, result) = atomValues.[idx]
    atoms (parse_prop_formula prop_formula)
    |> should equal result

let private tautologyValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // prop.p014
        // Pelletier #06
        parse_prop_formula @"p \/ ~p",
        true
    );
    (
        // idx 1
        // prop.p015
        parse_prop_formula @"p \/ q ==> p",
        false
    );
    (
        // idx 2
        // prop.p016
        parse_prop_formula @"p \/ q ==> q \/ (p <=> q)",
        false
    );
    (
        // idx 3
        // prop.p017
        parse_prop_formula @"(p \/ q) /\ ~(p /\ q) ==> (~p <=> q)",
        true
    );
    (
        // idx 4
        // prop.p019
        // Pelletier #16
        parse_prop_formula @"(p ==> q) \/ (q ==> p)",
        true
    );
    (
        // idx 5
        // prop.p020
        parse_prop_formula @"p \/ (q <=> r) <=> (p \/ q <=> p \/ r)",
        true
    );
    (
        // idx 6
        // prop.p021
        // Harrison #02 - Equations within equations
        parse_prop_formula @"p /\ q <=> ((p <=> q) <=> p \/ q)",
        true
    );
    (
        // idx 7
        // prop.p022 
        // Harrison #03 - Equations within equations
        parse_prop_formula @"(p ==> q) <=> (~q ==> ~p)",
        true
    );
    (
        // idx 8
        // prop.p023
        parse_prop_formula @"(p ==> ~q) <=> (q ==> ~p)",
        true
    );
    (
        // idx 9
        // prop.p024
        parse_prop_formula @"(p ==> q) <=> (q ==> p)",
        false
    );
    (
        // idx 10
        // prop.p029
        Iff((parse_prop_formula @"(p <=> q) <=> ~(r ==> s)"),
         nnf (parse_prop_formula @"(p <=> q) <=> ~(r ==> s)")),
        true
    );
    (
        // idx 11
        // prop.p030
        parse_prop_formula @"(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')",
        true
    );
    (
        // idx 12
        // prop.p031
        parse_prop_formula @"(p ==> p') /\ (q ==> q') ==> (p \/ q ==> p' \/ q')",
        true
    );
    (
        // idx 13
        // prop.p039
        // Harrison #04
        Iff((parse_prop_formula @"(p \/ q /\ r) /\ (~p \/ ~r)"),
         dnf (parse_prop_formula @"(p \/ q /\ r) /\ (~p \/ ~r)")),
        true
    );
    (
        // idx 14
        // prop.p041
        // Harrison #04
        Iff((parse_prop_formula @"(p \/ q /\ r) /\ (~p \/ ~r)"),
         cnf (parse_prop_formula @"(p \/ q /\ r) /\ (~p \/ ~r)")),
        true
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p014")>]
[<TestCase(1, TestName = "prop.p015")>]
[<TestCase(2, TestName = "prop.p016")>]
[<TestCase(3, TestName = "prop.p017")>]
[<TestCase(4, TestName = "prop.p019")>]
[<TestCase(5, TestName = "prop.p020")>]
[<TestCase(6, TestName = "prop.p021")>]
[<TestCase(7, TestName = "prop.p022")>]
[<TestCase(8, TestName = "prop.p023")>]
[<TestCase(9, TestName = "prop.p024")>]
[<TestCase(10, TestName = "prop.p029")>]
[<TestCase(11, TestName = "prop.p030")>]
[<TestCase(12, TestName = "prop.p031")>]
[<TestCase(13, TestName = "prop.p039")>]
[<TestCase(14, TestName = "prop.p041")>]
let ``tautology tests`` idx = 
    let (prop_formula, _) = tautologyValues.[idx]
    let (_, result) = tautologyValues.[idx]
    tautology prop_formula
    |> should equal result

let private psubstValues : (func<prop,formula<prop>> * string * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p018
        ((P"p") |=> (parse_prop_formula @"p /\ q")),
        @"p /\ q /\ p /\ q",
        And
            (And (Atom (P "p"),Atom (P "q")),
                And
                    (Atom (P "q"),And (And (Atom (P "p"),Atom (P "q")),Atom (P "q")))),
        @"<<(p /\ q) /\ q /\ (p /\ q) /\ q>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p018")>]
let ``psubst tests`` idx = 
    let (subst_function, _, _, _) = psubstValues.[idx]
    let (_, formula, _, _) = psubstValues.[idx]
    let (_, _, astResult, _) = psubstValues.[idx]
    let (_, _, _, stringResult) = psubstValues.[idx]
    let result = psubst subst_function (parse_prop_formula formula)
    result 
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

// prop.p025
[<Test>]
let ``equivalences``() =
    List.forall tautology [
        parse_prop_formula "true <=> false ==> false";
        parse_prop_formula "~p <=> p ==> false";
        parse_prop_formula "p /\ q <=> (p ==> q ==> false) ==> false";
        parse_prop_formula "p \/ q <=> (p ==> false) ==> q";
        parse_prop_formula "(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false"; ]
    |> should be True

let private dualValues : (string * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p026
        // Pelletier #06
        @"p \/ ~p",
        And (Atom (P "p"),Not (Atom (P "p"))),
        @"<<p /\ ~p>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p026")>]
let ``dual tests`` idx = 
    let (formula, _, _) = dualValues.[idx]
    let (_, astResult, _) = dualValues.[idx]
    let (_, _, stringResult) = dualValues.[idx]
    let result = dual (parse_prop_formula formula)
    result 
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private psimplifyValues : (string * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p027
        @"(true ==> (x <=> false)) ==> ~(y \/ false /\ z)",
        Imp (Not (Atom (P "x")),Not (Atom (P "y"))),
        @"<<~x ==> ~y>>"
    );
    (
        // idx 1
        // prop.p028
        @"((x ==> y) ==> true) \/ ~false",
        formula<prop>.True,
        @"<<true>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p027")>]
[<TestCase(1, TestName = "prop.p028")>]
let ``psimplify tests`` idx = 
    let (formula, _, _) = psimplifyValues.[idx]
    let (_, astResult, _) = psimplifyValues.[idx]
    let (_, _, stringResult) = psimplifyValues.[idx]
    let result = psimplify (parse_prop_formula formula)
    result 
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private dnfOrigValues : (string * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p032
        // Harrison #04 
        @"(p \/ q /\ r) /\ (~p \/ ~r)",
        Or
          (And (Not (Atom (P "p")),And (Atom (P "q"),Atom (P "r"))),
           Or
             (And (Atom (P "p"),And (Not (Atom (P "q")),Not (Atom (P "r")))),
              And (Atom (P "p"),And (Atom (P "q"),Not (Atom (P "r")))))),
        @"<<~p /\ q /\ r \/ p /\ ~q /\ ~r \/ p /\ q /\ ~r>>"
    ); 
    (
        // idx 1
        // prop.p034
        @"p /\ q /\ r /\ s /\ t /\ u \/ u /\ v",
        Or
            (And
               (Not (Atom (P "p")),
                And
                  (Not (Atom (P "q")),
                   And
                     (Not (Atom (P "r")),
                      And
                        (Not (Atom (P "s")),
                         And
                           (Not (Atom (P "t")),And (Atom (P "u"),Atom (P "v"))))))),
             Or
               (And
                  (Not (Atom (P "p")),
                   And
                     (Not (Atom (P "q")),
                      And
                        (Not (Atom (P "r")),
                         And
                           (Not (Atom (P "s")),
                            And (Atom (P "t"),And (Atom (P "u"),Atom (P "v"))))))),
                Or
                  (And
                     (Not (Atom (P "p")),
                      And
                        (Not (Atom (P "q")),
                         And
                           (Not (Atom (P "r")),
                            And
                              (Atom (P "s"),
                               And
                                 (Not (Atom (P "t")),
                                  And (Atom (P "u"),Atom (P "v"))))))),
                   Or
                     (And
                        (Not (Atom (P "p")),
                         And
                           (Not (Atom (P "q")),
                            And
                              (Not (Atom (P "r")),
                               And
                                 (Atom (P "s"),
                                  And
                                    (Atom (P "t"),
                                     And (Atom (P "u"),Atom (P "v"))))))),
                      Or
                        (And
                           (Not (Atom (P "p")),
                            And
                              (Not (Atom (P "q")),
                               And
                                 (Atom (P "r"),
                                  And
                                    (Not (Atom (P "s")),
                                     And
                                       (Not (Atom (P "t")),
                                        And (Atom (P "u"),Atom (P "v"))))))),
                         Or
                           (And
                              (Not (Atom (P "p")),
                               And
                                 (Not (Atom (P "q")),
                                  And
                                    (Atom (P "r"),
                                     And
                                       (Not (Atom (P "s")),
                                        And
                                          (Atom (P "t"),
                                           And (Atom (P "u"),Atom (P "v"))))))),
                            Or
                              (And
                                 (Not (Atom (P "p")),
                                  And
                                    (Not (Atom (P "q")),
                                     And
                                       (Atom (P "r"),
                                        And
                                          (Atom (P "s"),
                                           And
                                             (Not (Atom (P "t")),
                                              And (Atom (P "u"),Atom (P "v"))))))),
                               Or
                                 (And
                                    (Not (Atom (P "p")),
                                     And
                                       (Not (Atom (P "q")),
                                        And
                                          (Atom (P "r"),
                                           And
                                             (Atom (P "s"),
                                              And
                                                (Atom (P "t"),
                                                 And (Atom (P "u"),Atom (P "v"))))))),
                                  Or
                                    (And
                                       (Not (Atom (P "p")),
                                        And
                                          (Atom (P "q"),
                                           And
                                             (Not (Atom (P "r")),
                                              And
                                                (Not (Atom (P "s")),
                                                 And
                                                   (Not (Atom (P "t")),
                                                    And
                                                      (Atom (P "u"),Atom (P "v"))))))),
                                     Or
                                       (And
                                          (Not (Atom (P "p")),
                                           And
                                             (Atom (P "q"),
                                              And
                                                (Not (Atom (P "r")),
                                                 And
                                                   (Not (Atom (P "s")),
                                                    And
                                                      (Atom (P "t"),
                                                       And
                                                         (Atom (P "u"),
                                                          Atom (P "v"))))))),
                                        Or
                                          (And
                                             (Not (Atom (P "p")),
                                              And
                                                (Atom (P "q"),
                                                 And
                                                   (Not (Atom (P "r")),
                                                    And
                                                      (Atom (P "s"),
                                                       And
                                                         (Not (Atom (P "t")),
                                                          And
                                                            (Atom (P "u"),
                                                             Atom (P "v"))))))),
                                           Or
                                             (And
                                                (Not (Atom (P "p")),
                                                 And
                                                   (Atom (P "q"),
                                                    And
                                                      (Not (Atom (P "r")),
                                                       And
                                                         (Atom (P "s"),
                                                          And
                                                            (Atom (P "t"),
                                                             And
                                                               (Atom (P "u"),
                                                                Atom (P "v"))))))),
                                              Or
                                                (And
                                                   (Not (Atom (P "p")),
                                                    And
                                                      (Atom (P "q"),
                                                       And
                                                         (Atom (P "r"),
                                                          And
                                                            (Not (Atom (P "s")),
                                                             And
                                                               (Not
                                                                  (Atom (P "t")),
                                                                And
                                                                  (Atom (P "u"),
                                                                   Atom (P "v"))))))),
                                                 Or
                                                   (And
                                                      (Not (Atom (P "p")),
                                                       And
                                                         (Atom (P "q"),
                                                          And
                                                            (Atom (P "r"),
                                                             And
                                                               (Not
                                                                  (Atom (P "s")),
                                                                And
                                                                  (Atom (P "t"),
                                                                   And
                                                                     (Atom
                                                                        (P "u"),
                                                                      Atom
                                                                        (P "v"))))))),
                                                    Or
                                                      (And
                                                         (Not (Atom (P "p")),
                                                          And
                                                            (Atom (P "q"),
                                                             And
                                                               (Atom (P "r"),
                                                                And
                                                                  (Atom (P "s"),
                                                                   And
                                                                     (Not
                                                                        (Atom
                                                                           (P "t")),
                                                                      And
                                                                        (Atom
                                                                           (P "u"),
                                                                         Atom
                                                                           (P "v"))))))),
                                                       Or
                                                         (And
                                                            (Not (Atom (P "p")),
                                                             And
                                                               (Atom (P "q"),
                                                                And
                                                                  (Atom (P "r"),
                                                                   And
                                                                     (Atom
                                                                        (P "s"),
                                                                      And
                                                                        (Atom
                                                                           (P "t"),
                                                                         And
                                                                           (Atom
                                                                              (P "u"),
                                                                            Atom
                                                                              (P "v"))))))),
                                                          Or
                                                            (And
                                                               (Atom (P "p"),
                                                                And
                                                                  (Not
                                                                     (Atom
                                                                        (P "q")),
                                                                   And
                                                                     (Not
                                                                        (Atom
                                                                           (P "r")),
                                                                      And
                                                                        (Not
                                                                           (Atom
                                                                              (P "s")),
                                                                         And
                                                                           (Not
                                                                              (Atom
                                                                                 (P "t")),
                                                                            And
                                                                              (Atom
                                                                                 (P "u"),
                                                                               Atom
                                                                                 (P "v"))))))),
                                                             Or
                                                               (And
                                                                  (Atom (P "p"),
                                                                   And
                                                                     (Not
                                                                        (Atom
                                                                           (P "q")),
                                                                      And
                                                                        (Not
                                                                           (Atom
                                                                              (P "r")),
                                                                         And
                                                                           (Not
                                                                              (Atom
                                                                                 (P "s")),
                                                                            And
                                                                              (Atom
                                                                                 (P "t"),
                                                                               And
                                                                                 (Atom
                                                                                    (P "u"),
                                                                                  Atom
                                                                                    (P "v"))))))),
                                                                Or
                                                                  (And
                                                                     (Atom
                                                                        (P "p"),
                                                                      And
                                                                        (Not
                                                                           (Atom
                                                                              (P "q")),
                                                                         And
                                                                           (Not
                                                                              (Atom
                                                                                 (P "r")),
                                                                            And
                                                                              (Atom
                                                                                 (P "s"),
                                                                               And
                                                                                 (Not
                                                                                    (Atom
                                                                                       (P "t")),
                                                                                  And
                                                                                    (Atom
                                                                                       (P "u"),
                                                                                     Atom
                                                                                       (P "v"))))))),
                                                                   Or
                                                                     (And
                                                                        (Atom
                                                                           (P "p"),
                                                                         And
                                                                           (Not
                                                                              (Atom
                                                                                 (P "q")),
                                                                            And
                                                                              (Not
                                                                                 (Atom
                                                                                    (P "r")),
                                                                               And
                                                                                 (Atom
                                                                                    (P "s"),
                                                                                  And
                                                                                    (Atom
                                                                                       (P "t"),
                                                                                     And
                                                                                       (Atom
                                                                                          (P "u"),
                                                                                        Atom
                                                                                          (P "v"))))))),
                                                                      Or
                                                                        (And
                                                                           (Atom
                                                                              (P "p"),
                                                                            And
                                                                              (Not
                                                                                 (Atom
                                                                                    (P "q")),
                                                                               And
                                                                                 (Atom
                                                                                    (P "r"),
                                                                                  And
                                                                                    (Not
                                                                                       (Atom
                                                                                          (P "s")),
                                                                                     And
                                                                                       (Not
                                                                                          (Atom
                                                                                             (P "t")),
                                                                                        And
                                                                                          (Atom
                                                                                             (P "u"),
                                                                                           Atom
                                                                                             (P "v"))))))),
                                                                         Or
                                                                           (And
                                                                              (Atom
                                                                                 (P "p"),
                                                                               And
                                                                                 (Not
                                                                                    (Atom
                                                                                       (P "q")),
                                                                                  And
                                                                                    (Atom
                                                                                       (P "r"),
                                                                                     And
                                                                                       (Not
                                                                                          (Atom
                                                                                             (P "s")),
                                                                                        And
                                                                                          (Atom
                                                                                             (P "t"),
                                                                                           And
                                                                                             (Atom
                                                                                                (P "u"),
                                                                                              Atom
                                                                                                (P "v"))))))),
                                                                            Or
                                                                              (And
                                                                                 (Atom
                                                                                    (P "p"),
                                                                                  And
                                                                                    (Not
                                                                                       (Atom
                                                                                          (P "q")),
                                                                                     And
                                                                                       (Atom
                                                                                          (P "r"),
                                                                                        And
                                                                                          (Atom
                                                                                             (P "s"),
                                                                                           And
                                                                                             (Not
                                                                                                (Atom
                                                                                                   (P "t")),
                                                                                              And
                                                                                                (Atom
                                                                                                   (P "u"),
                                                                                                 Atom
                                                                                                   (P "v"))))))),
                                                                               Or
                                                                                 (And
                                                                                    (Atom
                                                                                       (P "p"),
                                                                                     And
                                                                                       (Not
                                                                                          (Atom
                                                                                             (P "q")),
                                                                                        And
                                                                                          (Atom
                                                                                             (P "r"),
                                                                                           And
                                                                                             (Atom
                                                                                                (P "s"),
                                                                                              And
                                                                                                (Atom
                                                                                                   (P "t"),
                                                                                                 And
                                                                                                   (Atom
                                                                                                      (P "u"),
                                                                                                    Atom
                                                                                                      (P "v"))))))),
                                                                                  Or
                                                                                    (And
                                                                                       (Atom
                                                                                          (P "p"),
                                                                                        And
                                                                                          (Atom
                                                                                             (P "q"),
                                                                                           And
                                                                                             (Not
                                                                                                (Atom
                                                                                                   (P "r")),
                                                                                              And
                                                                                                (Not
                                                                                                   (Atom
                                                                                                      (P "s")),
                                                                                                 And
                                                                                                   (Not
                                                                                                      (Atom
                                                                                                         (P "t")),
                                                                                                    And
                                                                                                      (Atom
                                                                                                         (P "u"),
                                                                                                       Atom
                                                                                                         (P "v"))))))),
                                                                                     Or
                                                                                       (And
                                                                                          (Atom
                                                                                             (P "p"),
                                                                                           And
                                                                                             (Atom
                                                                                                (P "q"),
                                                                                              And
                                                                                                (Not
                                                                                                   (Atom
                                                                                                      (P "r")),
                                                                                                 And
                                                                                                   (Not
                                                                                                      (Atom
                                                                                                         (P "s")),
                                                                                                    And
                                                                                                      (Atom
                                                                                                         (P "t"),
                                                                                                       And
                                                                                                         (Atom
                                                                                                            (P "u"),
                                                                                                          Atom
                                                                                                            (P "v"))))))),
                                                                                        Or
                                                                                          (And
                                                                                             (Atom
                                                                                                (P "p"),
                                                                                              And
                                                                                                (Atom
                                                                                                   (P "q"),
                                                                                                 And
                                                                                                   (Not
                                                                                                      (Atom
                                                                                                         (P "r")),
                                                                                                    And
                                                                                                      (Atom
                                                                                                         (P "s"),
                                                                                                       And
                                                                                                         (Not
                                                                                                            (Atom
                                                                                                               (P "t")),
                                                                                                          And
                                                                                                            (Atom
                                                                                                               (P "u"),
                                                                                                             Atom
                                                                                                               (P "v"))))))),
                                                                                           Or
                                                                                             (And
                                                                                                (Atom
                                                                                                   (P "p"),
                                                                                                 And
                                                                                                   (Atom
                                                                                                      (P "q"),
                                                                                                    And
                                                                                                      (Not
                                                                                                         (Atom
                                                                                                            (P "r")),
                                                                                                       And
                                                                                                         (Atom
                                                                                                            (P "s"),
                                                                                                          And
                                                                                                            (Atom
                                                                                                               (P "t"),
                                                                                                             And
                                                                                                               (Atom
                                                                                                                  (P "u"),
                                                                                                                Atom
                                                                                                                  (P "v"))))))),
                                                                                              Or
                                                                                                (And
                                                                                                   (Atom
                                                                                                      (P "p"),
                                                                                                    And
                                                                                                      (Atom
                                                                                                         (P "q"),
                                                                                                       And
                                                                                                         (Atom
                                                                                                            (P "r"),
                                                                                                          And
                                                                                                            (Not
                                                                                                               (Atom
                                                                                                                  (P "s")),
                                                                                                             And
                                                                                                               (Not
                                                                                                                  (Atom
                                                                                                                     (P "t")),
                                                                                                                And
                                                                                                                  (Atom
                                                                                                                     (P "u"),
                                                                                                                   Atom
                                                                                                                     (P "v"))))))),
                                                                                                 Or
                                                                                                   (And
                                                                                                      (Atom
                                                                                                         (P "p"),
                                                                                                       And
                                                                                                         (Atom
                                                                                                            (P "q"),
                                                                                                          And
                                                                                                            (Atom
                                                                                                               (P "r"),
                                                                                                             And
                                                                                                               (Not
                                                                                                                  (Atom
                                                                                                                     (P "s")),
                                                                                                                And
                                                                                                                  (Atom
                                                                                                                     (P "t"),
                                                                                                                   And
                                                                                                                     (Atom
                                                                                                                        (P "u"),
                                                                                                                      Atom
                                                                                                                        (P "v"))))))),
                                                                                                    Or
                                                                                                      (And
                                                                                                         (Atom
                                                                                                            (P "p"),
                                                                                                          And
                                                                                                            (Atom
                                                                                                               (P "q"),
                                                                                                             And
                                                                                                               (Atom
                                                                                                                  (P "r"),
                                                                                                                And
                                                                                                                  (Atom
                                                                                                                     (P "s"),
                                                                                                                   And
                                                                                                                     (Not
                                                                                                                        (Atom
                                                                                                                           (P "t")),
                                                                                                                      And
                                                                                                                        (Atom
                                                                                                                           (P "u"),
                                                                                                                         Atom
                                                                                                                           (P "v"))))))),
                                                                                                       Or
                                                                                                         (And
                                                                                                            (Atom
                                                                                                               (P "p"),
                                                                                                             And
                                                                                                               (Atom
                                                                                                                  (P "q"),
                                                                                                                And
                                                                                                                  (Atom
                                                                                                                     (P "r"),
                                                                                                                   And
                                                                                                                     (Atom
                                                                                                                        (P "s"),
                                                                                                                      And
                                                                                                                        (Atom
                                                                                                                           (P "t"),
                                                                                                                         And
                                                                                                                           (Atom
                                                                                                                              (P "u"),
                                                                                                                            Not
                                                                                                                              (Atom
                                                                                                                                 (P "v")))))))),
                                                                                                          And
                                                                                                            (Atom
                                                                                                               (P "p"),
                                                                                                             And
                                                                                                               (Atom
                                                                                                                  (P "q"),
                                                                                                                And
                                                                                                                  (Atom
                                                                                                                     (P "r"),
                                                                                                                   And
                                                                                                                     (Atom
                                                                                                                        (P "s"),
                                                                                                                      And
                                                                                                                        (Atom
                                                                                                                           (P "t"),
                                                                                                                         And
                                                                                                                           (Atom
                                                                                                                              (P "u"),
                                                                                                                            Atom
                                                                                                                              (P "v"))))))))))))))))))))))))))))))))))))))),
        @"<<~p /\ ~q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "~p /\ ~q /\ ~r /\ ~s /\ t /\ u /\ v \/ " + 
           "~p /\ ~q /\ ~r /\ s /\ ~t /\ u /\ v \/ " + 
           "~p /\ ~q /\ ~r /\ s /\ t /\ u /\ v \/ " + 
           "~p /\ ~q /\ r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "~p /\ ~q /\ r /\ ~s /\ t /\ u /\ v \/ " + 
           "~p /\ ~q /\ r /\ s /\ ~t /\ u /\ v \/ " + 
           "~p /\ ~q /\ r /\ s /\ t /\ u /\ v \/ " + 
           "~p /\ q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "~p /\ q /\ ~r /\ ~s /\ t /\ u /\ v \/ " + 
           "~p /\ q /\ ~r /\ s /\ ~t /\ u /\ v \/ " + 
           "~p /\ q /\ ~r /\ s /\ t /\ u /\ v \/ " + 
           "~p /\ q /\ r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "~p /\ q /\ r /\ ~s /\ t /\ u /\ v \/ " + 
           "~p /\ q /\ r /\ s /\ ~t /\ u /\ v \/ " + 
           "~p /\ q /\ r /\ s /\ t /\ u /\ v \/ " + 
           "p /\ ~q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "p /\ ~q /\ ~r /\ ~s /\ t /\ u /\ v \/ " + 
           "p /\ ~q /\ ~r /\ s /\ ~t /\ u /\ v \/ " + 
           "p /\ ~q /\ ~r /\ s /\ t /\ u /\ v \/ " + 
           "p /\ ~q /\ r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "p /\ ~q /\ r /\ ~s /\ t /\ u /\ v \/ " + 
           "p /\ ~q /\ r /\ s /\ ~t /\ u /\ v \/ " + 
           "p /\ ~q /\ r /\ s /\ t /\ u /\ v \/ " + 
           "p /\ q /\ ~r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "p /\ q /\ ~r /\ ~s /\ t /\ u /\ v \/ " + 
           "p /\ q /\ ~r /\ s /\ ~t /\ u /\ v \/ " + 
           "p /\ q /\ ~r /\ s /\ t /\ u /\ v \/ " + 
           "p /\ q /\ r /\ ~s /\ ~t /\ u /\ v \/ " + 
           "p /\ q /\ r /\ ~s /\ t /\ u /\ v \/ " + 
           "p /\ q /\ r /\ s /\ ~t /\ u /\ v \/ " + 
           "p /\ q /\ r /\ s /\ t /\ u /\ ~v \/ " + 
           "p /\ q /\ r /\ s /\ t /\ u /\ v>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p032")>]
[<TestCase(1, TestName = "prop.p034")>]
let ``dnf original tests`` idx = 
    let (formula, _, _) = dnfOrigValues.[idx]
    let (_, astResult, _) = dnfOrigValues.[idx]
    let (_, _, stringResult) = dnfOrigValues.[idx]
    let result = dnfOrig (parse_prop_formula formula)
    result 
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private dnfRawValues : (string * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p035
        // Harrison #04 
        @"(p \/ q /\ r) /\ (~p \/ ~r)",
        Or
            (Or
               (And (Atom (P "p"),Not (Atom (P "p"))),
                And (And (Atom (P "q"),Atom (P "r")),Not (Atom (P "p")))),
             Or
               (And (Atom (P "p"),Not (Atom (P "r"))),
                And (And (Atom (P "q"),Atom (P "r")),Not (Atom (P "r"))))),
        @"<<(p /\ ~p \/ (q /\ r) /\ ~p) \/ p /\ ~r \/ (q /\ r) /\ ~r>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p035")>]
let ``dnf raw tests`` idx = 
    let (formula, _, _) = dnfRawValues.[idx]
    let (_, astResult, _) = dnfRawValues.[idx]
    let (_, _, stringResult) = dnfRawValues.[idx]
    let result = rawdnf (parse_prop_formula formula)
    result 
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private dnfPureValues : (string * formula<prop> list list * string)[] = [| 
    (
        // idx 0
        // prop.p036
        // Harrison #04 
        @"(p \/ q /\ r) /\ (~p \/ ~r)",
        [[Atom (P "p"); Not (Atom (P "p"))];
         [Atom (P "p"); Not (Atom (P "r"))];
         [Atom (P "q"); Atom (P "r"); Not (Atom (P "p"))];
         [Atom (P "q"); Atom (P "r"); Not (Atom (P "r"))]],
        @"[[<<p>>; <<~p>>]; [<<p>>; <<~r>>]; [<<q>>; <<r>>; <<~p>>];
          [<<q>>; <<r>>; <<~r>>]]"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p036")>]
let ``dnf Pure tests`` idx = 
    let (formula, _, _) = dnfPureValues.[idx]
    let (_, astResult, _) = dnfPureValues.[idx]
    let (_, _, stringResult) = dnfPureValues.[idx]
    let result = purednf (parse_prop_formula formula)
    result 
    |> should equal astResult
    // TODO: Figure out how to generate stringResult. Works in FSI but not here.
//    sprint_prop_formula result
//    |> should equal stringResult

// prop.p037
// Harrison #04
[<Test>]
let ``non-trivial purednf``() =
    List.filter (non trivial) (purednf (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)")))
    |> should equal [[Atom (P "p"); Not (Atom (P "r"))]; 
                        [Atom (P "q"); Atom (P "r"); Not (Atom (P "p"))]]

let private dnfValues : (string * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p038
        // Harrison #04 
        @"(p \/ q /\ r) /\ (~p \/ ~r)",
        Or
            (And (Atom (P "p"),Not (Atom (P "r"))),
             And (Atom (P "q"),And (Atom (P "r"),Not (Atom (P "p"))))),
        @"<<p /\ ~r \/ q /\ r /\ ~p>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p038")>]
let ``dnf tests`` idx = 
    let (formula, _, _) = dnfValues.[idx]
    let (_, astResult, _) = dnfValues.[idx]
    let (_, _, stringResult) = dnfValues.[idx]
    let result = dnf (parse_prop_formula formula)
    result 
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private cnfValues : (string * formula<prop> * string)[] = [| 
    (
        // idx 0
        // prop.p040
        // Harrison #04 
        @"(p \/ q /\ r) /\ (~p \/ ~r)",
        And
            (Or (Atom (P "p"),Atom (P "q")),
             And
               (Or (Atom (P "p"),Atom (P "r")),
                Or (Not (Atom (P "p")),Not (Atom (P "r"))))),
        @"<<(p \/ q) /\ (p \/ r) /\ (~p \/ ~r)>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p040")>]
let ``cnf tests`` idx = 
    let (formula, _, _) = cnfValues.[idx]
    let (_, astResult, _) = cnfValues.[idx]
    let (_, _, stringResult) = cnfValues.[idx]
    let result = cnf (parse_prop_formula formula)
    result 
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private truthTableValues : (string * string)[] = [| 
    (
        // idx 0
        // prop.p010
        // Harrison #01 
        @"p /\ q ==> q /\ r", 
        "p     q     r     | formula\r\n" + 
        "---------------------------\r\n" + 
        "false false false | true  \r\n" + 
        "false false true  | true  \r\n" + 
        "false true  false | true  \r\n" + 
        "false true  true  | true  \r\n" + 
        "true  false false | true  \r\n" + 
        "true  false true  | true  \r\n" + 
        "true  true  false | false \r\n" + 
        "true  true  true  | true  \r\n" + 
        "---------------------------\r\n\r\n"
    );
    (
        // idx 1
        // prop.p012
        // Pelletier #08
        @"((p ==> q) ==> p) ==> p", 
        "p     q     | formula\r\n" + 
        "---------------------\r\n" + 
        "false false | true  \r\n" + 
        "false true  | true  \r\n" + 
        "true  false | true  \r\n" + 
        "true  true  | true  \r\n" +
         "---------------------\r\n\r\n"
    );
    (
        // idx 2
        // prop.p013
        @"p /\ ~p", 
        "p     | formula\r\n" + 
        "---------------\r\n" + 
        "false | false \r\n" + 
        "true  | false \r\n" + 
        "---------------\r\n\r\n"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "prop.p010")>]
[<TestCase(1, TestName = "prop.p012")>]
[<TestCase(2, TestName = "prop.p013")>]
let ``truthTable tests`` idx = 
    let (formula, _) = truthTableValues.[idx]
    let (_, result) = truthTableValues.[idx]
    sprint_truthtable (parse_prop_formula formula)
    |> should equal result
