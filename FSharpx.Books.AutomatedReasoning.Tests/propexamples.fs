// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.propexamples

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples

open NUnit.Framework
open FsUnit

let private ramseyValues : (int * int * int * formula<prop> * string)[] = [| 
    (
        // idx 0
        // propexamples.p001
        3, 3, 4,
        Or
            (Or
               (And (Atom (P "p_1_2"),And (Atom (P "p_1_3"),Atom (P "p_2_3"))),
                Or
                  (And
                     (Atom (P "p_1_2"),And (Atom (P "p_1_4"),Atom (P "p_2_4"))),
                   Or
                     (And
                        (Atom (P "p_1_3"),
                         And (Atom (P "p_1_4"),Atom (P "p_3_4"))),
                      And
                        (Atom (P "p_2_3"),
                         And (Atom (P "p_2_4"),Atom (P "p_3_4")))))),
             Or
               (And
                  (Not (Atom (P "p_1_2")),
                   And (Not (Atom (P "p_1_3")),Not (Atom (P "p_2_3")))),
                Or
                  (And
                     (Not (Atom (P "p_1_2")),
                      And (Not (Atom (P "p_1_4")),Not (Atom (P "p_2_4")))),
                   Or
                     (And
                        (Not (Atom (P "p_1_3")),
                         And (Not (Atom (P "p_1_4")),Not (Atom (P "p_3_4")))),
                      And
                        (Not (Atom (P "p_2_3")),
                         And (Not (Atom (P "p_2_4")),Not (Atom (P "p_3_4")))))))),
        @"<<(p_1_2 /\ p_1_3 /\ p_2_3 \/ p_1_2 /\ p_1_4 /\ p_2_4 \/ p_1_3 /\ p_1_4 /\ p_3_4 \/ p_2_3 /\ p_2_4 /\ p_3_4) \/ " + 
           "~p_1_2 /\ ~p_1_3 /\ ~p_2_3 \/ ~p_1_2 /\ ~p_1_4 /\ ~p_2_4 \/ ~p_1_3 /\ ~p_1_4 /\ ~p_3_4 \/ ~p_2_3 /\ ~p_2_4 /\ ~p_3_4>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "propexamples.p001")>]
let ``ramsey tests`` idx = 
    let (s, _, _, _, _) = ramseyValues.[idx]
    let (_, t, _, _, _) = ramseyValues.[idx]
    let (_, _, n, _, _) = ramseyValues.[idx]
    let (_, _, _, astResult, _) = ramseyValues.[idx]
    let (_, _, _, _, stringResult) = ramseyValues.[idx]
    let result = ramsey s t n
    result 
    |> should equal astResult
    sprint_prop_formula astResult
    |> should equal stringResult

let private tautologyValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // propexamples.p002
        (ramsey 3 3 5),
        false
    );
    (
        // idx 1
        // propexamples.p003
        (ramsey 3 3 6),
        true
    );
    (
        // idx 2
        // propexamples.p005
        (prime 7),
        true
    );
    (
        // idx 3
        // propexamples.p006
        (prime 9),
        false
    );
    (
        // idx 4
        // propexamples.p007
        (prime 11),
        true
    );
    |]

[<Test>]
[<TestCase(0, TestName = "propexamples.p002")>]
[<TestCase(1, TestName = "propexamples.p003")>]
[<TestCase(2, TestName = "propexamples.p005")>]
[<TestCase(3, TestName = "propexamples.p006")>]
[<TestCase(4, TestName = "propexamples.p007")>]
let ``tautology tests`` idx = 
    let (prop_formula, _) = tautologyValues.[idx]
    let (_, result) = tautologyValues.[idx]
    tautology prop_formula
    |> should equal result

let private ripplecarryValues : ((int -> formula<prop>) list * int * formula<prop> * string)[] = [| 
//let private ripplecarryValues = [| 
    (
        // idx 0
        // propexamples.p008
        (List.map mk_index ["X"; "Y"; "OUT"; "C"]),
        1,
        And
          (Iff
             (Atom (P "C_0"),
              Iff (Iff (Atom (P "X_0"),Not (Atom (P "Y_0"))),Not (Atom (P "OUT_0")))),
           Iff
             (Atom (P "OUT_1"),
              Or
                (And (Atom (P "X_0"),Atom (P "Y_0")),
                 And (Or (Atom (P "X_0"),Atom (P "Y_0")),Atom (P "OUT_0"))))),
        @"<<(C_0 <=> (X_0 <=> ~Y_0) <=> ~OUT_0) /\ (OUT_1 <=> X_0 /\ Y_0 \/ (X_0 \/ Y_0) /\ OUT_0)>>"
    );
    (
        // idx 1
        // propexamples.p004
        (List.map mk_index ["X"; "Y"; "OUT"; "C"]),
        2,
        And
          (And
             (Iff
                (Atom (P "C_0"),
                 Iff (Iff (Atom (P "X_0"),Not (Atom (P "Y_0"))),Not (Atom (P "OUT_0")))),
              Iff
                (Atom (P "OUT_1"),
                 Or
                   (And (Atom (P "X_0"),Atom (P "Y_0")),
                    And (Or (Atom (P "X_0"),Atom (P "Y_0")),Atom (P "OUT_0"))))),
           And
             (Iff
                (Atom (P "C_1"),
                 Iff (Iff (Atom (P "X_1"),Not (Atom (P "Y_1"))),Not (Atom (P "OUT_1")))),
              Iff
                (Atom (P "OUT_2"),
                 Or
                   (And (Atom (P "X_1"),Atom (P "Y_1")),
                    And (Or (Atom (P "X_1"),Atom (P "Y_1")),Atom (P "OUT_1")))))),
        @"<<((C_0 <=> (X_0 <=> ~Y_0) <=> ~OUT_0) /\ (OUT_1 <=> X_0 /\ Y_0 \/ (X_0 \/ Y_0) /\ OUT_0)) /\ " + 
            "(C_1 <=> (X_1 <=> ~Y_1) <=> ~OUT_1) /\ (OUT_2 <=> X_1 /\ Y_1 \/ (X_1 \/ Y_1) /\ OUT_1)>>"
    );
    (
        // idx 2
        // propexamples.p009
        (List.map mk_index ["X"; "Y"; "OUT"; "C"]),
        4,
        And
          (And
             (Iff
                (Atom (P "C_0"),
                 Iff (Iff (Atom (P "X_0"),Not (Atom (P "Y_0"))),Not (Atom (P "OUT_0")))),
              Iff
                (Atom (P "OUT_1"),
                 Or
                   (And (Atom (P "X_0"),Atom (P "Y_0")),
                    And (Or (Atom (P "X_0"),Atom (P "Y_0")),Atom (P "OUT_0"))))),
           And
             (And
                (Iff
                   (Atom (P "C_1"),
                    Iff
                      (Iff (Atom (P "X_1"),Not (Atom (P "Y_1"))),Not (Atom (P "OUT_1")))),
                 Iff
                   (Atom (P "OUT_2"),
                    Or
                      (And (Atom (P "X_1"),Atom (P "Y_1")),
                       And (Or (Atom (P "X_1"),Atom (P "Y_1")),Atom (P "OUT_1"))))),
              And
                (And
                   (Iff
                      (Atom (P "C_2"),
                       Iff
                         (Iff (Atom (P "X_2"),Not (Atom (P "Y_2"))),
                          Not (Atom (P "OUT_2")))),
                    Iff
                      (Atom (P "OUT_3"),
                       Or
                         (And (Atom (P "X_2"),Atom (P "Y_2")),
                          And (Or (Atom (P "X_2"),Atom (P "Y_2")),Atom (P "OUT_2"))))),
                 And
                   (Iff
                      (Atom (P "C_3"),
                       Iff
                         (Iff (Atom (P "X_3"),Not (Atom (P "Y_3"))),
                          Not (Atom (P "OUT_3")))),
                    Iff
                      (Atom (P "OUT_4"),
                       Or
                         (And (Atom (P "X_3"),Atom (P "Y_3")),
                          And (Or (Atom (P "X_3"),Atom (P "Y_3")),Atom (P "OUT_3")))))))),
        @"<<((C_0 <=> (X_0 <=> ~Y_0) <=> ~OUT_0) /\ (OUT_1 <=> X_0 /\ Y_0 \/ (X_0 \/ Y_0) /\ OUT_0)) /\ ((C_1 <=> (X_1 <=> ~Y_1) <=> ~OUT_1) /\ (OUT_2 <=> X_1 /\ Y_1 \/ (X_1 \/ Y_1) /\ OUT_1)) /\ ((C_2 <=> (X_2 <=> ~Y_2) <=> ~OUT_2) /\ (OUT_3 <=> X_2 /\ Y_2 \/ (X_2 \/ Y_2) /\ OUT_2)) /\ (C_3 <=> (X_3 <=> ~Y_3) <=> ~OUT_3) /\ (OUT_4 <=> X_3 /\ Y_3 \/ (X_3 \/ Y_3) /\ OUT_3)>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "propexamples.p008")>]
[<TestCase(1, TestName = "propexamples.p004")>]
[<TestCase(2, TestName = "propexamples.p009")>]
let ``ripplecarry tests`` idx = 
    let (formulas, _, _, _) = ripplecarryValues.[idx]
    let (_, n, _, _) = ripplecarryValues.[idx]
    let (_, _, resultAst, _) = ripplecarryValues.[idx]
    let (_, _, _, resultString) = ripplecarryValues.[idx]
    let [x; y; out; c] = formulas
    let result = ripplecarry x y out c n
    result 
    |> should equal resultAst
    sprint_prop_formula result
    |> should equal resultString
