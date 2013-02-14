// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.defcnf

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.defcnf

open NUnit.Framework
open FsUnit

let private cnfValues : (string * formula<prop> * string )[] = [| 
    (
        // idx 0
        // defcnf.p001
        @"p <=> (q <=> r)",
        And
          (Or (Atom (P "p"),Or (Atom (P "q"),Atom (P "r"))),
           And
             (Or (Atom (P "p"),Or (Not (Atom (P "q")),Not (Atom (P "r")))),
              And
                (Or (Atom (P "q"),Or (Not (Atom (P "p")),Not (Atom (P "r")))),
                 Or (Atom (P "r"),Or (Not (Atom (P "p")),Not (Atom (P "q"))))))),
        @"<<(p \/ q \/ r) /\ (p \/ ~q \/ ~r) /\ (q \/ ~p \/ ~r) /\ (r \/ ~p \/ ~q)>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "defcnf.p001")>]
let ``cnf tests`` idx = 
    let (fm, _, _) = cnfValues.[idx]
    let (_, astResult, _) = cnfValues.[idx]
    let (_, _, stringResult) = cnfValues.[idx]
    let result = cnf (parse_prop_formula fm)
    result
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private defcnfOrigValues : (string * formula<prop> * string )[] = [| 
    (
        // idx 0
        // defcnf.p002
        @"(p \/ (q /\ ~r)) /\ s",
        And
          (Or (Atom (P "p"),Or (Atom (P "p_1"),Not (Atom (P "p_2")))),
           And
             (Or (Atom (P "p_1"),Or (Atom (P "r"),Not (Atom (P "q")))),
              And
                (Or (Atom (P "p_2"),Not (Atom (P "p"))),
                 And
                   (Or (Atom (P "p_2"),Not (Atom (P "p_1"))),
                    And
                      (Or (Atom (P "p_2"),Not (Atom (P "p_3"))),
                       And
                         (Atom (P "p_3"),
                          And
                            (Or
                               (Atom (P "p_3"),
                                Or (Not (Atom (P "p_2")),Not (Atom (P "s")))),
                             And
                               (Or (Atom (P "q"),Not (Atom (P "p_1"))),
                                And
                                  (Or (Atom (P "s"),Not (Atom (P "p_3"))),
                                   Or
                                     (Not (Atom (P "p_1")),Not (Atom (P "r")))))))))))),
        @"<<(p \/ p_1 \/ ~p_2) /\ (p_1 \/ r \/ ~q) /\ (p_2 \/ ~p) /\ (p_2 \/ ~p_1) /\ " + 
           "(p_2 \/ ~p_3) /\ p_3 /\ (p_3 \/ ~p_2 \/ ~s) /\ (q \/ ~p_1) /\ (s \/ ~p_3) /\ (~p_1 \/ ~r)>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "defcnf.p002")>]
let ``defcnfOrig tests`` idx = 
    let (fm, _, _) = defcnfOrigValues.[idx]
    let (_, astResult, _) = defcnfOrigValues.[idx]
    let (_, _, stringResult) = defcnfOrigValues.[idx]
    let result = defcnfOrig (parse_prop_formula fm)
    result
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult

let private defcnfValues : (string * formula<prop> * string )[] = [| 
    (
        // idx 0
        // defcnf.p003
        @"(p \/ (q /\ ~r)) /\ s",
        And
          (Or (Atom (P "p"),Atom (P "p_1")),
           And
             (Or (Atom (P "p_1"),Or (Atom (P "r"),Not (Atom (P "q")))),
              And
                (Or (Atom (P "q"),Not (Atom (P "p_1"))),
                 And
                   (Atom (P "s"),Or (Not (Atom (P "p_1")),Not (Atom (P "r"))))))),
        @"<<(p \/ p_1) /\ (p_1 \/ r \/ ~q) /\ (q \/ ~p_1) /\ s /\ (~p_1 \/ ~r)>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "defcnf.p003")>]
let ``defcnf tests`` idx = 
    let (fm, _, _) = defcnfValues.[idx]
    let (_, astResult, _) = defcnfValues.[idx]
    let (_, _, stringResult) = defcnfValues.[idx]
    let result = defcnf (parse_prop_formula fm)
    result
    |> should equal astResult
    sprint_prop_formula result
    |> should equal stringResult
