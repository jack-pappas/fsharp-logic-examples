// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.limitations

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop
open FSharpx.Books.AutomatedReasoning.folderived
open FSharpx.Books.AutomatedReasoning.tactics
open FSharpx.Books.AutomatedReasoning.limitations

open FSharp.Compatibility.OCaml

open NUnit.Framework
open FsUnit

let private godelFormulaValues = [| 
    // limitations.p001  // idx 0
    ("~(x = 0)", (Num.Big_int 2116574771128325487937994357299494I));
    // limitations.p002  // idx 1
    ("x = x", (Num.Big_int 735421674029290002I))
    // limitations.p003  // idx 2
    ("0 < 0", (Num.Big_int 1767I))
    |]

[<Test>]
// limitations.p001
[<TestCase(0, TestName = "limitation.p001")>]
// limitations.p002
[<TestCase(1, TestName = "limitation.p002")>]
// limitations.p003
[<TestCase(2, TestName = "limitation.p003")>]
let ``Godel Formula`` idx = 
    let (formula, _) = godelFormulaValues.[idx]
    let (_, result) = godelFormulaValues.[idx]
    gform (parse formula)
    |> should equal result
    

let private diag001Values = [| 
    // limitations.p004  // idx 0
    ("p(x)",
     "p(`p(x)')");
    // limitations.p005  // idx 1
    ("This string is diag(x)",
     "This string is diag(`This string is diag(x)')")
    // limitations.p006  // idx 2
    ("The result of substituting the quotation of x for `x' in x \ has property P",
     "The result of substituting the quotation of `The result of substituting the quotation of x for `x' in x \ has property P' for `x' in `The result of substituting the quotation of x for `x' in x \ has property P' \ has property P")
    |]

[<Test>]
// limitations.p004
[<TestCase(0, TestName = "limitation.p004")>]
// limitations.p005
[<TestCase(1, TestName = "limitation.p005")>]
// limitations.p006
[<TestCase(2, TestName = "limitation.p006")>]
let ``diag001 test`` idx =
    let (value, _) = diag001Values.[idx]
    let (_, result) = diag001Values.[idx]
    diag001 value
    |> should equal result

let private dholdsValues = [| 
    // limitations.p007  // idx 0
    (100, false);
    // limitations.p008  // idx 1
    (101, true)
    |]

[<Test>]
// limitations.p007
[<TestCase(0, TestName = "limitation.p007")>]
// limitations.p008
[<TestCase(1, TestName = "limitation.p008")>]
let ``dholds prime`` idx =
    let (value, _) = dholdsValues.[idx]
    let (_, result) = dholdsValues.[idx]
    let prime_form p = subst("p" |=> numeral p) (parse @"S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)")
    dholds undefined (prime_form (Num.Int value))
    |> should equal result
            
// limitations.p009
[<Test>]
let ``classify``() = 
    classify Sigma 1 (parse @"forall x. x < 2 ==> exists y z. forall w. w < x + 2 ==> w + x + y + z = 42")
    |> should be True

// limitations.p010
[<Test>]
let ``sigma bound``() = 
    sigma_bound (parse @"exists p x. p < x /\ (S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)) /\ ~(x = 0) /\ forall z. z <= x ==> (exists w. w <= x /\ x = z * w) ==> z = S(0) \/ exists x. x <= z /\ z = p * x")
    |> should equal (Num.Int 4)
            
let prog_suc = 
    List.foldBack (fun m -> m)
        [(1,Blank) |-> (Blank,Right,2);  
        (2,One) |-> (One,Right,2);  
        (2,Blank) |-> (One,Right,3); 
        (3,Blank) |-> (Blank,Left,4); 
        (3,One) |-> (Blank,Left,4); 
        (4,One) |-> (One,Left,4); 
        (4,Blank) |-> (Blank,Stay,0)]  
        undefined;;

// limitations.p011
[<Test>]
let ``prog_suc 1``() = 
    exec prog_suc [0]
    |> should equal 1

// limitations.p012
[<Test>]
let ``prog_suc 2``() = 
    exec prog_suc [1]
    |> should equal 2

// limitations.p013
[<Test>]
let ``prog_suc 3``() = 
    exec prog_suc [19]
    |> should equal 20

let private robEvalValues : (string * thm ) [] = [| 
    // limitations.p014  // idx 0
    (   @"S(0) + (S(S(0)) * ((S(0) + S(S(0)) + S(0))))",
        Imp
            (And
               (Forall
                    ("m",
                    Forall
                        ("n",
                        Imp
                            (Atom (R ("=",[Fn ("S",[Var "m"]); Fn ("S",[Var "n"])])),
                                Atom (R ("=",[Var "m"; Var "n"]))))),
                And
                    (Forall
                        ("n",
                        Iff
                            (Not (Atom (R ("=",[Var "n"; Fn ("0",[])]))),
                            Exists
                                ("m",Atom (R ("=",[Var "n"; Fn ("S",[Var "m"])]))))),
                    And
                        (Forall
                            ("n",
                            Atom
                                (R ("=",[Fn ("+",[Fn ("0",[]); Var "n"]); Var "n"]))),
                        And
                            (Forall
                                ("m",
                                Forall
                                    ("n",
                                    Atom
                                        (R ("=",
                                            [Fn ("+",[Fn ("S",[Var "m"]); Var "n"]);
                                            Fn ("S",[Fn ("+",[Var "m"; Var "n"])])])))),
                            And
                                (Forall
                                    ("n",
                                    Atom
                                        (R ("=",
                                            [Fn ("*",[Fn ("0",[]); Var "n"]);
                                            Fn ("0",[])]))),
                                And
                                    (Forall
                                        ("m",
                                        Forall
                                            ("n",
                                            Atom
                                                (R ("=",
                                                    [Fn
                                                        ("*",[Fn ("S",[Var "m"]); Var "n"]);
                                                    Fn
                                                        ("+",
                                                            [Var "n";
                                                            Fn ("*",[Var "m"; Var "n"])])])))),
                                    And
                                        (Forall
                                            ("m",
                                            Forall
                                                ("n",
                                                Iff
                                                    (Atom (R ("<=",[Var "m"; Var "n"])),
                                                    Exists
                                                        ("d",
                                                            Atom
                                                                (R ("=",
                                                                    [Fn ("+",[Var "m"; Var "d"]);
                                                                        Var "n"])))))),
                                        Forall
                                            ("m",
                                            Forall
                                                ("n",
                                                Iff
                                                    (Atom (R ("<",[Var "m"; Var "n"])),
                                                    Atom
                                                        (R ("<=",
                                                            [Fn ("S",[Var "m"]); Var "n"])))))))))))),
             Atom
                (R ("=",
                    [Fn
                        ("+",
                        [Fn ("S",[Fn ("0",[])]);
                        Fn
                            ("*",
                                [Fn ("S",[Fn ("S",[Fn ("0",[])])]);
                                Fn
                                    ("+",
                                        [Fn ("S",[Fn ("0",[])]);
                                        Fn
                                            ("+",
                                                [Fn ("S",[Fn ("S",[Fn ("0",[])])]);
                                                Fn ("S",[Fn ("0",[])])])])])]);
                    Fn
                        ("S",
                            [Fn
                                ("S",
                                [Fn
                                    ("S",
                                    [Fn
                                        ("S",
                                        [Fn
                                            ("S",
                                            [Fn
                                                ("S",
                                                [Fn
                                                    ("S",
                                                    [Fn
                                                        ("S",[Fn ("S",[Fn ("0",[])])])])])])])])])])])))
    )
    |]

[<Test>]
// limitations.p014
[<TestCase(0, TestName = "limitation.p014")>]
let ``Robinson eval`` idx =
    let (tm, _) = robEvalValues.[idx]
    let (_, result) = robEvalValues.[idx]
    robeval (parset tm) 
    |> should equal result

let private robNeValues : (string * string * thm ) [] = [| 
    // limitations.p015  // idx 0
    (   @"S(0) + S(0) + S(0)",
        @"S(S(0)) * S(S(0))",
        Imp
            (And
                (Forall
                    ("m",
                    Forall
                        ("n",
                        Imp
                            (Atom (R ("=",[Fn ("S",[Var "m"]); Fn ("S",[Var "n"])])),
                                Atom (R ("=",[Var "m"; Var "n"]))))),
                And
                    (Forall
                        ("n",
                        Iff
                            (Not (Atom (R ("=",[Var "n"; Fn ("0",[])]))),
                                Exists
                                    ("m",Atom (R ("=",[Var "n"; Fn ("S",[Var "m"])]))))),
                    And
                        (Forall
                            ("n",
                            Atom
                                (R ("=",[Fn ("+",[Fn ("0",[]); Var "n"]); Var "n"]))),
                        And
                            (Forall
                                ("m",
                                Forall
                                    ("n",
                                    Atom
                                        (R ("=",
                                            [Fn ("+",[Fn ("S",[Var "m"]); Var "n"]);
                                            Fn ("S",[Fn ("+",[Var "m"; Var "n"])])])))),
                            And
                                (Forall
                                    ("n",
                                    Atom
                                        (R ("=",
                                            [Fn ("*",[Fn ("0",[]); Var "n"]);
                                            Fn ("0",[])]))),
                                    And
                                        (Forall
                                            ("m",
                                            Forall
                                                ("n",
                                                    Atom
                                                        (R ("=",
                                                            [Fn
                                                                ("*",[Fn ("S",[Var "m"]); Var "n"]);
                                                            Fn
                                                                ("+",
                                                                    [Var "n";
                                                                    Fn ("*",[Var "m"; Var "n"])])])))),
                                        And
                                            (Forall
                                                ("m",
                                                Forall
                                                    ("n",
                                                        Iff
                                                            (Atom (R ("<=",[Var "m"; Var "n"])),
                                                            Exists
                                                                ("d",
                                                                Atom
                                                                    (R ("=",
                                                                        [Fn ("+",[Var "m"; Var "d"]);
                                                                            Var "n"])))))),
                                            Forall
                                                ("m",
                                                Forall
                                                    ("n",
                                                        Iff
                                                            (Atom (R ("<",[Var "m"; Var "n"])),
                                                            Atom
                                                                (R ("<=",
                                                                    [Fn ("S",[Var "m"]); Var "n"])))))))))))),
                Imp
                    (Atom
                        (R ("=",
                            [Fn
                                ("+",
                                [Fn ("S",[Fn ("0",[])]);
                                Fn
                                    ("+",
                                        [Fn ("S",[Fn ("0",[])]); Fn ("S",[Fn ("0",[])])])]);
                            Fn
                                ("*",
                                    [Fn ("S",[Fn ("S",[Fn ("0",[])])]);
                                    Fn ("S",[Fn ("S",[Fn ("0",[])])])])])),formula<fol>.False))
    );
    // limitations.p016  // idx 1
    (   @"0 + 0 * S(0)",
        @"S(S(0)) + 0",
        Imp
            (And
                (Forall
                    ("m",
                    Forall
                        ("n",
                        Imp
                            (Atom (R ("=",[Fn ("S",[Var "m"]); Fn ("S",[Var "n"])])),
                                Atom (R ("=",[Var "m"; Var "n"]))))),
                And
                    (Forall
                        ("n",
                        Iff
                            (Not (Atom (R ("=",[Var "n"; Fn ("0",[])]))),
                                Exists
                                    ("m",Atom (R ("=",[Var "n"; Fn ("S",[Var "m"])]))))),
                    And
                        (Forall
                            ("n",
                            Atom
                                (R ("=",[Fn ("+",[Fn ("0",[]); Var "n"]); Var "n"]))),
                        And
                            (Forall
                                ("m",
                                Forall
                                    ("n",
                                    Atom
                                        (R ("=",
                                            [Fn ("+",[Fn ("S",[Var "m"]); Var "n"]);
                                            Fn ("S",[Fn ("+",[Var "m"; Var "n"])])])))),
                            And
                                (Forall
                                    ("n",
                                    Atom
                                        (R ("=",
                                            [Fn ("*",[Fn ("0",[]); Var "n"]);
                                            Fn ("0",[])]))),
                                And
                                    (Forall
                                        ("m",
                                        Forall
                                            ("n",
                                                Atom
                                                    (R ("=",
                                                        [Fn
                                                            ("*",[Fn ("S",[Var "m"]); Var "n"]);
                                                        Fn
                                                            ("+",
                                                                [Var "n";
                                                                Fn ("*",[Var "m"; Var "n"])])])))),
                                    And
                                        (Forall
                                            ("m",
                                            Forall
                                                ("n",
                                                Iff
                                                    (Atom (R ("<=",[Var "m"; Var "n"])),
                                                    Exists
                                                        ("d",
                                                        Atom
                                                            (R ("=",
                                                                [Fn ("+",[Var "m"; Var "d"]);
                                                                    Var "n"])))))),
                                            Forall
                                                ("m",
                                                Forall
                                                    ("n",
                                                        Iff
                                                            (Atom (R ("<",[Var "m"; Var "n"])),
                                                            Atom
                                                                (R ("<=",
                                                                    [Fn ("S",[Var "m"]); Var "n"])))))))))))),
                    Imp
                        (Atom
                            (R ("=",
                                [Fn
                                    ("+",
                                    [Fn ("0",[]);
                                    Fn ("*",[Fn ("0",[]); Fn ("S",[Fn ("0",[])])])]);
                                Fn ("+",[Fn ("S",[Fn ("S",[Fn ("0",[])])]); Fn ("0",[])])])),formula<fol>.False))
    );
    // limitations.p017  // idx 2
    (   @"S(S(0)) + 0",
        @"0 + 0 + 0 * 0",
        Imp
            (And
                (Forall
                    ("m",
                    Forall
                        ("n",
                        Imp
                            (Atom (R ("=",[Fn ("S",[Var "m"]); Fn ("S",[Var "n"])])),
                                Atom (R ("=",[Var "m"; Var "n"]))))),
                And
                    (Forall
                        ("n",
                        Iff
                            (Not (Atom (R ("=",[Var "n"; Fn ("0",[])]))),
                                Exists
                                    ("m",Atom (R ("=",[Var "n"; Fn ("S",[Var "m"])]))))),
                    And
                        (Forall
                            ("n",
                                Atom
                                    (R ("=",[Fn ("+",[Fn ("0",[]); Var "n"]); Var "n"]))),
                        And
                            (Forall
                                ("m",
                                Forall
                                    ("n",
                                    Atom
                                        (R ("=",
                                            [Fn ("+",[Fn ("S",[Var "m"]); Var "n"]);
                                            Fn ("S",[Fn ("+",[Var "m"; Var "n"])])])))),
                                And
                                    (Forall
                                        ("n",
                                        Atom
                                            (R ("=",
                                                [Fn ("*",[Fn ("0",[]); Var "n"]);
                                                Fn ("0",[])]))),
                                    And
                                        (Forall
                                            ("m",
                                            Forall
                                                ("n",
                                                    Atom
                                                        (R ("=",
                                                            [Fn
                                                                ("*",[Fn ("S",[Var "m"]); Var "n"]);
                                                            Fn
                                                                ("+",
                                                                    [Var "n";
                                                                    Fn ("*",[Var "m"; Var "n"])])])))),
                                        And
                                            (Forall
                                                ("m",
                                                Forall
                                                    ("n",
                                                    Iff
                                                        (Atom (R ("<=",[Var "m"; Var "n"])),
                                                        Exists
                                                            ("d",
                                                            Atom
                                                                (R ("=",
                                                                    [Fn ("+",[Var "m"; Var "d"]);
                                                                        Var "n"])))))),
                                            Forall
                                                ("m",
                                                Forall
                                                    ("n",
                                                    Iff
                                                        (Atom (R ("<",[Var "m"; Var "n"])),
                                                        Atom
                                                            (R ("<=",
                                                                [Fn ("S",[Var "m"]); Var "n"])))))))))))),
                Imp
                    (Atom
                        (R ("=",
                            [Fn ("+",[Fn ("S",[Fn ("S",[Fn ("0",[])])]); Fn ("0",[])]);
                            Fn
                                ("+",
                                    [Fn ("0",[]);
                                    Fn
                                        ("+",
                                            [Fn ("0",[]); Fn ("*",[Fn ("0",[]); Fn ("0",[])])])])])),formula<fol>.False))
    )
    |]

[<Test>]
// pg. 570
// limitations.p015
[<TestCase(0, TestName = "limitation.p015")>]
// limitations.p016
[<TestCase(1, TestName = "limitation.p016")>]
// limitations.p017
[<TestCase(2, TestName = "limitation.p017")>]
let ``Robinson ne`` idx =
    let (s, _, _) = robNeValues.[idx]
    let (_, t, _) = robNeValues.[idx]
    let (_, _, result) = robNeValues.[idx]
    rob_ne (parset s) (parset t)
    |> should equal result

// pg. 573
// ------------------------------------------------------------------------- //
// Example in the text.                                                      //
// ------------------------------------------------------------------------- //

let private sigmaValues = [| 
    // limitations.p018  // idx 0
    ( @"exists p. S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)",
        Imp
            (And
               (Forall
                  ("m",
                   Forall
                     ("n",
                      Imp
                        (Atom (R ("=",[Fn ("S",[Var "m"]); Fn ("S",[Var "n"])])),
                         Atom (R ("=",[Var "m"; Var "n"]))))),
                And
                  (Forall
                     ("n",
                      Iff
                        (Not (Atom (R ("=",[Var "n"; Fn ("0",[])]))),
                         Exists
                           ("m",Atom (R ("=",[Var "n"; Fn ("S",[Var "m"])]))))),
                   And
                     (Forall
                        ("n",
                         Atom
                           (R ("=",[Fn ("+",[Fn ("0",[]); Var "n"]); Var "n"]))),
                      And
                        (Forall
                           ("m",
                            Forall
                              ("n",
                               Atom
                                 (R ("=",
                                     [Fn ("+",[Fn ("S",[Var "m"]); Var "n"]);
                                      Fn ("S",[Fn ("+",[Var "m"; Var "n"])])])))),
                         And
                           (Forall
                              ("n",
                               Atom
                                 (R ("=",
                                     [Fn ("*",[Fn ("0",[]); Var "n"]);
                                      Fn ("0",[])]))),
                            And
                              (Forall
                                 ("m",
                                  Forall
                                    ("n",
                                     Atom
                                       (R ("=",
                                           [Fn
                                              ("*",[Fn ("S",[Var "m"]); Var "n"]);
                                            Fn
                                              ("+",
                                               [Var "n";
                                                Fn ("*",[Var "m"; Var "n"])])])))),
                               And
                                 (Forall
                                    ("m",
                                     Forall
                                       ("n",
                                        Iff
                                          (Atom (R ("<=",[Var "m"; Var "n"])),
                                           Exists
                                             ("d",
                                              Atom
                                                (R ("=",
                                                    [Fn ("+",[Var "m"; Var "d"]);
                                                     Var "n"])))))),
                                  Forall
                                    ("m",
                                     Forall
                                       ("n",
                                        Iff
                                          (Atom (R ("<",[Var "m"; Var "n"])),
                                           Atom
                                             (R ("<=",
                                                 [Fn ("S",[Var "m"]); Var "n"])))))))))))),
             Exists
               ("p",
                And
                  (Atom (R ("<=",[Fn ("S",[Fn ("S",[Fn ("0",[])])]); Var "p"])),
                   Forall
                     ("n",
                      Imp
                        (Atom (R ("<",[Var "n"; Var "p"])),
                         Imp
                           (Exists
                              ("x",
                               And
                                 (Atom (R ("<=",[Var "x"; Var "p"])),
                                  Atom
                                    (R ("=",
                                        [Var "p"; Fn ("*",[Var "n"; Var "x"])])))),
                            Atom (R ("=",[Var "n"; Fn ("S",[Fn ("0",[])])]))))))))
    )
    |]

[<Test>]
// limitations.p018
[<TestCase(0, TestName = "limitation.p018")>]
let ``sigma prove`` idx =
    let (formula, _) = sigmaValues.[idx]
    let (_, result) = sigmaValues.[idx]
    sigma_prove (parse formula)
    |> should equal result
    
// limitations.p019
[<Test>]
let ``meson002``() =
    meson002 (parse @"(True(G) <=> ~(|--(G))) /\ Pi(G) /\ (forall p. Sigma(p) ==> (|--(p) <=> True(p))) /\ (forall p. True(Not(p)) <=> ~True(p)) /\  (forall p. Pi(p) ==> Sigma(Not(p))) ==> (|--(Not(G)) <=> |--(G))")
    |> should equal [5; 5]

let private godelValues = [| 
    // limitations.p020  // idx 0
    Imp 
        (And
            (Forall
                ("p",
                Imp
                    (Atom (R ("|--",[Var "p"])),
                    Atom (R ("|--",[Fn ("Pr",[Var "p"])])))),
            And
                (Forall
                    ("p",
                    Forall
                        ("q",
                            Atom
                                (R ("|--",
                                    [Fn
                                        ("imp",
                                        [Fn ("Pr",[Fn ("imp",[Var "p"; Var "q"])]);
                                            Fn
                                                ("imp",
                                                [Fn ("Pr",[Var "p"]); Fn ("Pr",[Var "q"])])])])))),
                Forall
                    ("p",
                        Atom
                            (R ("|--",
                                [Fn
                                    ("imp",
                                    [Fn ("Pr",[Var "p"]);
                                        Fn ("Pr",[Fn ("Pr",[Var "p"])])])]))))),
        Imp
            (And
                (Forall
                    ("p",
                    Forall
                        ("q",
                            Imp
                                (And
                                    (Atom (R ("|--",[Fn ("imp",[Var "p"; Var "q"])])),
                                    Atom (R ("|--",[Var "p"]))),
                                Atom (R ("|--",[Var "q"]))))),
                And
                    (Forall
                        ("p",
                        Forall
                            ("q",
                                Atom
                                    (R ("|--",
                                        [Fn
                                            ("imp",
                                            [Var "q"; Fn ("imp",[Var "p"; Var "q"])])])))),
                    Forall
                        ("p",
                        Forall
                            ("q",
                            Forall
                                ("r",
                                Atom
                                    (R ("|--",
                                        [Fn
                                        ("imp",
                                            [Fn
                                            ("imp",
                                                [Var "p";
                                                Fn ("imp",[Var "q"; Var "r"])]);
                                            Fn
                                            ("imp",
                                                [Fn ("imp",[Var "p"; Var "q"]);
                                                Fn ("imp",[Var "p"; Var "r"])])])]))))))),
            Imp
                (And
                    (Atom
                        (R ("|--",
                            [Fn
                                ("imp",
                                [Var "G";
                                    Fn ("imp",[Fn ("Pr",[Var "G"]); Var "F"])])])),
                    Atom
                        (R ("|--",
                            [Fn
                                ("imp",
                                [Fn ("imp",[Fn ("Pr",[Var "G"]); Var "F"]);
                                    Var "G"])]))),
                Imp
                    (Atom
                    (R ("|--",[Fn ("imp",[Fn ("Pr",[Var "F"]); Var "F"])])),
                    Atom (R ("|--",[Var "F"]))))))
    |]

[<Test>]
// limitations.p020
[<TestCase(0, TestName = "limitations.p020")>]
let ``Godel theorem`` idx =
    let result = godelValues.[idx]
    prove (parse @"(forall p. |--(p) ==> |--(Pr(p))) /\ (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\ (forall p. |--(imp(Pr(p),Pr(Pr(p))))) ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\ (forall p q. |--(imp(q,imp(p,q)))) /\ (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r))))) ==> |--(imp(G,imp(Pr(G),F))) /\ |--(imp(imp(Pr(G),F),G)) ==> |--(imp(Pr(F),F)) ==> |--(F)") 
        [assume
            ["lob1",(parse @"forall p. |--(p) ==> |--(Pr(p))"); 
             "lob2",(parse @"forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))");
             "lob3",(parse @"forall p. |--(imp(Pr(p),Pr(Pr(p))))")]; 
         assume ["logic",(parse @"(forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\ (forall p q. |--(imp(q,imp(p,q)))) /\  (forall p q r. |--(imp(imp(p,imp(q,r)), imp(imp(p,q),imp(p,r)))))")];
         assume ["fix1",(parse @"|--(imp(G,imp(Pr(G),F)))"); 
                 "fix2",(parse @"|--(imp(imp(Pr(G),F),G))")]; 
         assume ["consistency",(parse @"|--(imp(Pr(F),F))")]; 
         have (parse @"|--(Pr(imp(G,imp(Pr(G),F))))") by ["lob1"; "fix1"];
         so have (parse @"|--(imp(Pr(G),Pr(imp(Pr(G),F))))") by ["lob2"; "logic"];
         so have (parse @"|--(imp(Pr(G),imp(Pr(Pr(G)),Pr(F))))") by ["lob2"; "logic"];
         so have (parse @"|--(imp(Pr(G),Pr(F)))") by ["lob3"; "logic"]; 
         so note ("L", (parse @"|--(imp(Pr(G),F))") ) by ["consistency"; "logic"]; 
         so have (parse @"|--(G)") by ["fix2"; "logic"]; 
         so have (parse @"|--(Pr(G))") by ["lob1"; "logic"]; 
         so conclude (parse @"|--(F)") by ["L"; "logic"]; 
         qed]
     |> should equal result
