// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.qelim

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.decidable
open FSharpx.Books.AutomatedReasoning.qelim

open NUnit.Framework
open FsUnit

// pg. 335
//  ------------------------------------------------------------------------- // 
//  Examples.                                                                 // 
//  ------------------------------------------------------------------------- // 

let private qelimValues =  
    [|
        ( // qelim.p001    // idx 0
            @"forall x y. exists z. z < x /\ z < y",
            formula<fol>.True
        );
        ( // qelim.p002    // idx 1
            @"exists z. z < x /\ z < y",
            formula<fol>.True
        );
        ( // qelim.p003    // idx 2
            @"exists z. x < z /\ z < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( // qelim.p004    // idx 3
            @"(forall x. x < a ==> x < b)",
            Not
                (Or
                   (Atom (R ("<",[Var "b"; Var "a"])),
                    Atom (R ("<",[Var "b"; Var "a"]))))
        );
        ( // qelim.p005    // idx 4
            @"forall a b. (forall x. x < a ==> x < b) <=> a <= b",
            formula<fol>.True
        );
        ( // qelim.p006    // idx 5
            @"forall a b. (forall x. x < a <=> x < b) <=> a = b",
            formula<fol>.True
        );
        ( // qelim.p007    // idx 6
            @"exists x y z. forall u.
                    x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)",
            formula<fol>.False
        );
        ( // qelim.p008    // idx 7
            @"forall x. exists y. x < y",
            formula<fol>.True
        );
        ( // qelim.p009    // idx 8
            @"forall x y z. x < y /\ y < z ==> x < z",
            formula<fol>.True
        );
        ( // qelim.p010    // idx 9
            @"forall x y. x < y \/ (x = y) \/ y < x",
            formula<fol>.True
        );
        ( // qelim.p011   // idx 10
            @"exists x y. x < y /\ y < x",
            formula<fol>.False
        );
        ( // qelim.p012   // idx 11
            @"forall x y. exists z. z < x /\ x < y",
            formula<fol>.False
        );
        ( // qelim.p013   // idx 12
            @"exists z. z < x /\ x < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( // qelim.p014   // idx 13
            @"forall x y. exists z. z < x /\ z < y",
            formula<fol>.True
        );
        ( // qelim.p015   // idx 14
            @"forall x y. x < y ==> exists z. x < z /\ z < y",
            formula<fol>.True
        );
        ( // qelim.p016   // idx 15
            @"forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)",
            formula<fol>.True
        );
        ( // qelim.p017   // idx 16
            @"exists x. x = x",
            formula<fol>.True
        );
        ( // qelim.p018   // idx 17
            @"exists x. x = x /\ x = y",
            formula<fol>.True
        );
        ( // qelim.p019   // idx 18
            @"exists z. x < z /\ z < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( // qelim.p020   // idx 19
            @"exists z. x <= z /\ z <= y",
            Or
                (Atom (R ("<",[Var "x"; Var "y"])),
                 Or
                   (Atom (R ("<",[Var "x"; Var "y"])),
                    Or
                      (Atom (R ("<",[Var "x"; Var "y"])),
                       Atom (R ("=",[Var "y"; Var "x"])))))
        );
        ( // qelim.p021   // idx 20
            @"exists z. x < z /\ z <= y",
            Or
                (Atom (R ("<",[Var "x"; Var "y"])),Atom (R ("<",[Var "x"; Var "y"])))
        );
        ( // qelim.p022   // idx 21
            @"forall x y z. exists u. u < x /\ u < y /\ u < z",
            formula<fol>.True
        );
        ( // qelim.p023   // idx 22
            @"forall y. x < y /\ y < z ==> w < z",
            Not
                (And
                   (Atom (R ("<",[Var "x"; Var "z"])),
                    Not (Atom (R ("<",[Var "w"; Var "z"])))))
        );
        ( // qelim.p024   // idx 23
            @"forall x y. x < y",
            formula<fol>.False
        );
        ( // qelim.p025   // idx 24
            @"exists z. z < x /\ x < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( // qelim.p026   // idx 25
            @"forall a b. (forall x. x < a ==> x < b) <=> a <= b",
            formula<fol>.True
        );
        ( // qelim.p027   // idx 26
            @"forall x. x < a ==> x < b",
            Not
                (Or
                   (Atom (R ("<",[Var "b"; Var "a"])),
                    Atom (R ("<",[Var "b"; Var "a"]))))
        );
        ( // qelim.p028   // idx 27
            @"forall x. x < a ==> x <= b",
            Not (Atom (R ("<",[Var "b"; Var "a"])))
        );
        ( // qelim.p029   // idx 28
            @"forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)",
            formula<fol>.True
        );
        ( // qelim.p030   // idx 29
            @"forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)",
            formula<fol>.True
        );
        ( // qelim.p031   // idx 30
            @"forall x y. x <= y \/ x < y",
            formula<fol>.False
        )
    |]

// qelim.p001
[<TestCase(0, TestName = "qelim.p001")>]

// qelim.p002
[<TestCase(1, TestName = "qelim.p002")>]

// qelim.p003
[<TestCase(2, TestName = "qelim.p003")>]

// qelim.p004
[<TestCase(3, TestName = "qelim.p004")>]

// qelim.p005
[<TestCase(4, TestName = "qelim.p005")>]

// qelim.p006
[<TestCase(5, TestName = "qelim.p006")>]

// qelim.p007
[<TestCase(6, TestName = "qelim.p007")>]

// qelim.p008
[<TestCase(7, TestName = "qelim.p008")>]

// qelim.p009
[<TestCase(8, TestName = "qelim.p009")>]

// qelim.p010
[<TestCase(9, TestName = "qelim.p010")>]

// qelim.p011
[<TestCase(10, TestName = "qelim.p011")>]

// qelim.p012
[<TestCase(11, TestName = "qelim.p012")>]

// qelim.p013
[<TestCase(12, TestName = "qelim.p013")>]

// qelim.p014
[<TestCase(13, TestName = "qelim.p014")>]

// qelim.p015
[<TestCase(14, TestName = "qelim.p015")>]

// qelim.p016
[<TestCase(15, TestName = "qelim.p016")>]

// qelim.p017
[<TestCase(16, TestName = "qelim.p017")>]

// qelim.p018
[<TestCase(17, TestName = "qelim.p018")>]

// qelim.p019
[<TestCase(18, TestName = "qelim.p019")>]

// qelim.p020
[<TestCase(19, TestName = "qelim.p020")>]

// qelim.p021
[<TestCase(20, TestName = "qelim.p021")>]

// qelim.p022
[<TestCase(21, TestName = "qelim.p022")>]

// qelim.p023
[<TestCase(22, TestName = "qelim.p023")>]

// qelim.p024
[<TestCase(23, TestName = "qelim.p024")>]

// qelim.p025
[<TestCase(24, TestName = "qelim.p025")>]

// qelim.p026
[<TestCase(25, TestName = "qelim.p026")>]

// qelim.p027
[<TestCase(26, TestName = "qelim.p027")>]

// qelim.p028
[<TestCase(27, TestName = "qelim.p028")>]

// qelim.p029
[<TestCase(28, TestName = "qelim.p029")>]

// qelim.p030
[<TestCase(29, TestName = "qelim.p030")>]

// qelim.p031
[<TestCase(30, TestName = "qelim.p031")>]

let ``quelim_dlo`` idx =
    let (input, _) = qelimValues.[idx]
    let (_, result) = qelimValues.[idx]
    quelim_dlo (parse input)
    |> should equal result

