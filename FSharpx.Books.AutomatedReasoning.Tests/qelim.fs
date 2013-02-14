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
        ( 
            // idx 0
            // qelim.p001    
            @"forall x y. exists z. z < x /\ z < y",
            formula<fol>.True
        );
        ( 
            // idx 1
            // qelim.p002    
            @"exists z. z < x /\ z < y",
            formula<fol>.True
        );
        ( 
            // idx 2
            // qelim.p003    
            @"exists z. x < z /\ z < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( 
            // idx 3
            // qelim.p004    
            @"(forall x. x < a ==> x < b)",
            Not
                (Or
                   (Atom (R ("<",[Var "b"; Var "a"])),
                    Atom (R ("<",[Var "b"; Var "a"]))))
        );
        ( 
            // idx 4
            // qelim.p005    
            @"forall a b. (forall x. x < a ==> x < b) <=> a <= b",
            formula<fol>.True
        );
        ( 
            // idx 5
            // qelim.p006    
            @"forall a b. (forall x. x < a <=> x < b) <=> a = b",
            formula<fol>.True
        );
        ( 
            // idx 6
            // qelim.p007    
            @"exists x y z. forall u.
                    x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)",
            formula<fol>.False
        );
        ( 
            // idx 7
            // qelim.p008    
            @"forall x. exists y. x < y",
            formula<fol>.True
        );
        ( 
            // idx 8
            // qelim.p009    
            @"forall x y z. x < y /\ y < z ==> x < z",
            formula<fol>.True
        );
        ( 
            // idx 9
            // qelim.p010    
            @"forall x y. x < y \/ (x = y) \/ y < x",
            formula<fol>.True
        );
        ( 
            // idx 10
            // qelim.p011   
            @"exists x y. x < y /\ y < x",
            formula<fol>.False
        );
        ( 
            // idx 11
            // qelim.p012   
            @"forall x y. exists z. z < x /\ x < y",
            formula<fol>.False
        );
        ( 
            // idx 12
            // qelim.p013   
            @"exists z. z < x /\ x < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( 
            // idx 13
            // qelim.p014   
            @"forall x y. exists z. z < x /\ z < y",
            formula<fol>.True
        );
        ( 
            // idx 14
            // qelim.p015   
            @"forall x y. x < y ==> exists z. x < z /\ z < y",
            formula<fol>.True
        );
        ( 
            // idx 15
            // qelim.p016   
            @"forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)",
            formula<fol>.True
        );
        ( 
            // idx 16
            // qelim.p017   
            @"exists x. x = x",
            formula<fol>.True
        );
        ( 
            // idx 17
            // qelim.p018   
            @"exists x. x = x /\ x = y",
            formula<fol>.True
        );
        ( 
            // idx 18
            // qelim.p019   
            @"exists z. x < z /\ z < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( 
            // idx 19
            // qelim.p020   
            @"exists z. x <= z /\ z <= y",
            Or
                (Atom (R ("<",[Var "x"; Var "y"])),
                 Or
                   (Atom (R ("<",[Var "x"; Var "y"])),
                    Or
                      (Atom (R ("<",[Var "x"; Var "y"])),
                       Atom (R ("=",[Var "y"; Var "x"])))))
        );
        ( 
            // idx 20
            // qelim.p021   
            @"exists z. x < z /\ z <= y",
            Or
                (Atom (R ("<",[Var "x"; Var "y"])),Atom (R ("<",[Var "x"; Var "y"])))
        );
        ( 
            // idx 21
            // qelim.p022   
            @"forall x y z. exists u. u < x /\ u < y /\ u < z",
            formula<fol>.True
        );
        ( 
            // idx 22
            // qelim.p023   
            @"forall y. x < y /\ y < z ==> w < z",
            Not
                (And
                   (Atom (R ("<",[Var "x"; Var "z"])),
                    Not (Atom (R ("<",[Var "w"; Var "z"])))))
        );
        ( 
            // idx 23
            // qelim.p024   
            @"forall x y. x < y",
            formula<fol>.False
        );
        ( 
            // idx 24
            // qelim.p025   
            @"exists z. z < x /\ x < y",
            Atom (R ("<",[Var "x"; Var "y"]))
        );
        ( 
            // idx 25
            // qelim.p026   
            @"forall a b. (forall x. x < a ==> x < b) <=> a <= b",
            formula<fol>.True
        );
        ( 
            // idx 26
            // qelim.p027   
            @"forall x. x < a ==> x < b",
            Not
                (Or
                   (Atom (R ("<",[Var "b"; Var "a"])),
                    Atom (R ("<",[Var "b"; Var "a"]))))
        );
        ( 
            // idx 27
            // qelim.p028   
            @"forall x. x < a ==> x <= b",
            Not (Atom (R ("<",[Var "b"; Var "a"])))
        );
        ( 
            // idx 28
            // qelim.p029   
            @"forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)",
            formula<fol>.True
        );
        ( 
            // idx 29
            // qelim.p030   
            @"forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)",
            formula<fol>.True
        );
        (    
            // idx 30
            // qelim.p031  
            @"forall x y. x <= y \/ x < y",
            formula<fol>.False
        )
    |]

[<Test>]
[<TestCase(0, TestName = "qelim.p001")>]
[<TestCase(1, TestName = "qelim.p002")>]
[<TestCase(2, TestName = "qelim.p003")>]
[<TestCase(3, TestName = "qelim.p004")>]
[<TestCase(4, TestName = "qelim.p005")>]
[<TestCase(5, TestName = "qelim.p006")>]
[<TestCase(6, TestName = "qelim.p007")>]
[<TestCase(7, TestName = "qelim.p008")>]
[<TestCase(8, TestName = "qelim.p009")>]
[<TestCase(9, TestName = "qelim.p010")>]
[<TestCase(10, TestName = "qelim.p011")>]
[<TestCase(11, TestName = "qelim.p012")>]
[<TestCase(12, TestName = "qelim.p013")>]
[<TestCase(13, TestName = "qelim.p014")>]
[<TestCase(14, TestName = "qelim.p015")>]
[<TestCase(15, TestName = "qelim.p016")>]
[<TestCase(16, TestName = "qelim.p017")>]
[<TestCase(17, TestName = "qelim.p018")>]
[<TestCase(18, TestName = "qelim.p019")>]
[<TestCase(19, TestName = "qelim.p020")>]
[<TestCase(20, TestName = "qelim.p021")>]
[<TestCase(21, TestName = "qelim.p022")>]
[<TestCase(22, TestName = "qelim.p023")>]
[<TestCase(23, TestName = "qelim.p024")>]
[<TestCase(24, TestName = "qelim.p025")>]
[<TestCase(25, TestName = "qelim.p026")>]
[<TestCase(26, TestName = "qelim.p027")>]
[<TestCase(27, TestName = "qelim.p028")>]
[<TestCase(28, TestName = "qelim.p029")>]
[<TestCase(29, TestName = "qelim.p030")>]
[<TestCase(30, TestName = "qelim.p031")>]
let ``quelim_dlo`` idx =
    let (input, _) = qelimValues.[idx]
    let (_, result) = qelimValues.[idx]
    quelim_dlo (parse input)
    |> should equal result
