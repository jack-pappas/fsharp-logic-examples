// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.skolem

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.prolog
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.skolem
    
open NUnit.Framework
open FsUnit

let private simplifyValues : (string * formula<fol> * string)[] = [|
    (
        // idx 0
        // skolem.p001
        @"(forall x y. P(x) \/ (P(y) /\ false)) 
            ==> exists z. Q",
        Imp (Forall ("x",Atom (R ("P",[Var "x"]))),Atom (R ("Q",[]))),
        @"<<(forall x. P(x)) ==> Q>>"
    )
    |]

[<Test>]
[<TestCase(0, TestName = "skolem.p001")>]
let ``simplify tests`` idx =
    let (formula, _, _) = simplifyValues.[idx]
    let (_, astResult, _) = simplifyValues.[idx]
    let (_, _, stringResult) = simplifyValues.[idx]
    let result = simplify (parse formula)
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult
    

let private nnfValues : (string * formula<fol> * string)[] = [|
    (
        // idx 0
        // skolem.p002
        @"(forall x. P(x)) 
            ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))",
        Or
          (Exists ("x",Not (Atom (R ("P",[Var "x"])))),
           Or
             (And
                (Exists ("y",Atom (R ("Q",[Var "y"]))),
                 Exists
                   ("z",
                    And (Atom (R ("P",[Var "z"])),Atom (R ("Q",[Var "z"]))))),
              And
                (Forall ("y",Not (Atom (R ("Q",[Var "y"])))),
                 Forall
                   ("z",
                    Or
                      (Not (Atom (R ("P",[Var "z"]))),
                       Not (Atom (R ("Q",[Var "z"])))))))),
        @"<<(exists x. ~P(x)) \/ (exists y. Q(y)) /\ (exists z. P(z) /\ Q(z)) \/ (forall y. ~Q(y)) /\ (forall z. ~P(z) \/ ~Q(z))>>"
    )
    |]

[<Test>]
[<TestCase(0, TestName = "skolem.p002")>]
let ``nnf tests`` idx =
    let (formula, _, _) = nnfValues.[idx]
    let (_, astResult, _) = nnfValues.[idx]
    let (_, _, stringResult) = nnfValues.[idx]
    let result = nnf (parse formula)
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult
    

let private pnfValues : (string * formula<fol> * string)[] = [|
    (
        // idx 0
        // skolem.p003
        @"(forall x. P(x) \/ R(y)) 
            ==> exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z))",
        Exists
          ("x",
           Forall
             ("z",
              Or
                (And
                   (Not (Atom (R ("P",[Var "x"]))),
                    Not (Atom (R ("R",[Var "y"])))),
                 Or
                   (Atom (R ("Q",[Var "x"])),
                    Or
                      (Not (Atom (R ("P",[Var "z"]))),
                       Not (Atom (R ("Q",[Var "z"])))))))),
        @"<<exists x. forall z. ~P(x) /\ ~R(y) \/ Q(x) \/ ~P(z) \/ ~Q(z)>>"
    )
    |]

[<Test>]
[<TestCase(0, TestName = "skolem.p003")>]
let ``pnf tests`` idx =
    let (formula, _, _) = pnfValues.[idx]
    let (_, astResult, _) = pnfValues.[idx]
    let (_, _, stringResult) = pnfValues.[idx]
    let result = pnf (parse formula)
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult
    
let private skolemizeValues : (string * formula<fol> * string)[] = [|
    (
        // idx 0
        // skolem.p004
        @"exists y. x < y 
            ==> forall u. exists v. x * u < y * v",
        Or
          (Not (Atom (R ("<",[Var "x"; Fn ("f_y",[Var "x"])]))),
           Atom
             (R ("<",
                 [Fn ("*",[Var "x"; Var "u"]);
                  Fn
                    ("*",[Fn ("f_y",[Var "x"]); Fn ("f_v",[Var "u"; Var "x"])])]))),
        @"<<~x <f_y(x) \/ x *u <f_y(x) *f_v(u,x)>>"
    )
    (
        // idx 1
        // skolem.p005
        @"forall x. P(x)
                 ==> (exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z)))",
        Or
          (Not (Atom (R ("P",[Var "x"]))),
           Or
             (Atom (R ("Q",[Fn ("c_y",[])])),
              Or
                (Not (Atom (R ("P",[Var "z"]))),Not (Atom (R ("Q",[Var "z"])))))),
        @"<<~P(x) \/ Q(c_y) \/ ~P(z) \/ ~Q(z)>>"
    )
    |]

[<Test>]
[<TestCase(0, TestName = "skolem.p004")>]
[<TestCase(1, TestName = "skolem.p005")>]
let ``skolemize tests`` idx =
    let (formula, _, _) = skolemizeValues.[idx]
    let (_, astResult, _) = skolemizeValues.[idx]
    let (_, _, stringResult) = skolemizeValues.[idx]
    let result = skolemize (parse formula)
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult
