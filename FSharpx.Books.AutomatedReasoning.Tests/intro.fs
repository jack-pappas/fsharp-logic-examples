// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.intro

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro

open NUnit.Framework
open FsUnit

let private simplifyValues : (expression * expression)[] = [| 
    (
        // idx 0
        // intro.p002
        (Add (Mul (Add (Mul (Const 0, Var "x"), Const 1), Const 3), Const 12)),
        (Const 15)
    );
    |]

[<Test>]
[<TestCase(0, TestName = "intro.p002")>]
let ``simplify tests`` idx = 
    let (expr, _) = simplifyValues.[idx]
    let (_, result) = simplifyValues.[idx]
    simplify expr
    |> should equal result

let private lexValues : (string * string list)[] = [| 
    (
        // idx 0
        // intro.p003
        @"2*((var_1 + x') + 11)",
        ["2"; "*"; "("; "("; "var_1"; "+"; "x'"; ")"; "+"; "11"; ")"]
    );
    (
        // idx 1
        // intro.p004
        @"if //p1-- == *p2++) then f() else g()",
        ["if"; "//"; "p1"; "--"; "=="; "*"; "p2"; "++"; ")"; "then"; "f"; "("; ")"; "else"; "g"; "("; ")"]
    );
    |]

[<Test>]
[<TestCase(0, TestName = "intro.p003")>]
[<TestCase(1, TestName = "intro.p004")>]
let ``lex tests`` idx = 
    let (text, _) = lexValues.[idx]
    let (_, result) = lexValues.[idx]
    lex (explode text)
    |> should equal result

let private parse_expValues : (string * expression)[] = [| 
    (
        // idx 0
        // intro.p005
        @"x + 1",
        (Add (Var "x",Const 1))
    );
    (
        // idx 1
        // intro.p006
        @"(x1 + x2 + x3) * (1 + 2 + 3 * x + y)",
        (Mul (Add (Var "x1",Add (Var "x2",Var "x3")), 
            Add (Const 1,Add (Const 2,Add (Mul (Const 3,Var "x"),Var "y")))))
    );
    (
        // idx 2
        // intro.p008
        @"x + 3 * y",
        Add (Var "x",Mul (Const 3,Var "y"))
    );
    (
        // idx 3
        // intro.p009
        @"(x + 3) * y",
        Mul (Add (Var "x",Const 3),Var "y")
    );
    (
        // idx 4
        // intro.p010
        @"1 + 2 + 3",
        Add (Const 1,Add (Const 2,Const 3))
    );
    (
        // idx 5
        // intro.p011
        @"((1 + 2) + 3) + 4",
        Add (Add (Add (Const 1,Const 2),Const 3),Const 4)
    );
    (
        // idx 6
        // intro.p012
        @"(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)",
        Mul (Add (Var "x1", Add (Var "x2", Add (Var "x3", Add (Var "x4", Add (Var "x5", Add (Var "x6", Add (Var "x7",Add (Var "x8",Add (Var "x9",Var "x10"))))))))), 
            Add (Var "y1", Add (Var "y2", Add (Var "y3", Add (Var "y4", Add (Var "y5", Add (Var "y6", Add (Var "y7",Add (Var "y8",Add (Var "y9",Var "y10"))))))))))
    );
    |]

[<Test>]
[<TestCase(0, TestName = "intro.p005")>]
[<TestCase(1, TestName = "intro.p006")>]
[<TestCase(2, TestName = "intro.p008")>]
[<TestCase(3, TestName = "intro.p009")>]
[<TestCase(4, TestName = "intro.p010")>]
[<TestCase(5, TestName = "intro.p011")>]
[<TestCase(6, TestName = "intro.p012")>]
let ``parse_exp tests`` idx = 
    let (text, _) = parse_expValues.[idx]
    let (_, result) = parse_expValues.[idx]
    parse_exp text
    |> should equal result

let private string_of_expValues : (string * string)[] = [| 
    (
        // idx 0
        // intro.p007
        "x + 3 * y",
        "(x + (3 * y))"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "intro.p007")>]
let ``string_of_exp tests`` idx = 
    let (text, _) = string_of_expValues.[idx]
    let (_, result) = string_of_expValues.[idx]
    string_of_exp (parse_exp text)
    |> should equal result