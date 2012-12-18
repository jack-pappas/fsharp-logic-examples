// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.grobner

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.complex
open FSharpx.Books.AutomatedReasoning.grobner

open NUnit.Framework
open FsUnit

let private grobner_decideValues : (string * bool)[] = [| 
    (
        // idx 0
        // grobner.p001
        // grobner.p005
        @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0",
        true
    ); 
    (
        // idx 1
        // grobner.p002
        // grobner.p006
        @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0",
        false
    );
    (
        // idx 2
        // grobner.p003
        // grobner.p007
        // grobner #1
        @"(a * x^2 + b * x + c = 0) /\
        (a * y^2 + b * y + c = 0) /\
        ~(x = y)
        ==> (a * x * y = c) /\ (a * (x + y) + b = 0)",
        true
    );
    (
        // idx 3
        // grobner.p008
        @"(y_1 = 2 * y_3) /\
        (y_2 = 2 * y_4) /\
        (y_1 * y_3 = y_2 * y_4)
        ==> (y_1^2 = y_2^2)",
        true
    );
    (
        // idx 4
        // grobner.p009
        @"(x1 = u3) /\
        (x1 * (u2 - u1) = x2 * u3) /\
        (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
        (x3 * u3 = x4 * u2) /\
        ~(u1 = 0) /\
        ~(u3 = 0)
        ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)",
        true
    );
    (
        // idx 5
        // grobner.p010
        @"(u1 * x1 - u1 * u3 = 0) /\
        (u3 * x2 - (u2 - u1) * x1 = 0) /\
        (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
        (u3 * x4 - u2 * x3 = 0) /\
        ~(u1 = 0) /\
        ~(u3 = 0)
        ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)",
        true
    );
    (
        // idx 6
        // grobner.p011
        @"a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0 
        ==> 4*a^2*c-b^2*a = 0",
        true
    );
    (
        // idx 7
        // grobner.p012
        @"a * x^2 + b * x + c = 0 /\ d * x + e = 0 
        ==> d^2*c-e*d*b+a*e^2 = 0",
        true
    );
    (
        // idx 8
        // grobner.p013
        @"a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0
        ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0",
        true
    );
    (
        // idx 9
        // grobner.p014
        @"a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0
            ==>
            e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
            g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0",
        false
    );
    (
        // idx 10
        // grobner.p015
        @"(x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2
        ==> x0 = x0' /\ y0 = y0'",
        false
    );
    (
        // idx 11
        // grobner.p016
        @"(x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2 /\
        ~((x1 - x0)^2 + (y1 - y0)^2 = 0) /\
        ~((x1 - x0')^2 + (y1 - y0')^2 = 0)
        ==> x0 = x0' /\ y0 = y0'",
        false
    );
    (
        // idx 12
        // grobner.p017
        @"(x1 - x0)^2 + (y1 - y0)^2 = d /\
        (x2 - x0)^2 + (y2 - y0)^2 = d /\
        (x3 - x0)^2 + (y3 - y0)^2 = d /\
        (x1 - x0')^2 + (y1 - y0')^2 = e /\
        (x2 - x0')^2 + (y2 - y0')^2 = e /\
        (x3 - x0')^2 + (y3 - y0')^2 = e /\
        ~(d = 0) /\ ~(e = 0)
        ==> x0 = x0' /\ y0 = y0'",
        false
    );
    (
        // idx 13
        // grobner.p018
        @"y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y",
        true
    );
    (
        // idx 14
        // grobner.p020
        @"a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
        ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 = 0",
        true
    );
    (
        // idx 15
        // grobner.p022
        @"b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
        ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0",
        true
    );
    (
        // idx 16
        // grobner.p023
        @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
        ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0",
        true
    );
    (
        // idx 17
        // grobner.p024
        @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
        ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)",
        true
    );
    (
        // idx 18
        // grobner.p025
        @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
        ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3",
        true
    );
    (
        // idx 19
        // grobner.p026
        @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 
        ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0",
        true
    );
    (
        // idx 20
        // grobner.p027
        @"(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0",
        true
    );
    (
        // idx 21
        // grobner.p028
        @"t - u = n /\ 27 * t * u = m^3 /\
        ct^3 = t /\ cu^3 = u /\
        x = ct - cu
        ==> x^3 + m * x = n",
        false
    );
    |]

[<TestCase(0, TestName = "grobner.p001")>]
[<TestCase(1, TestName = "grobner.p002")>]
[<TestCase(2, TestName = "grobner.p003")>]
[<TestCase(3, TestName = "grobner.p008")>]
[<TestCase(4, TestName = "grobner.p009")>]
[<TestCase(5, TestName = "grobner.p010")>]
[<TestCase(6, TestName = "grobner.p011")>]
[<TestCase(7, TestName = "grobner.p012")>]
[<TestCase(8, TestName = "grobner.p013")>]
[<TestCase(9, TestName = "grobner.p014", Category = "LongRunning")>]
[<TestCase(10, TestName = "grobner.p015", Category = "LongRunning")>]
[<TestCase(11, TestName = "grobner.p016", Category = "LongRunning")>]
[<TestCase(12, TestName = "grobner.p017", Category = "LongRunning")>]
[<TestCase(13, TestName = "grobner.p018")>]
[<TestCase(14, TestName = "grobner.p020")>]
[<TestCase(15, TestName = "grobner.p022")>]
[<TestCase(16, TestName = "grobner.p023")>]
[<TestCase(17, TestName = "grobner.p024")>]
[<TestCase(18, TestName = "grobner.p025")>]
[<TestCase(19, TestName = "grobner.p026")>]
[<TestCase(20, TestName = "grobner.p027")>]
[<TestCase(21, TestName = "grobner.p028")>]

[<Test>]
let ``grobner_decide tests`` idx = 
    let (formula, _) = grobner_decideValues.[idx]
    let (_, result) = grobner_decideValues.[idx]
    grobner_decide (parse formula)
    |> should equal result

let complex_qelimValues : (formula<fol> * formula<fol>)[] = [|
    (
        // idx 
        // grobner.p004
        // grobner #1
        generalize (parse @"(a * x^2 + b * x + c = 0) /\
        (a * y^2 + b * y + c = 0) /\
        ~(x = y)
        ==> (a * x * y = c) /\ (a * (x + y) + b = 0)"),
        formula<fol>.True
    );
    (
        // idx 
        // grobner.p019
        parse @"forall a b c d e.
            a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
            ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 = 0",
        formula<fol>.True
    );
    (
        // idx 
        // grobner.p021
        parse @"forall b d e.
            b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
            ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0",
        formula<fol>.True
    );
    |]

[<TestCase(0, TestName = "grobner.p004")>]
[<TestCase(1, TestName = "grobner.p019")>]
[<TestCase(2, TestName = "grobner.p021")>]

[<Test>]
let ``complex_qelim tests`` idx = 
    let (formula, _) = complex_qelimValues.[idx]
    let (_, result) = complex_qelimValues.[idx]
    complex_qelim formula
    |> should equal result
