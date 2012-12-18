// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.combining

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.cong
open FSharpx.Books.AutomatedReasoning.cooper
open FSharpx.Books.AutomatedReasoning.real
open FSharpx.Books.AutomatedReasoning.combining

open NUnit.Framework
open FsUnit

let private nelopValues : (((string * int -> bool) * (string * int -> bool) * (formula<fol> -> bool)) list * string * bool)[] = [| 
    (
        // idx 0
        // combining.p003
        (add_default [int_lang]),
        @"f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v 
            ==> false",
        true
    );
    (
        // idx 1
        // combining.p005
        (add_default [int_lang]),
        @"y <= x /\ y >= x + z /\ z >= 0 
            ==> f(f(x) - f(y)) = f(z)",
        true
    );
    (
        // idx 2
        // combining.p006
        (add_default [int_lang]),
        @"x = y /\ y >= z /\ z >= x 
            ==> f(z) = f(x)",
        true
    );
    (
        // idx 3
        // combining.p007
        (add_default [int_lang]),
        @"a <= b /\ b <= f(a) /\ f(a) <= 1 
            ==> a + b <= 1 \/ b + f(b) <= 1 \/ f(f(b)) <= f(a)",
        true
    );
    (
        // idx 4
        // combining.p010
        (add_default [int_lang]),
        @"f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v 
            ==> false",
        true
    );
    (
        // idx 5
        // combining.p011
        (add_default [int_lang]),
        @"f(v) = v /\ f(u) = u - 1 /\ u = v 
            ==> false",
        true
    );
    (
        // idx 6
        // combining.p012
        (add_default [int_lang]),
        @"z = f(x - y) /\ x = z + y /\ ~(-(y) = -(x - f(f(z)))) 
            ==> false",
        true
    );
    (
        // idx 7
        // combining.p013
        (add_default [int_lang]),
        @"a + 2 = b 
            ==> f(read(update(A,a,3),b-2)) = f(b - a + 1)",
        false
    );
    (
        // idx 8
        // combining.p014
        (add_default [int_lang]),
        @"(x = y /\ z = 1 
            ==> f(f((x+z))) = f(f((1+y))))",
        true
    );
    (
        // idx 9
        // combining.p015
        (add_default [int_lang]),
        @"hd(x) = hd(y) /\ tl(x) = tl(y) /\ ~(x = nil) /\ ~(y = nil) 
            ==> f(x) = f(y)",
        false
    );
    (
        // idx 10
        // combining.p016
        (add_default [int_lang]),
        @"~(f(f(x) - f(y)) = f(z)) /\ y <= x /\ y >= x + z /\ z >= 0 
            ==> false",
        true
    );
    (
        // idx 11
        // combining.p017
        (add_default [int_lang]),
        @"x < f(y) + 1 /\ f(y) <= x 
            ==> (P(x,y) <=> P(f(y),y))",
        false  // Dummy value used as place holder
    );
    (
        // idx 12
        // combining.p018
        (add_default [int_lang]),
        @"(x >= y ==> MAX(x,y) = x) /\ (y >= x ==> MAX(x,y) = y) 
            ==> x = y + 2 ==> MAX(x,y) = x",
        true
    );
    (
        // idx 13
        // combining.p019
        (add_default [int_lang]),
        @"x <= g(x) /\ x >= g(x) 
            ==> x = g(g(g(g(x))))",
        true
    );
    (
        // idx 14
        // combining.p020
        (add_default [real_lang]),
        @"x^2 =  1 ==> (f(x) = f(-(x))) 
            ==> (f(x) = f(1))",
        true
    );
    (
        // idx 15
        // combining.p021
        (add_default [int_lang]),
        @"2 * f(x + y) = 3 * y /\ 2 * x = y 
            ==> f(f(x + y)) = 3 * x",
        true
    );
    (
        // idx 16
        // combining.p022
        (add_default [real_lang]),
        @"x^2 = y^2 /\ x < y /\ z^2 = z /\ x < x * z /\ P(f(1 + z)) 
            ==> P(f(x + y) - f(0))",
        false  // Dummy value used as place holder
    );
    (
        // idx 17
        // combining.p023
        (add_default [int_lang]),
        @"4 * x = 2 * x + 2 * y /\ x = f(2 * x - y) /\ f(2 * y - x) = 3 /\ f(x) = 4 
            ==> false",
        true
    );
    |]
    
[<TestCase(0, TestName = "combining.p003")>]
[<TestCase(1, TestName = "combining.p005")>]
[<TestCase(2, TestName = "combining.p006")>]
[<TestCase(3, TestName = "combining.p007")>]
[<TestCase(4, TestName = "combining.p010")>]
[<TestCase(5, TestName = "combining.p011")>]
[<TestCase(6, TestName = "combining.p012")>]
[<TestCase(7, TestName = "combining.p013")>]
[<TestCase(8, TestName = "combining.p014")>]
[<TestCase(9, TestName = "combining.p015")>]
[<TestCase(10, TestName = "combining.p016")>]
[<TestCase(11, TestName = "combining.p017", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(12, TestName = "combining.p018")>]
[<TestCase(13, TestName = "combining.p019")>]
[<TestCase(14, TestName = "combining.p020")>]
[<TestCase(15, TestName = "combining.p021")>]
[<TestCase(16, TestName = "combining.p022", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(17, TestName = "combining.p023")>]

[<Test>]
let ``nelop tests`` idx = 
    let (langs, _, _) = nelopValues.[idx]
    let (_, formula, _) = nelopValues.[idx]
    let (_, _, result) = nelopValues.[idx]
    nelop langs (parse formula)
    |> should equal result

// combining.p001
[<Test>]
let ``combining.p001``() = 
    (integer_qelim << generalize) (parse
        @"(u + 1 = v /\ v_1 + 1 = u - 1 /\ v_2 - 1 = v + 1 /\ v_3 = v - 1) ==> u = v_3 /\ ~(v_1 = v_2)")
    |> should equal formula<fol>.True

// combining.p002
[<Test>]
let ``combining.p002``() = 
    ccvalid (parse
        @"(v_2 = f(v_3) /\ v_1 = f(u)) ==> ~(u = v_3 /\ ~(v_1 = v_2))")
    |> should be True
      
// combining.p003  
[<Test>]
let ``combining.p003``() =
    nelop001 (add_default [int_lang]) (parse
        @"f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false")
    |> should be True

// combining.p004
[<Test>]
let ``combining.p004``() =
    let bell n = List.length (allpartitions (1 -- n))
    List.map bell (1 -- 10)
    |> should equal [1; 2; 5; 15; 52; 203; 877; 4140; 21147; 115975]

// combining.p008
[<Test>]
let ``combining.p008``() = 
    List.map (real_qelim << generalize) [
        parse @"x * y = 0 /\ z = 0 ==> x = z \/ y = z";
        parse @"x * y = 0 /\ z = 0 ==> x = z";
        parse @"x * y = 0 /\ z = 0 ==> y = z"; ]
    |> should equal [formula<fol>.True; formula<fol>.False; formula<fol>.False]

// combining.p009
[<Test>]
let ``combining.p009``() = 
    List.map (integer_qelim << generalize) [
        parse @"0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y \/ x = z";
        parse @"0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y";
        parse @"0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = z"; ]
    |> should equal [formula<fol>.True; formula<fol>.False; formula<fol>.False]
