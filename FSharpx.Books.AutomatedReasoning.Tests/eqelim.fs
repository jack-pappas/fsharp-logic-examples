// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.eqelim

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.eqelim

open NUnit.Framework
open FsUnit

let private meson002Values : (string * int list)[] = [| 
    (
        // idx 0
        // eqelim.p001
        @"(forall x. P(1,x,x)) /\ 
              (forall x. P(x,x,1)) /\ 
              (forall u v w x y z. P(x,y,u) /\ 
              P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
                  ==> forall a b c. P(a,b,c) 
              ==> P(b,a,c)",
        [13]
    );
    (
        // idx 1
        // eqelim.p002
        @"(forall x. R(x,x)) /\ 
        (forall x y. R(x,y) ==>  R(y,x)) /\ 
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
        <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z)))",
        [4; 3; 9; 3; 2; 7]
    );
    (
        // idx 2
        // eqelim.p016
        @"(forall x. P(1,x,x)) /\ 
        (forall x. P(i(x),x,1)) /\ 
        (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
        ==> forall x. P(x,1,x)",
        [10]
    );
    (
        // idx 3
        // eqelim.p017
        @"(forall x. P(1,x,x)) /\ 
        (forall x. P(i(x),x,1)) /\ 
        (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
        ==> forall x. P(x,i(x),1)",
        [7]
    );
    (
        // idx 4
        // eqelim.p018
        @"(forall x. P(1,x,x)) /\ 
        (forall x. P(x,x,1)) /\ 
        (forall x y. exists z. P(x,y,z)) /\ 
        (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
        ==> forall a b c. P(a,b,c) ==> P(b,a,c)",
        [13]
    );
    (
        // idx 5
        // eqelim.p019
        @"(forall x. R(x,x)) /\ 
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) 
        <=> (forall x y. R(x,y) <=> (forall z. R(y,z) ==> R(x,z)))",
        [3; 3; 2; 3]
    );
    (
        // idx 6
        // eqelim.p020
        @"(forall x y. R(x,y) ==>  R(y,x)) <=> 
        (forall x y. R(x,y) <=> R(x,y) /\ R(y,x))",
        [2; 2]
    );
    (
        // idx 7
        // eqelim.p021
        @"(forall x. (forall w. R'(x,w) <=> R'(x,w))) /\ 
        (forall x y. (forall w. R'(x,w) <=> R'(y,w)) 
            ==> (forall w. R'(y,w) <=> R'(x,w))) /\ 
        (forall x y z. (forall w. R'(x,w) <=> R'(y,w)) /\ 
            (forall w. R'(y,w) <=> R'(z,w)) 
                ==> (forall w. R'(x,w) <=> R'(z,w)))",
        [2; 3; 2; 3]
    );
    (
        // idx 8
        // eqelim.p022
        @"(forall x y. R(x,y) <=> (forall z. R'(x,z) <=> R'(y,z))) /\ 
        (forall x. R'(x,x)) 
        ==> forall x y. ~R'(x,y) ==> ~R(x,y)",
        [3]
    );
    (
        // idx 9
        // eqelim.p023
        @"(forall x y. R(x,y) <=> (forall z. R'(y,z) ==> R'(x,z))) /\ 
        (forall x. R'(x,x)) 
        ==> forall x y. ~R'(x,y) ==> ~R(x,y)",
        [3]
    );
    (
        // idx 10
        // eqelim.p024
        @"(forall x y. R(x,y) <=> R'(x,y) /\ R'(y,x)) 
        ==> forall x y. ~R'(x,y) ==> ~R(x,y)",
        [2]
    );
    |]

[<TestCase(0, TestName = "eqelim.p001")>]
[<TestCase(1, TestName = "eqelim.p002")>]
[<TestCase(2, TestName = "eqelim.p016")>]
[<TestCase(3, TestName = "eqelim.p017")>]
[<TestCase(4, TestName = "eqelim.p018", Category = "LongRunning")>]
[<TestCase(5, TestName = "eqelim.p019")>]
[<TestCase(6, TestName = "eqelim.p020")>]
[<TestCase(7, TestName = "eqelim.p021")>]
[<TestCase(8, TestName = "eqelim.p022")>]
[<TestCase(9, TestName = "eqelim.p023")>]
[<TestCase(10, TestName = "eqelim.p024")>]

[<Test>]
let ``meson002 tests`` idx = 
    let (formula, _) = meson002Values.[idx]
    let (_, result) = meson002Values.[idx]
    meson002 (parse formula)
    |> should equal result

let private bmesonValues : (string * int list)[] = [| 
    (
        // idx 0
        // eqelim.p003
        // eqelim.p008
        // Wishnu #1
        @"(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
        (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')",
        [25; 25]
    );
    (
        // idx 1
        // eqelim.p005
        @"(forall x y z. x * (y * z) = (x * y) * z) /\ 
        (forall x. e * x = x) /\ 
        (forall x. i(x) * x = e)                                
        ==> forall x. x * i(x) = e",
        [19]
    );
    (
        // idx 2
        // eqelim.p006
        // Dijkstra 1266a
        @"(forall x. f(x) ==> g(x)) /\ 
        (exists x. f(x)) /\ 
        (forall x y. g(x) /\ g(y) ==> x = y) 
        ==> forall y. g(y) ==> f(y)",
        [9]
    );
    (
        // idx 3
        // eqelim.p010
        @"(forall x y z. x * (y * z) = (x * y) * z) /\ 
        (forall x. e * x = x) /\ 
        (forall x. i(x) * x = e) 
        ==> forall x. x * e = x",
        [17]
    );
    (
        // idx 4
        // eqelim.p012
        @"(forall x y z. x * (y * z) = (x * y) * z) /\ 
        (forall x. e * x = x) /\ 
        (forall x. i(x) * x = e) 
        ==> forall x. x * i(x) = e",
        []
    );
    (
        // idx 5
        // eqelim.p014
        @"(forall x y z. x * (y * z) = (x * y) * z) /\ p * q * p = p 
        ==> exists q'. p * q' * p = p /\ q' * p * q' = q'",
        []
    );
    |]

[<TestCase(0, TestName = "eqelim.p003", Category = "LongRunning")>]
[<TestCase(1, TestName = "eqelim.p005", Category = "LongRunning")>]
[<TestCase(2, TestName = "eqelim.p006")>]
[<TestCase(3, TestName = "eqelim.p010", Category = "LongRunning")>]
[<TestCase(4, TestName = "eqelim.p012", Category = "LongRunning")>]
[<TestCase(5, TestName = "eqelim.p014", Category = "LongRunning")>]

[<Test>]
let ``bmeson tests`` idx = 
    let (formula, _) = bmesonValues.[idx]
    let (_, result) = bmesonValues.[idx]
    let result1 = bmeson (parse formula)
    printfn "%A" result1
    result1
    |> should equal result

let private emesonValues : (string * int list)[] = [| 
    (
        // idx 0
        // eqelim.p004
        // eqelim.p009
        // Wishnu #1
        @"(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
        (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')",
        [16; 16]
    )
    (
        // idx 1
        // eqelim.p007
        // Dijkstra 1266a
        @"        (forall x. f(x) ==> g(x)) /\ 
        (exists x. f(x)) /\ 
        (forall x y. g(x) /\ g(y) ==> x = y) 
        ==> forall y. g(y) ==> f(y)",
        [6]
    )
    (
        // idx 2
        // eqelim.p011
        @"(forall x y z. x * (y * z) = (x * y) * z) /\ 
        (forall x. e * x = x) /\ 
        (forall x. i(x) * x = e) 
        ==> forall x. x * e = x",
        []
    )
    (
        // idx 3
        // eqelim.p013
        @"(forall x y z. x * (y * z) = (x * y) * z) /\ 
        (forall x. e * x = x) /\ 
        (forall x. i(x) * x = e) 
        ==> forall x. x * i(x) = e",
        []
    )
    (
        // idx 4
        // eqelim.p015
        @"(forall x y z. x * (y * z) = (x * y) * z) /\ p * q * p = p 
        ==> exists q'. p * q' * p = p /\ q' * p * q' = q'",
        []
    )
    |]

[<TestCase(0, TestName = "eqelim.p014")>]
[<TestCase(1, TestName = "eqelim.p007")>]
[<TestCase(2, TestName = "eqelim.p011", Category = "LongRunning")>]
[<TestCase(3, TestName = "eqelim.p013", Category = "LongRunning")>]
[<TestCase(4, TestName = "eqelim.p015", Category = "LongRunning")>]

[<Test>]
let ``emeson tests`` idx = 
    let (formula, _) = emesonValues.[idx]
    let (_, result) = emesonValues.[idx]
    let result1 = emeson (parse formula)
    printfn "%A" result1
    result1
    |> should equal result
