// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.folderived

open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.folderived
open NUnit.Framework
open FsUnit

// pg. 490
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``icongruence``() = 
    icongruence (parset @"s") (parset @"t") (parset @"f(s,g(s,t,s),u,h(h(s)))")
                            (parset @"f(s,g(t,t,s),u,h(h(t)))")
    |> should equal (parse @"s = t ==> f(s,g(s,t,s),u,h(h(s))) = f(s,g(t,t,s),u,h(h(t)))")
    
// pg. 494
// ------------------------------------------------------------------------- //
// An example.                                                               //
// ------------------------------------------------------------------------  //

let private results = [|
                @"(forall x y z. x + y + z = z + y + x) ==>
                    (forall y' z. y + y' + z = z + y' + y)"; // 0
                @"x + x = 2 * x ==> (x + x = x ==> x = 0) ==> 2 * x = x ==> x = 0"; // 1
                @"x + x = 2 * x ==>
                    (x + x = y + y ==> y + y + y = x + x + x) ==>
                    2 * x = y + y ==> y + y + y = x + 2 * x"; // 2
                @"(forall x y z. x + y + z = y + z + z) ==>
                    (forall y z. x + y + z = y + z + z)"; // 3
                @"(forall x. x = x) ==> x = x"; // 4
                @"(forall x y z. x + y + z = y + z + z) ==>
                    (forall y' z'. (w + y + z) + y' + z' = y' + z' + z')"; // 5
                @"(forall x y z. x + y + z = y + z + z) ==>
                    (forall y' z'. (x + y + z) + y' + z' = y' + z' + z')"; // 6
                @"(forall x y z. nothing_much) ==> (forall y z. nothing_much)"; // 7
                @"x + x = 2 * x ==>
                    ((exists x. x = 2) <=> (exists y. y + x + x = y + y + y)) ==>
                    ((exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y))"; // 8
                @"x = y ==>
                    ((forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)) ==>
                    ((forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y))"; // 9
                @"(forall x x' x''. x + x' + x'' = 0) ==>
                    (forall x'' x'''. x' + x'' + x''' = 0)"; // 10
                @"(forall x x' x''. x + x' + x'' = 0) ==>
                    (forall x' x'''. x'' + x' + x''' = 0)"; // 11
                @"(forall x x' x''. x + x' + x'' = 0) ==>
                    (forall x''' x''''. (x' + x'') + x''' + x'''' = 0)"; // 12
                @"(forall x x' x''. x + x' + x'' = 0) ==>
                    (forall x''' x''''. (x + x' + x'') + x''' + x'''' = 0)"; // 13
                @"(forall x x'. x + x' = x' + x) ==> (forall x'. 2 * x + x' = x' + 2 * x)"; // 14
        |]

[<TestCase(@"y", @"forall x y z. x + y + z = z + y + x", 0)>]
[<TestCase(@"x", @"forall x y z. x + y + z = y + z + z", 3)>]
[<TestCase(@"x", @"forall x. x = x", 4)>]
[<TestCase(@"w + y + z", @"forall x y z. x + y + z = y + z + z", 5)>]
[<TestCase(@"x + y + z", @"forall x y z. x + y + z = y + z + z", 6)>]
[<TestCase(@"x + y + z", @"forall x y z. nothing_much", 7)>]
[<TestCase(@"x'", @"forall x x' x''. x + x' + x'' = 0", 10)>]
[<TestCase(@"x''", @"forall x x' x''. x + x' + x'' = 0", 11)>]
[<TestCase(@"x' + x''", @"forall x x' x''. x + x' + x'' = 0", 12)>]
[<TestCase(@"x + x' + x''", @"forall x x' x''. x + x' + x'' = 0", 13)>]
[<TestCase(@"2 * x", @"forall x x'. x + x' = x' + x", 14)>]
let ``ispec``(f, qf, idx) = 
    ispec (parset f) (parse qf)
    |> should equal (parse results.[idx])

[<TestCase(@"x + x", @"2 * x", @"x + x = x ==> x = 0", @"2 * x = x ==> x = 0", 1)>]
[<TestCase(@"x + x", @"2 * x", @"(x + x = y + y) ==> (y + y + y = x + x + x)", 
                    @"2 * x = y + y ==> y + y + y = x + 2 * x", 2)>]
[<TestCase(@"x + x", @"2 * x", @"(exists x. x = 2) <=> exists y. y + x + x = y + y + y", 
                    @"(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)", 8)>]
[<TestCase(@"x", @"y", @"(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)", 
                    @"(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)", 9)>]
let ``isubst``(f1, f2, qf1, qf2, idx) = 
    isubst (parset f1) (parset f2)
            (parse qf1) (parse qf2)
    |> should equal (parse results.[idx])