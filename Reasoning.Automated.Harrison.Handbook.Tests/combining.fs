// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.combining

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.cong
open Reasoning.Automated.Harrison.Handbook.cooper
open Reasoning.Automated.Harrison.Handbook.real
open Reasoning.Automated.Harrison.Handbook.combining
open NUnit.Framework
open FsUnit

// pg. 440
// ------------------------------------------------------------------------- //
// Running example if we magically knew the interpolant.                     //
// ------------------------------------------------------------------------- //
    
[<Test>]
let ``integer qelim``() = 
    (integer_qelim << generalize) (parse
        @"(u + 1 = v /\ v_1 + 1 = u - 1 /\ v_2 - 1 = v + 1 /\ v_3 = v - 1) ==> u = v_3 /\ ~(v_1 = v_2)")
    |> should equal formula<fol>.True // be careful with generic True

[<Test>]
let ``ccvalid``() = 
    ccvalid (parse
        @"(v_2 = f(v_3) /\ v_1 = f(u)) ==> ~(u = v_3 /\ ~(v_1 = v_2))")
    |> should be True
        
// pg. 444
// ------------------------------------------------------------------------- //
// Check that our example works.                                             //
// ------------------------------------------------------------------------- //

[<Test>]
let ``nelop001``() =
    nelop001 (add_default [int_lang]) (parse
        @"f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false")
    |> should be True

[<TestCase(@"y <= x /\ y >= x + z /\ z >= 0 ==> f(f(x) - f(y)) = f(z)", Result = true)>]
[<TestCase(@"x = y /\ y >= z /\ z >= x ==> f(z) = f(x)", Result = true)>]
[<TestCase(@"z = f(x - y) /\ x = z + y /\ ~(-(y) = -(x - f(f(z)))) ==> false", Result = true)>]
[<TestCase(@"a + 2 = b ==> f(read(update(A,a,3),b-2)) = f(b - a + 1)", Result = false)>]
[<TestCase(@"hd(x) = hd(y) /\ tl(x) = tl(y) /\ ~(x = nil) /\ ~(y = nil) ==> f(x) = f(y)", Result = false)>]
[<TestCase(@"~(f(f(x) - f(y)) = f(z)) /\ y <= x /\ y >= x + z /\ z >= 0 ==> false", Result = true)>]
[<TestCase(@"(x >= y ==> MAX(x,y) = x) /\ (y >= x ==> MAX(x,y) = y) ==> x = y + 2 ==> MAX(x,y) = x", Result = true)>]
[<TestCase(@"x <= g(x) /\ x >= g(x) ==> x = g(g(g(g(x))))", Result = true)>]
[<TestCase(@"2 * f(x + y) = 3 * y /\ 2 * x = y ==> f(f(x + y)) = 3 * x", Result = true)>]
[<TestCase(@"4 * x = 2 * x + 2 * y /\ x = f(2 * x - y) /\ f(2 * y - x) = 3 /\ f(x) = 4 ==> false", Result = true)>]
let ``nelop int_lang`` f = 
    nelop (add_default [int_lang]) (parse f)

[<TestCase(@"x^2 =  1 ==> (f(x) = f(-(x)))  ==> (f(x) = f(1))", Result = true)>]
let ``nelop real_lang`` f = 
    nelop (add_default [real_lang]) (parse f)

// pg. 447
// ------------------------------------------------------------------------- //
// Confirmation of non-convexity.                                            //
// ------------------------------------------------------------------------- //

[<Test>]
let ``non-convexity real_qelim``() = 
    List.map (real_qelim << generalize) [
        parse @"x * y = 0 /\ z = 0 ==> x = z \/ y = z";
        parse @"x * y = 0 /\ z = 0 ==> x = z";
        parse @"x * y = 0 /\ z = 0 ==> y = z"; ]
    |> should equal [formula<fol>.True; formula<fol>.False; formula<fol>.False]

[<Test>]
let ``non-convexity integer_qelim``() = 
    List.map (integer_qelim << generalize) [
        parse @"0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y \/ x = z";
        parse @"0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y";
        parse @"0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = z"; ]
    |> should equal [formula<fol>.True; formula<fol>.False; formula<fol>.False]
