// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.folderived

open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.folderived
open NUnit.Framework
open FsUnit

// pg. 490
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test icongruence``() = 
    icongruence (parset "s") (parset "t") (parset "f(s,g(s,t,s),u,h(h(s)))")
                            (parset "f(s,g(t,t,s),u,h(h(t)))")
    |> sprint_thm
    |> should equal "|- s =t ==> f(s,g(s,t,s),u,h(h(s))) =f(s,g(t,t,s),u,h(h(t)))"
    
// pg. 494
// ------------------------------------------------------------------------- //
// An example.                                                               //
// ------------------------------------------------------------------------  //

[<TestCase("y", "forall x y z. x + y + z = z + y + x", 
                Result="|- (forall x y z. x +y +z =z +y +x) ==> (forall y' z. y +y' +z =z +y' +y)")>]
[<TestCase("x", "forall x. x = x", 
                Result="|- (forall x. x =x) ==> x =x")>]
[<TestCase("x", "forall x y z. x + y + z = y + z + z", 
                Result="|- (forall x y z. x +y +z =y +z +z) ==> (forall y z. x +y +z =y +z +z)")>]
[<TestCase("w + y + z", "forall x y z. x + y + z = y + z + z", 
                Result="|- (forall x y z. x +y +z =y +z +z) ==> (forall y' z'. (w +y +z) +y' +z' =y' +z' +z')")>]
[<TestCase("x + y + z", "forall x y z. x + y + z = y + z + z", 
                Result="|- (forall x y z. x +y +z =y +z +z) ==> (forall y' z'. (x +y +z) +y' +z' =y' +z' +z')")>]
[<TestCase("x + y + z", "forall x y z. nothing_much", 
                Result="|- (forall x y z. nothing_much) ==> (forall y z. nothing_much)")>]
[<TestCase("x'", "forall x x' x''. x + x' + x'' = 0", 
                Result="|- (forall x x' x''. x +x' +x'' =0) ==> (forall x'' x'''. x' +x'' +x''' =0)")>]
[<TestCase("x''", "forall x x' x''. x + x' + x'' = 0", 
                Result="|- (forall x x' x''. x +x' +x'' =0) ==> (forall x' x'''. x'' +x' +x''' =0)")>]
[<TestCase("x' + x''", "forall x x' x''. x + x' + x'' = 0", 
                Result="|- (forall x x' x''. x +x' +x'' =0) ==> (forall x''' x''''. (x' +x'') +x''' +x'''' =0)")>]
[<TestCase("x + x' + x''", "forall x x' x''. x + x' + x'' = 0", 
                Result="|- (forall x x' x''. x +x' +x'' =0) ==> (forall x''' x''''. (x +x' +x'') +x''' +x'''' =0)")>]
[<TestCase("2 * x", "forall x x'. x + x' = x' + x", 
                Result="|- (forall x x'. x +x' =x' +x) ==> (forall x'. 2 *x +x' =x' +2 *x)")>]
let ``test ispec``(f, qf) = 
    ispec (parset f) (parse qf)
    |> sprint_thm

[<TestCase("x + x", "2 * x", "x + x = x ==> x = 0", "2 * x = x ==> x = 0", 
                    Result="|- x +x =2 *x ==> (x +x =x ==> x =0) ==> 2 *x =x ==> x =0")>]
[<TestCase("x + x", "2 * x", "(x + x = y + y) ==> (y + y + y = x + x + x)", 
                    "2 * x = y + y ==> y + y + y = x + 2 * x", 
                    Result="|- x +x =2 *x ==> (x +x =y +y ==> y +y +y =x +x +x) ==> 2 *x =y +y ==> y +y +y =x +2 *x")>]
[<TestCase("x + x", "2 * x", "(exists x. x = 2) <=> exists y. y + x + x = y + y + y", 
                    "(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)", 
                    Result="|- x +x =2 *x ==> ((exists x. x =2) <=> (exists y. y +x +x =y +y +y)) ==> ((exists x. x =2) <=> (exists y. y +2 *x =y +y +y))")>]
[<TestCase("x", "y", "(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)", 
                    "(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)",
                    Result="|- x =y ==> ((forall z. x =z) <=> (exists x. y <z) /\ (forall y. y <x)) ==> ((forall z. y =z) <=> (exists x. y <z) /\ (forall y'. y' <y))")>]
let ``test isubst``(f1, f2, qf1, qf2) = 
    isubst (parset f1) (parset f2)
            (parse qf1) (parse qf2)
    |> sprint_thm