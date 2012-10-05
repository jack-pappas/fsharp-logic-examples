// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Reasoning.Automated.Harrison.Handbook.Tests.fol

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
    
open NUnit.Framework
open FsUnit

// pg. 126

[<Test>]
let ``test holds with bool_interp``() =
    holds bool_interp undefined (parse "forall x. (x = 0) \/ (x = 1)")
    |> should be True

[<Test>]
let ``test holds with mod_interp 1``() =
    holds (mod_interp 2) undefined (parse "forall x. (x = 0) \/ (x = 1)")
    |> should be True

[<Test>]
let ``test holds with mod_interp 2``() =
    holds (mod_interp 3) undefined (parse "forall x. (x = 0) \/ (x = 1)")
    |> should be False    

    
[<Test>]
let ``test holds with a range of mod_interp``() =
    let fm = (parse "forall x. ~(x = 0) ==> exists y. x * y = 1")
    List.filter (fun n -> holds (mod_interp n) undefined fm) (1--45)
    |> should equal [1; 2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43]

// pg. 129

[<Test>]
let ``test holds with mod_interp 3``() =
    holds (mod_interp 3) undefined (parse "(forall x. x = 0) ==> 1 = 0")
    |> should be True

[<Test>]
let ``test holds with mod_interp 4``() =
    holds (mod_interp 3) undefined (parse "forall x. x = 0 ==> 1 = 0")
    |> should be False    

// pg. 133
// ------------------------------------------------------------------------- //
// Variant function and examples.                                            //
// ------------------------------------------------------------------------- //

[<TestCase("x", "y", "z", Result="x")>]
[<TestCase("x", "x", "y", Result="x'")>]
[<TestCase("x", "x", "x'", Result="x''")>]
let ``test variant``(x, y, z) =
    variant x [y; z]