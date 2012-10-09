// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.completion

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.rewrite
open Reasoning.Automated.Harrison.Handbook.order
open Reasoning.Automated.Harrison.Handbook.completion

open NUnit.Framework
open FsUnit

// pg. 277
// ------------------------------------------------------------------------- //
// Simple example.                                                           //
// ------------------------------------------------------------------------- //

[<Test>]
let ``critical_pairs``() =
    let eq = (parse @"f(f(x)) = g(x)")
    critical_pairs eq eq
    |> should equal 
    <| [Atom
          (R ("=",
            [Fn ("f", [Fn ("g", [Var "x0"])]);
             Fn ("g", [Fn ("f", [Var "x0"])])]));
        Atom (R ("=", [Fn ("g", [Var "x1"]); Fn ("g", [Var "x1"])]))]

// pg. 284
// ------------------------------------------------------------------------- //
// Inverse property (K&B example 4).                                         //
// ------------------------------------------------------------------------- //

[<Test>]
let ``complete_and_simplify``() =
    complete_and_simplify ["1"; "*"; "i"] [parse @"i(a) * (a * b) = b"]
    |> should equal
    <| [Atom
          (R ("=",
            [Fn ("*", [Var "x0"; Fn ("*", [Fn ("i", [Var "x0"]); Var "x3"])]);
             Var "x3"]));
         Atom
          (R ("=",
            [Fn ("*", [Fn ("i", [Fn ("i", [Var "x0"])]); Var "x1"]);
             Fn ("*", [Var "x0"; Var "x1"])]));
         Atom
          (R ("=",
            [Fn ("*", [Fn ("i", [Var "a"]); Fn ("*", [Var "a"; Var "b"])]);
             Var "b"]))]
  
// pg. 284
// ------------------------------------------------------------------------- //
// Auxiliary result used to justify extension of language for cancellation.  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``meson002 and equalitize``() =
    (meson002 >>|> equalitize) (parse @"
        (forall x y z. x * y = x * z ==> y = z) <=> 
        (forall x z. exists w. forall y. z = x * y ==> w = y)")
    |> should equal [5; 4]

[<Test>]
let ``skolemize again``() =
    skolemize (parse @"
        forall x z. exists w. forall y. z = x * y ==> w = y")
    |> should equal
    <| Or (Not (Atom (R ("=", [Var "z"; Fn ("*", [Var "x"; Var "y"])]))),
            Atom (R ("=", [Fn ("f_w", [Var "x"; Var "z"]); Var "y"])))
