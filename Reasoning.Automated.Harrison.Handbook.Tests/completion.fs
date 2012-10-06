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
let ``test critical_pairs``() =
    let eq = (parse "f(f(x)) = g(x)")
    sprint_fol_formula_list (critical_pairs eq eq)
    |> should equal "<<f(g(x0)) =g(f(x0))>>
<<g(x1) =g(x1)>>
"
  
// pg. 284
// ------------------------------------------------------------------------- //
// Inverse property (K&B example 4).                                         //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test complete_and_simplify``() =
    sprint_fol_formula_list (complete_and_simplify ["1"; "*"; "i"] [parse "i(a) * (a * b) = b"])
    |> should equal "<<x0 *i(x0) *x3 =x3>>
<<i(i(x0)) *x1 =x0 *x1>>
<<i(a) *a *b =b>>
"
  
// pg. 284
// ------------------------------------------------------------------------- //
// Auxiliary result used to justify extension of language for cancellation.  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test meson002 and equalitize``() =
    (meson002 << equalitize) (parse "
        (forall x y z. x * y = x * z ==> y = z) <=> 
        (forall x z. exists w. forall y. z = x * y ==> w = y)")
    |> should equal [5; 4]

[<Test>]
let ``test skolemize again``() =
    sprint_fol_formula (skolemize (parse "
        forall x z. exists w. forall y. z = x * y ==> w = y"))
    |> should equal "<<~z =x *y \/ f_w(x,z) =y>>
"
