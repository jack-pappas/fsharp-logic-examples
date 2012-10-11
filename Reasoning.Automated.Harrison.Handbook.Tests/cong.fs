// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.cong

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.stal
open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.cong

open NUnit.Framework
open FsUnit

// pg. 253
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``ccvalid 1``() =
    ccvalid (parse @"f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c 
        ==> f(c) = c \/ f(g(c)) = g(f(c))")
    |> should be True
    
[<Test>]
let ``ccvalid 2``() =
    ccvalid (parse @"f(f(f(f(c)))) = c /\ f(f(c)) = c ==> f(c) = c")
    |> should be False

