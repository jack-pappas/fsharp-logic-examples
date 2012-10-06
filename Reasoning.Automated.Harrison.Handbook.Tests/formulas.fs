// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.formulas

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.folMod
open NUnit.Framework
open FsUnit

// TODO : Implement unit tests for formulas (particularly parsing and evaluation).

let private parsed_formulas : formula<fol>[] = [|
    Exists ("a",
     Exists ("b",
      And (Atom (R (">", [Var "a"; Fn ("1", [])])),
       And (Atom (R (">", [Var "b"; Fn ("1", [])])),
        And
         (Or (Atom (R ("=", [Fn ("*", [Fn ("2", []); Var "b"]); Var "a"])),
           Atom
            (R ("=",
              [Fn ("*", [Fn ("2", []); Var "b"]);
               Fn ("+", [Fn ("*", [Fn ("3", []); Var "a"]); Fn ("1", [])])]))),
         Atom (R ("=", [Var "a"; Var "b"])))))));
    |]

// This case currently fails (raises exception) when the formula is
// on two lines; if it's put on a single line, it parses just fine.
[<TestCase("exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)", 0)>]
let ``parse formulas`` (f, idx) =
    parse f
    |> should equal parsed_formulas.[idx]


