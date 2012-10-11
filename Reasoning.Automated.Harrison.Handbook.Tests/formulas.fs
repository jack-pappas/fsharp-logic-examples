// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.formulas

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.fol
open NUnit.Framework
open FsUnit

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

[<TestCase(@"exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)", 0)>]
let ``parse formulas`` (f, idx) =
    parse f
    |> should equal parsed_formulas.[idx]


[<Test>]
let ``sanity check parsing``() =
    parse @"((w + x)^4 + (w + y)^4 + (w + z)^4 +
             (x + y)^4 + (x + z)^4 + (y + z)^4 +
             (w - x)^4 + (w - y)^4 + (w - z)^4 +
             (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
            (w^2 + x^2 + y^2 + z^2)^2"
    |> should equal
    <| Atom
         (R ("=",
           [Fn ("/",
             [Fn ("+",
               [Fn ("^", [Fn ("+", [Var "w"; Var "x"]); Fn ("4", [])]);
                Fn ("+",
                 [Fn ("^", [Fn ("+", [Var "w"; Var "y"]); Fn ("4", [])]);
                  Fn ("+",
                   [Fn ("^", [Fn ("+", [Var "w"; Var "z"]); Fn ("4", [])]);
                    Fn ("+",
                     [Fn ("^", [Fn ("+", [Var "x"; Var "y"]); Fn ("4", [])]);
                      Fn ("+",
                       [Fn ("^", [Fn ("+", [Var "x"; Var "z"]); Fn ("4", [])]);
                        Fn ("+",
                         [Fn ("^",
                           [Fn ("+", [Var "y"; Var "z"]); Fn ("4", [])]);
                          Fn ("+",
                           [Fn ("^",
                             [Fn ("-", [Var "w"; Var "x"]); Fn ("4", [])]);
                            Fn ("+",
                             [Fn ("^",
                               [Fn ("-", [Var "w"; Var "y"]); Fn ("4", [])]);
                              Fn ("+",
                               [Fn ("^",
                                 [Fn ("-", [Var "w"; Var "z"]); Fn ("4", [])]);
                                Fn ("+",
                                 [Fn ("^",
                                   [Fn ("-", [Var "x"; Var "y"]); Fn ("4", [])]);
                                  Fn ("+",
                                   [Fn ("^",
                                     [Fn ("-", [Var "x"; Var "z"]);
                                      Fn ("4", [])]);
                                    Fn ("^",
                                     [Fn ("-", [Var "y"; Var "z"]);
                                      Fn ("4", [])])])])])])])])])])])])]);
              Fn ("6", [])]);
            Fn ("^",
             [Fn ("+",
               [Fn ("^", [Var "w"; Fn ("2", [])]);
                Fn ("+",
                 [Fn ("^", [Var "x"; Fn ("2", [])]);
                  Fn ("+",
                   [Fn ("^", [Var "y"; Fn ("2", [])]);
                    Fn ("^", [Var "z"; Fn ("2", [])])])])]);
              Fn ("2", [])])]))


