// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpx.Books.AutomatedReasoning.Tests.fol

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
    
open NUnit.Framework
open FsUnit

// pg. 126
// fol.p007
// Harrison #06 
[<Test>]
let ``holds with bool_interp``() =
    holds bool_interp undefined (parse "forall x. (x = 0) \/ (x = 1)")
    |> should be True

// fol.p008
// Harrison #06 
[<Test>]
let ``holds with mod_interp 1``() =
    holds (mod_interp 2) undefined (parse "forall x. (x = 0) \/ (x = 1)")
    |> should be True

// fol.p009
// Harrison #06 
[<Test>]
let ``holds with mod_interp 2``() =
    holds (mod_interp 3) undefined (parse "forall x. (x = 0) \/ (x = 1)")
    |> should be False    

// fol.p010
[<Test>]
let ``holds with a range of mod_interp``() =
    let fm = (parse "forall x. ~(x = 0) ==> exists y. x * y = 1")
    List.filter (fun n -> holds (mod_interp n) undefined fm) (1--45)
    |> should equal [1; 2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43]

// pg. 129

// fol.p011
[<Test>]
let ``holds with mod_interp 3``() =
    holds (mod_interp 3) undefined (parse "(forall x. x = 0) ==> 1 = 0")
    |> should be True

// fol.p012
[<Test>]
let ``holds with mod_interp 4``() =
    holds (mod_interp 3) undefined (parse "forall x. x = 0 ==> 1 = 0")
    |> should be False    

// pg. 133
// ------------------------------------------------------------------------- //
// Variant function and examples.                                            //
// ------------------------------------------------------------------------- //

// fol.p013
[<TestCase(@"x", "y", "z", Result = "x")>]
// fol.p014
[<TestCase(@"x", "x", "y", Result = "x'")>]
// fol.p015
[<TestCase(@"x", "x", "x'", Result = "x''")>]
let ``variant``(x, y, z) =
    variant x [y; z]

let private subst_results = [| 
                                Forall ("x'", Atom (R ("=", [Var "x'"; Var "x"])));
                                Forall ("x'",
                                 Forall ("x''",
                                  Imp (Atom (R ("=", [Var "x'"; Var "x"])),
                                   Atom (R ("=", [Var "x'"; Var "x''"])))));
                            |]

// fol.p016
[<TestCase(@"forall x. x = y", 0)>]
// fol.p017
[<TestCase(@"forall x x'. x = y ==> x = x'", 1)>]
let ``subst`` (f, idx) =
    subst ("y" |=> Var "x") (parse f)
    |> should equal subst_results.[idx]



let private parseValues : (string * formula<fol>)[] = [| 
    (
        // idx 0
        // fol.p018
        @"exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)",
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
                            Atom (R ("=", [Var "a"; Var "b"])))))))
    );
    (
        // idx 1
        // fol.p019
        @"((w + x)^4 + (w + y)^4 + (w + z)^4 +
           (x + y)^4 + (x + z)^4 + (y + z)^4 +
           (w - x)^4 + (w - y)^4 + (w - z)^4 +
           (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
           (w^2 + x^2 + y^2 + z^2)^2",
            Atom
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
    )
    |]

[<TestCase(0, TestName = "fol.p018")>]
[<TestCase(1, TestName = "fol.p019")>]

let ``parse tests`` (idx) =
    let (text, _) = parseValues.[idx]
    let (_, result) = parseValues.[idx]
    parse text
    |> should equal result