// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.unif

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.unif

open NUnit.Framework
open FsUnit

// pg. 171
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``unify_and_apply 1``() =
    unify_and_apply [(parset "f(x,g(y))"),(parset "f(f(z),w)")]
    |> should equal [(Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]),
                        Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]))]

[<Test>]
let ``unify_and_apply 2``() =
    unify_and_apply [(parset "f(x,y)"),(parset "f(y,x)")]
    |> should equal [(Fn ("f",[Var "y"; Var "y"]), Fn ("f",[Var "y"; Var "y"]))]

[<Test>]
let ``unify_and_apply 3``() =
    unify_and_apply [(parset "x_0"),(parset "f(x_1,x_1)");
                        (parset "x_1"),(parset "f(x_2,x_2)");
                        (parset "x_2"),(parset "f(x_3,x_3)")]
    |> should equal [(Fn
                          ("f",
                            [Fn
                                ("f",
                                [Fn ("f",[Var "x_3"; Var "x_3"]);
                                Fn ("f",[Var "x_3"; Var "x_3"])]);
                            Fn
                                ("f",
                                    [Fn ("f",[Var "x_3"; Var "x_3"]);
                                    Fn ("f",[Var "x_3"; Var "x_3"])])]),
                        Fn
                            ("f",
                            [Fn
                                ("f",
                                    [Fn ("f",[Var "x_3"; Var "x_3"]);
                                    Fn ("f",[Var "x_3"; Var "x_3"])]);
                            Fn
                                ("f",
                                    [Fn ("f",[Var "x_3"; Var "x_3"]);
                                    Fn ("f",[Var "x_3"; Var "x_3"])])]));
                        (Fn
                            ("f",
                                [Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]),
                         Fn
                            ("f",
                                [Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]));
                        (Fn ("f",[Var "x_3"; Var "x_3"]), Fn ("f",[Var "x_3"; Var "x_3"]))]
