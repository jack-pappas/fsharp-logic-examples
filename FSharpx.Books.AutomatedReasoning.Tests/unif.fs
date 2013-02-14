// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.unif

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.unif

open NUnit.Framework
open FsUnit

let private unify_and_applyValues : ((term * term) list * (term * term) list)[] = [| 
    (
        // idx 0
        // unif.p001
        [(parset @"f(x,g(y))"),(parset @"f(f(z),w)")],
        [(Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]),
            Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]))]
    );
    (
        // idx 1
        // unify.p002
        [(parset @"f(x,y)"),(parset @"f(y,x)")],
        [(Fn ("f",[Var "y"; Var "y"]), Fn ("f",[Var "y"; Var "y"]))]
    );
    (
        // idx 2
        // unify.p003
        [(parset @"f(x,g(y))"),(parset @"f(y,x)")],
        [(Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]),
            Fn ("f",[Fn ("f",[Var "z"]); Fn ("g",[Var "y"])]))]
    );
    (
        // idx 3
        // unify.p004
        [(parset @"x_0"),(parset @"f(x_1,x_1)");
         (parset @"x_1"),(parset @"f(x_2,x_2)");
         (parset @"x_2"),(parset @"f(x_3,x_3)")],
        [(Fn
            ("f",
             [Fn
                ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]);
              Fn
                ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])])]),
          Fn
            ("f",
             [Fn
                ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]);
              Fn
                ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])])]));
         (Fn ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]),
          Fn ("f",[Fn ("f",[Var "x_3"; Var "x_3"]); Fn ("f",[Var "x_3"; Var "x_3"])]));
         (Fn ("f",[Var "x_3"; Var "x_3"]), Fn ("f",[Var "x_3"; Var "x_3"]))]
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "unif.p001")>]
[<TestCase(1, TestName = "unif.p002")>]
[<TestCase(2, TestName = "unif.p003",
    ExpectedException = typeof<System.Exception>,
    ExpectedMessage = "cyclic")>]
[<TestCase(3, TestName = "unif.p004")>]
let ``unify_and_apply tests`` (idx) =
    let (eqs, _) = unify_and_applyValues.[idx]
    let (_, result) = unify_and_applyValues.[idx]
    unify_and_apply eqs
    |> should equal result
