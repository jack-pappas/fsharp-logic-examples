// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.skolems

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.skolems

open NUnit.Framework
open FsUnit

let private skolemizesValues : (formula<fol> list * formula<fol> list)[] = [| 
    (
        // idx 0
        // skolems.p001
        [parse @"exists x y. x + y = 2";
        parse @"forall x. exists y. x + 1 = y"; ],
        [Atom
           (R ("=",
               [Fn ("old_+",[Fn ("c_x",[]); Fn ("c_y",[])]); Fn ("old_2",[])]));
         Forall
           ("x",
            Atom
              (R ("=",
                  [Fn ("old_+",[Var "x"; Fn ("old_1",[])]);
                   Fn ("f_y",[Var "x"])])))]
    );
    |]

[<TestCase(0, TestName = "skolems.p001")>]

[<Test>]
let skolemizes idx = 
    let (formula, _) = skolemizesValues.[idx]
    let (_, result) = skolemizesValues.[idx]
    skolemizes formula
    |> should equal result