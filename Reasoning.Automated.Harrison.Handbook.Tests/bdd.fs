// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.bdd

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples
open FSharpx.Books.AutomatedReasoning.bdd
 
open NUnit.Framework
open FsUnit

// pg. 105
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``bddtaut``() =
    bddtaut (mk_adder_test 4 2)
    |> should be True

// pg. 107
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``ebddtaut with prime``() =
    ebddtaut (prime 101)
    |> should be True

[<Test>]
let ``ebddtaut with mk_adder_test``() =
    ebddtaut (mk_adder_test 9 5)
    |> should be True


