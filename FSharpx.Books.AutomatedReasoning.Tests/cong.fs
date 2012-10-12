// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.cong

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.stal
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.cong

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

