// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.stal

open FSharpx.Books.AutomatedReasoning.lib    
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples
open FSharpx.Books.AutomatedReasoning.defcnf
open FSharpx.Books.AutomatedReasoning.dp
open FSharpx.Books.AutomatedReasoning.stal
open FSharp.Compatibility.OCaml
open Num

open NUnit.Framework
open FsUnit

let private triggersValues : (string * ((formula<prop> * formula<prop>) * (formula<prop> * formula<prop>) list) list)[] = [| 
    (
        // idx 0
        // stal.p001
        @"p <=> (q /\ r)",
        [((Atom (P "p"), formula<prop>.True), [(Atom (P "q"), formula<prop>.True); (Atom (P "r"), formula<prop>.True)]); 
         ((Atom (P "q"), formula<prop>.True), [(Atom (P "r"), Atom (P "p"))]); 
         ((Atom (P "q"), Not formula<prop>.True), [(Atom (P "p"), Not formula<prop>.True)]); 
         ((Atom (P "q"), Not (Atom (P "p"))), [(Atom (P "p"), Not formula<prop>.True); (Atom (P "r"), Atom (P "p"))]); 
         ((Atom (P "r"), formula<prop>.True), [(Atom (P "q"), Atom (P "p"))]); 
         ((Atom (P "r"), Atom (P "q")), [(Atom (P "q"), Atom (P "p"))]); 
         ((Atom (P "r"), Not formula<prop>.True), [(Atom (P "p"), Not formula<prop>.True)]); 
         ((Atom (P "r"), Not (Atom (P "p"))), [(Atom (P "p"), Not formula<prop>.True); (Atom (P "q"), Atom (P "p"))]); 
         ((Atom (P "r"), Not (Atom (P "q"))), [(Atom (P "p"), Not formula<prop>.True)])
        ]
    );
    |]

[<TestCase(0, TestName = "stal.p001")>]

[<Test>]
let triggers idx = 
    let (formula, _) = triggersValues.[idx]
    let (_, result) = triggersValues.[idx]
    triggers (parse_prop_formula formula)
    |> should equal result

let private stalmarckValues : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // stal.p002
        (mk_adder_test 6 3),
        true
    );
    (
        // idx 1
        // stal.p003
        (mk_adder_test 2 1),
        true
    );
    |]

[<TestCase(0, TestName = "stal.p002", Category = "LongRunning")>]
[<TestCase(1, TestName = "stal.p003")>]

[<Test>]
let ``stalmarck tests`` idx = 
    let (formula, _) = stalmarckValues.[idx]
    let (_, result) = stalmarckValues.[idx]
    stalmarck formula
    |> should equal result
