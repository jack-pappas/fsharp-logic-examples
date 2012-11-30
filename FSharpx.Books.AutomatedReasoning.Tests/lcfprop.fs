// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.lcfprop

open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop

open NUnit.Framework
open FsUnit

let private lcfpropValues : (string * thm * string )[] = [| 
    (
        // idx 0
        // Pelletier #12
        // lcfprop.p003
        @"((p <=> q) <=> r) <=> (p <=> (q <=> r))",
        Iff
            (Iff (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),Atom (R ("r",[]))),
            Iff (Atom (R ("p",[])),Iff (Atom (R ("q",[])),Atom (R ("r",[]))))),
        @"|- ((p <=> q) <=> r) <=> p <=> q <=> r"
    );
    (
        // idx 1
        // Pelletier #16
        // lcfprop.p001
        @"(p ==> q) \/ (q ==> p)",
        Or
            (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),
            Imp (Atom (R ("q",[])),Atom (R ("p",[])))),
        @"|- (p ==> q) \/ (q ==> p)"
    );
    (
        // idx 2
        // Harrison #02 - Equations within equations
        // lcfprop.p002
        @"p /\ q <=> ((p <=> q) <=> p \/ q)",
        Iff
            (And (Atom (R ("p",[])),Atom (R ("q",[]))),
            Iff
                (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),
                Or (Atom (R ("p",[])),Atom (R ("q",[]))))),
        @"|- p /\ q <=> (p <=> q) <=> p \/ q"
    );
    |]
    
[<TestCase(0, TestName = "Pelletier #12")>]
[<TestCase(1, TestName = "Pelletier #16")>]
[<TestCase(1, TestName = "Harrison #02 - Equations within equations")>]

[<Test>]
let ``lcftaut ast tests`` idx = 
    let (formula, _, _) = lcfpropValues.[idx]
    let (_, ast_result, _) = lcfpropValues.[idx]
    lcftaut (parse formula)
    |> should equal ast_result

[<TestCase(0, TestName = "Pelletier #12")>]
[<TestCase(1, TestName = "Pelletier #16")>]
[<TestCase(1, TestName = "Harrison #02 - Equations within equations")>]

[<Test>]
let ``lcftaut pp tests`` idx = 
    let (formula, _, _) = lcfpropValues.[idx]
    let (_, _, pretty_printer_result) = lcfpropValues.[idx]
    lcftaut (parse formula)
    |> sprint_thm
    |> should equal pretty_printer_result
