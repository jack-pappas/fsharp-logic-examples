// ========================================================================= //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.Option

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples
open FSharpx.Books.AutomatedReasoning.defcnf
open FSharpx.Books.AutomatedReasoning.dp

open NUnit.Framework
open FsUnit

// OCaml uses exceptions as a control flow.
// In F# exceptions are expensive in terms of time.
// Duning the intial conversion of the from OCaml to F# some of 
// the exceptions were converted to use F# Options. Later
// it was decided to not use F# Options so as to keep
// the F# code as close as possible to the OCaml code
// since the goal was to help people learn from the book and
// using F# Options can dramtically change the appearance of
// the F# code for someone new to F# and/or OCaml.
//
// There is an optimized version of the F# code takes the coverted
// F# code and make such optimizations.
//
// To show that exception as a control flow can be replaced
// equivalently with F# Options, the following test are presented.
//
// In order to be able to test against the F# Options version of the code
// for an F# equivelent, the the F# Options version of the code 
// is placed here for access by the test functions.

let one_literal_rule_Option clauses =
    let findExpr cl =
        List.length cl = 1
    match List.tryFind findExpr clauses with
    | None -> None
    | Some value -> 
        let u = List.head value
        let u' = negate u
        let clauses1 = List.filter (fun cl -> not (mem u cl)) clauses
        image (fun cl -> subtract cl [u']) clauses1
        |> Some

let affirmative_negative_rule_Option clauses =
    let neg', pos = List.partition negative (unions clauses)
    let neg = image negate neg'
    let pos_only = subtract pos neg 
    let neg_only = subtract neg pos
    let pureItem = union pos_only (image negate neg_only)
    if pureItem = [] then None
    else
        let clauses' = List.filter (fun cl -> intersect cl pureItem = []) clauses
        clauses'
        |> Some

let rec dp_Option clauses =
    if clauses = [] then true 
    elif mem [] clauses then false 
    else 
        match one_literal_rule_Option clauses with
        | Some value -> dp_Option value
        | None ->
            match affirmative_negative_rule_Option clauses with
            | Some value -> dp_Option value
            | None -> dp_Option (resolution_rule clauses)

let rec dpll_Option clauses =       
    if clauses = [] then true 
    elif mem [] clauses then false 
    else
        match one_literal_rule_Option clauses with
        | Some value -> dpll value
        | None ->
            match affirmative_negative_rule_Option clauses with
            | Some value -> dpll value
            | None -> 
                let pvs = List.filter positive (unions clauses)
                let p = maximize (posneg_count clauses) pvs
                dpll (insert [p] clauses) || dpll (insert [negate p] clauses)

let dpsat_Option fm = dp_Option (defcnfs fm)

let dptaut_Option fm = not (dpsat_Option (Not fm))
            
let private options001Values : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // dp.p002
        (prime 11),
        true
    );
    |]

[<TestCase(0, TestName = "dp.p002")>]

[<Test>]
let ``options001 tests`` idx = 
    let (prop_formula, _) = options001Values.[idx]
    let (_, result) = options001Values.[idx]
    dptaut_Option prop_formula
    |> should equal result
    dptaut prop_formula
    |> should equal result

let private options002Values : (formula<prop> * bool)[] = [| 
    (
        // idx 0
        // dp.p003
        (prime 11),
        true
    );
    |]

[<TestCase(0, TestName = "dp.p003")>]

[<Test>]
let ``dplltaut tests`` idx = 
    let (prop_formula, _) = options002Values.[idx]
    let (_, result) = options002Values.[idx]
    dptaut_Option prop_formula
    |> should equal result
    dplltaut prop_formula
    |> should equal result
