// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.dp

open intro
open formulas
open prop
open defcnf 

// ========================================================================= //
// The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.           //
// ========================================================================= //

// pg. 81
// ------------------------------------------------------------------------- //
// The DP procedure.                                                         //
// ------------------------------------------------------------------------- //    
      
// Note: Signature difference because of use of F# List.tryFind
// OCaml : 'a formula list list -> 'a formula list list = <fun>
// F#    : 'a formula list list -> 'a formula list list option
let one_literal_rule clauses =
    let findExpr cl =
        List.length cl = 1

    match List.tryFind findExpr clauses with
    | None -> None
    | Some value -> 
        let u = List.head value
        let u' = negate u
        clauses
        |> List.filter (fun cl -> not (mem u cl))
        |> image (fun cl -> subtract cl [u'])
        |> Some
        
// Note signature difference because of use of F# Some and None
// OCaml : 'a formula list list -> 'a formula list list = <fun>
// F#    : 'a formula list list -> 'a formula list list option
let affirmative_negative_rule clauses =
    let neg', pos = List.partition negative (unions clauses)
    let neg = image negate neg'
    let pos_only = subtract pos neg 
    let neg_only = subtract neg pos
    let pureItem = union pos_only (image negate neg_only)
    if pureItem = [] then None
    else
        let clauses' = List.filter (fun cl -> intersect cl pureItem = []) clauses
        Some clauses'
            
let resolve_on p clauses =
    let p' = negate p 
    let pos, notpos = List.partition (mem p) clauses
    let neg, other = List.partition (mem p') notpos
    let res0 =
        let pos' = image (List.filter (fun l -> l <> p)) pos
        let neg' = image (List.filter (fun l -> l <> p')) neg
        allpairs union pos' neg'
    let clauses' = union other (List.filter (non trivial) res0)
    clauses'

let resolution_blowup cls l =
    let m = List.length (List.filter (mem l) cls)
    let n = List.length (List.filter (mem (negate l)) cls)
    m * n - m - n

let resolution_rule clauses =
    let pvs = List.filter positive (unions clauses)
    let p = minimize (resolution_blowup clauses) pvs
    resolve_on p clauses

//. pg. 84. 
// ------------------------------------------------------------------------- //
// Overall procedure.                                                        //
// ------------------------------------------------------------------------- //

let rec dp clauses =
    if clauses = [] then true 
    elif mem [] clauses then false 
    else 
        match one_literal_rule clauses with
        | Some value -> dp value
        | None ->
            match affirmative_negative_rule clauses with
            | Some value -> dp value
            | None -> dp (resolution_rule clauses)

// pg. 84
// ------------------------------------------------------------------------- //
// Davis-Putnam satisfiability tester and tautology checker.                 //
// ------------------------------------------------------------------------- //

let dpsat fm = dp (defcnfs fm)

let dptaut fm = not (dpsat (Not fm))

// pg. 85
// ------------------------------------------------------------------------- //
// The same thing but with the DPLL procedure.                               //
// ------------------------------------------------------------------------- //

let posneg_count cls l =
    let m = List.length (List.filter (mem l) cls)                 
    let n = List.length (List.filter (mem (negate l)) cls)
    m + n                                  

let rec dpll clauses =       
    if clauses = [] then true 
    elif mem [] clauses then false 
    else
        match one_literal_rule clauses with
        | Some value -> dpll value
        | None ->
            match affirmative_negative_rule clauses with
            | Some value -> dpll value
            | None -> 
                let pvs = List.filter positive (unions clauses)
                let p = maximize (posneg_count clauses) pvs
                dpll (insert [p] clauses) || dpll (insert [negate p] clauses)
                                                     
let dpllsat fm = dpll (defcnfs fm)

let dplltaut fm = not (dpllsat (Not fm))                   

// pg.86
// ------------------------------------------------------------------------- //
// Iterative implementation with explicit trail instead of recursion.        //
// ------------------------------------------------------------------------- //

type trailmix = Guessed | Deduced

let unassigned =
    let litabs p = 
        match p with
        | Not q -> q
        | _ -> p
    fun cls trail ->
        subtract (unions (image (image litabs) cls))
            (image (litabs << fst) trail)

let rec unit_subpropagate (cls, fn, trail) =
    let cls' = List.map (List.filter (not << defined fn << negate)) cls
    let uu = function
        | [c] when not (defined fn c) -> [c]
        | _ -> failwith ""
    let newunits = unions (mapfilter uu cls')
    if newunits = [] then
        cls', fn, trail
    else
        let trail' = List.foldBack (fun p t -> (p, Deduced) :: t) newunits trail
        let fn' = List.foldBack (fun u -> u |-> ()) newunits fn
        unit_subpropagate (cls', fn', trail')

let unit_propagate (cls, trail) =
    let fn = List.foldBack (fun (x, _) -> x |-> ()) trail undefined
    let cls', fn', trail' = unit_subpropagate (cls, fn, trail)
    cls', trail'

let rec backtrack trail =
    match trail with
    | (p, Deduced) :: tt ->
        backtrack tt
    | _ -> trail

let rec dpli cls trail =
    let cls', trail' = unit_propagate (cls, trail)
    if mem [] cls' then
        match backtrack trail with
        | (p, Guessed) :: tt ->
            dpli cls ((negate p, Deduced) :: tt)
        | _ -> false
        else
            match unassigned cls trail' with
            | [] -> true
            | ps ->
                let p = maximize (posneg_count cls') ps
                dpli cls ((p, Guessed) :: trail')

let dplisat fm = dpli (defcnfs fm) []

let dplitaut fm = not (dplisat (Not fm))

// pg. 88
// ------------------------------------------------------------------------- //
// With simple non-chronological backjumping and learning.                   //
// ------------------------------------------------------------------------- //

let rec backjump cls p trail =
    match backtrack trail with
    | (q, Guessed) :: tt ->
        let cls', trail' = unit_propagate (cls, (p, Guessed) :: tt)
        if mem [] cls' then backjump cls p tt else trail
    | _ -> trail

let rec dplb cls trail =
    let cls', trail' = unit_propagate (cls, trail)
    if mem [] cls' then
        match backtrack trail with
        | (p, Guessed) :: tt ->
            let trail' = backjump cls p tt
            let declits = List.filter (fun (_, d) -> d = Guessed) trail'
            let conflict = insert (negate p) (image (negate << fst) declits)
            dplb (conflict :: cls) ((negate p, Deduced) :: trail')
        | _ -> false
    else
        match unassigned cls trail' with
        | [] -> true
        | ps ->
            let p = maximize (posneg_count cls') ps
            dplb cls ((p, Guessed) :: trail')

let dplbsat fm = dplb (defcnfs fm) []

let dplbtaut fm = not (dplbsat (Not fm))


