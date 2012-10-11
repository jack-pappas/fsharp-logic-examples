// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.rewrite

open formulas
open fol
open resolution

//
// ========================================================================= //
// Rewriting.                                                                //
// ========================================================================= //

// pg. 262
// ------------------------------------------------------------------------- //
// Rewriting at the top level with first of list of equations.               //
// ------------------------------------------------------------------------- //

let rec rewrite1 eqs t =
    match eqs with
    | Atom (R ("=", [l; r])) :: oeqs -> 
        try 
            tsubst (term_match undefined [l, t]) r
        with Failure _ ->
            rewrite1 oeqs t
    | _ ->
        failwith "rewrite1"

// pg. 263
// ------------------------------------------------------------------------- //
// Rewriting repeatedly and at depth (top-down).                             //
// ------------------------------------------------------------------------- //

let rec rewrite eqs tm =
    try rewrite eqs (rewrite1 eqs tm)
    with Failure _ ->
        match tm with
        | Var x ->
            tm
        | Fn (f, args) -> 
            let tm' = Fn (f, List.map (rewrite eqs) args)
            if tm' = tm then tm 
            else rewrite eqs tm'
                
// ------------------------------------------------------------------------- //
// Note that ML doesn't accept nonlinear patterns.                           //
// ------------------------------------------------------------------------- //
//
// ********** Point being that CAML doesn't accept nonlinear patterns
//
//function (x,x) -> 0
//
// *********** Actually fun x x -> 0 works, but the xs seem to be
// *********** considered distinct

