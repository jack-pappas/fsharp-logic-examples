// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.cong

open formulas
open prop
open folMod
open skolem
open equal

// pg. 249
// ========================================================================= //
// Simple congruence closure.                                                //
// ========================================================================= //

let rec subterms tm =
    match tm with
    | Fn (f, args) ->
        List.foldBack (union << subterms) args [tm]
    | _ -> [tm]

// pg. 250
// ------------------------------------------------------------------------- //
// Test whether subterms are congruent under an equivalence.                 //
// ------------------------------------------------------------------------- //

let congruent eqv (s, t) =
    match s, t with
    | Fn (f, a1), Fn (g, a2) when f = g ->
        List.forall2 (equivalent eqv) a1 a2
    | _ -> false

// pg. 251
// ------------------------------------------------------------------------- //
// Merging of terms, with congruence closure.                                //
// ------------------------------------------------------------------------- //

let rec emerge (s, t) (eqv, pfn) =
    let s' = canonize eqv s 
    let t' = canonize eqv t
    if s' = t' then
        eqv, pfn
    else
        let sp = tryapplyl pfn s' 
        let tp = tryapplyl pfn t'
        let eqv' = equate (s, t) eqv
        let st' = canonize eqv' s'
        let pfn' = (st' |-> union sp tp) pfn
        List.foldBack (fun (u, v) (eqv, pfn) ->
                    if congruent eqv (u, v) then emerge (u, v) (eqv, pfn)
                    else eqv, pfn)
                (allpairs (fun u v -> (u, v)) sp tp) (eqv', pfn')

// pg. 253
// ------------------------------------------------------------------------- //
// Satisfiability of conjunction of ground equations and inequations.        //
// ------------------------------------------------------------------------- //

let predecessors t pfn =
    match t with
    | Fn (f, a) ->
        List.foldBack (fun s f -> (s |-> insert t (tryapplyl f s)) f) (setify a) pfn
    | _ -> pfn

let ccsatisfiable fms =
    let pos, neg = List.partition positive fms
    let eqps = List.map dest_eq pos 
    let eqns = List.map (dest_eq << negate) neg        
    let pfn =
        let lrs =
            List.map fst eqps
            @ List.map snd eqps
            @ List.map fst eqns
            @ List.map snd eqns
        List.foldBack predecessors (unions (List.map subterms lrs)) undefined
    let eqv, _ = List.foldBack emerge eqps (unequal, pfn)
    List.forall (fun (l, r) ->
        not <| equivalent eqv l r) eqns

// pg. 253
// ------------------------------------------------------------------------- //
// Validity checking a universal formula.                                    //
// ------------------------------------------------------------------------- //

let ccvalid fm =
    let fms = simpdnf (askolemize (Not (generalize fm)))
    not (List.exists ccsatisfiable fms)
