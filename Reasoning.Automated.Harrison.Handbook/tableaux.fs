// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.tableaux

open intro
open formulas
open prop
open folMod
open skolem
open herbrand
open unif

// ========================================================================= //
// Tableaux, seen as an optimized version of a Prawitz-like procedure.       //
// ========================================================================= //
//
// pg. 174
// ------------------------------------------------------------------------- //
// Unify literals (just pretend the toplevel relation is a function).        //
// ------------------------------------------------------------------------- //

let rec unify_literals env tmp =
    match tmp with
    | False, False ->
        env
    | Not p, Not q ->
        unify_literals env (p, q)
    | Atom (R (p1, a1)), Atom (R (p2, a2)) ->
        unify env [Fn (p1, a1), Fn (p2, a2)]        
    | _ ->
        failwith "Can't unify literals"

// pg. 174
// ------------------------------------------------------------------------- //
// Unify complementary literals.                                             //
// ------------------------------------------------------------------------- //

let inline unify_complements env (p, q) =
    unify_literals env (p, negate q)

// pg. 174
// ------------------------------------------------------------------------- //
// Unify and refute a set of disjuncts.                                      //
// ------------------------------------------------------------------------- //

let rec unify_refute djs (acc : func<string, term>) : func<string, term> =
    match djs with
    | [] ->
        acc
    | head :: tail ->
        head
        |> List.partition positive
        ||> allpairs (fun p q -> (p, q))
        |> tryfind (unify_refute tail << unify_complements acc)


// pg. 175
// ------------------------------------------------------------------------- //
// Hence a Prawitz-like procedure (using unification on DNF).                //
// ------------------------------------------------------------------------- //

let rec prawitz_loop djs0 fvs djs n =
    let djs1 =
        let inst =
            let newvars =
                // OPTIMIZE : Change this call to List.map to use List.init instead.
                let l = List.length fvs
                List.map (fun k -> "_" + string (n * l + k)) [1 .. l]
            fpf fvs (List.map Var newvars)
        distrib (image (image (subst inst)) djs0) djs

    try unify_refute djs1 undefined,(n + 1)
    with Failure _ ->
        prawitz_loop djs0 fvs djs1 (n + 1)

let prawitz fm =
    let fm0 = skolemize (Not (generalize fm))
    snd <| prawitz_loop (simpdnf fm0) (fv fm0) [[]] 0

// ------------------------------------------------------------------------- //
// Comparison of number of ground instances.                                 //
// ------------------------------------------------------------------------- //

let compare fm =
    prawitz fm, davisputnam fm

// pg. 177
// ------------------------------------------------------------------------- //
// More standard tableau procedure, effectively doing DNF incrementally.     //
// ------------------------------------------------------------------------- //

let rec tableau (fms, lits, n, env, k) cont =
    if n < 0 then
        failwith "no proof at this level"
    else
        match fms with
        | [] ->
            failwith "tableau: no proof"

        | And (p, q) :: unexp ->
            tableau (p :: q :: unexp, lits, n, env, k) cont

        | Or (p, q) :: unexp ->
            tableau (p :: unexp, lits, n, env, k) <| fun (env, k) ->
                tableau (q :: unexp, lits, n, env, k) cont

        | Forall (x, p) :: unexp ->
            let fms =
                let p' =
                    let y = Var ("_" + string k)
                    subst (x |=> y) p
                p' :: unexp @ [Forall (x, p)]

            tableau (fms, lits, n - 1, env, k + 1) cont

        | fm :: unexp ->
            try
                lits
                |> tryfind (fun l ->
                    cont (unify_complements env (fm, l), k))
            with Failure _ ->
                tableau (unexp, fm :: lits, n, env, k) cont

let rec deepen n f =
    try printfn "Searching with depth limit %d" n
        f n
    with Failure _ ->
        deepen (n + 1) f
        
let tabrefute fms =
    deepen 0 <| fun n ->
        tableau (fms, [], n, undefined, 0) id
        |> ignore
        n

let tab fm =
    match askolemize <| Not (generalize fm) with
    | False -> 0
    | sfm ->
        tabrefute [sfm]

// pg. 178
// ------------------------------------------------------------------------- //
// Try to split up the initial formula first; often a big improvement.       //
// ------------------------------------------------------------------------- //

let splittab fm =
    generalize fm
    |> Not
    |> askolemize
    |> simpdnf
    |> List.map tabrefute

