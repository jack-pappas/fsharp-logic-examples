// IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
// By downloading, copying, installing or using the software you agree
// to this license.  If you do not agree to this license, do not
// download, install, copy or use the software.
// 
// Copyright (c) 2003-2007, John Harrison
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of John Harrison may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
// USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.
//
// ===================================================================
//
// Converted to F# 2.0
//
// Copyright (c) 2012, Eric Taucher
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the previous disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the previous disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of Eric Taucher may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
//
// ===================================================================

namespace Reasoning.Automated.Harrison.Handbook

module tableaux =
    open intro
    open formulas
    open prop
    open folMod
    open skolem
    open herbrand
    open unif

// ========================================================================= //
// Tableaux, seen as an optimized version of a Prawitz-like procedure.       //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //
//
// pg. 174
// ------------------------------------------------------------------------- //
// Unify literals (just pretend the toplevel relation is a function).        //
// ------------------------------------------------------------------------- //

    let rec unify_literals env tmp =
        match tmp with
        | Atom (R (p1, a1)), Atom (R (p2, a2)) ->
            unify env [Fn(p1,a1),Fn(p2,a2)]
        | Not p, Not q ->
            unify_literals env (p,q)
        | False, False -> env
        | _ -> failwith "Can't unify literals"

// pg. 174
// ------------------------------------------------------------------------- //
// Unify complementary literals.                                             //
// ------------------------------------------------------------------------- //

    let unify_complements env (p,q) =
        unify_literals env (p, negate q)

// pg. 174
// ------------------------------------------------------------------------- //
// Unify and refute a set of disjuncts.                                      //
// ------------------------------------------------------------------------- //

    // Note: Used book tryfind instead of F# List.tryFind
    let rec unify_refute djs (acc : func<string, term>) : func<string, term> =
        let rec tryfind f l =
            match l with
            | [] ->
                failwith "tryfind"
            | h::t -> 
                try f h
                with _ ->
                    tryfind f t

        match djs with
        | [] -> acc
        | head :: tail -> 
            let pos, neg = List.partition positive head
            let unifyResult = unify_complements acc
            tryfind (unify_refute tail >>|> unify_complements acc) (allpairs (fun p q -> (p, q)) pos neg)


// pg. 175
// ------------------------------------------------------------------------- //
// Hence a Prawitz-like procedure (using unification on DNF).                //
// ------------------------------------------------------------------------- //

    let rec prawitz_loop djs0 fvs djs n =
        let l = List.length fvs
        let newvars = List.map (fun k -> "_" + string (n * l + k)) (1--l)
        let inst = fpf fvs (List.map (fun x -> Var x) newvars)
        let djs1 = distrib (image (image (subst inst)) djs0) djs
        try unify_refute djs1 undefined,(n + 1) with 
        | Failure _ -> prawitz_loop djs0 fvs djs1 (n + 1)

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

    let rec tableau (fms,lits,n) cont (env,k) =
        if n < 0 then failwith "no proof at this level" 
        else
            match fms with
            | [] -> failwith "tableau: no proof"
            | And (p, q) :: unexp ->
                tableau (p :: q :: unexp, lits, n) cont (env, k)
            | Or (p, q) :: unexp ->
                tableau (p :: unexp, lits, n) (tableau (q :: unexp, lits, n) cont) (env, k)
            | Forall (x, p) :: unexp ->
                let y = Var ("_" + string k)
                let p' = subst (x |=> y) p
                tableau (p' :: unexp @ [Forall (x, p)], lits, n - 1) cont (env, k + 1)
            | fm :: unexp ->
                let rec tryfind f l =
                    match l with
                    | []     -> failwith "tryfind"
                    | h::t -> 
                        try f h
                        with _ ->
                            tryfind f t
                try lits |> tryfind (fun l ->
                    cont (unify_complements env (fm, l), k))
                with _ ->
                    tableau (unexp, fm :: lits, n) cont (env, k)

    let rec deepen f n =
        try printf "Searching with depth limit "
            printfn "%d" n
            f n
        with _ ->
            deepen f (n + 1)
        
    let tabrefute fms =
        deepen (fun n -> tableau (fms, [], n) id (undefined, 0) |> ignore; n) 0

    let tab fm =
        let sfm = askolemize (Not (generalize fm))
        if sfm = False then 0 else tabrefute [sfm]

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

