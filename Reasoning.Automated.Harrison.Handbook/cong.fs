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

module cong =
    open formulas
    open prop
    open folMod
    open skolem
    open equal
//
// pg. 249
// ========================================================================= //
// Simple congruence closure.                                                //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

    let rec subterms tm =
        match tm with
        | Fn (f, args) ->
            itlist (union >>|> subterms) args [tm]
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
            itlist (fun (u, v) (eqv, pfn) ->
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
            itlist (fun s f -> (s |-> insert t (tryapplyl f s)) f) (setify a) pfn
        | _ -> pfn

    let ccsatisfiable fms =
        let pos, neg = List.partition positive fms
        let eqps = List.map dest_eq pos 
        let eqns = List.map (dest_eq >>|> negate) neg        
        let pfn =
            let lrs =
                List.map fst eqps
                @ List.map snd eqps
                @ List.map fst eqns
                @ List.map snd eqns
            itlist predecessors (unions (List.map subterms lrs)) undefined
        let eqv, _ = itlist emerge eqps (unequal, pfn)
        List.forall (fun (l, r) ->
            not <| equivalent eqv l r) eqns

// pg. 253
// ------------------------------------------------------------------------- //
// Validity checking a universal formula.                                    //
// ------------------------------------------------------------------------- //

    let ccvalid fm =
        let fms = simpdnf (askolemize (Not (generalize fm)))
        not (List.exists ccsatisfiable fms)
