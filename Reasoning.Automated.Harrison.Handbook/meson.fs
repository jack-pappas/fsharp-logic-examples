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

module meson =
    open formulas
    open prop
    open folMod
    open skolem
    open tableaux
    open prolog

// ========================================================================= //
// Model elimination procedure (MESON version, based on Stickel's PTTP).     //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //
//
// pg. 219
// ------------------------------------------------------------------------- //
// Generation of contrapositives.                                            //
// ------------------------------------------------------------------------- //

    let contrapositives cls =
        let baseClause = List.map (fun c -> List.map negate (subtract cls [c]),c) cls
        if List.forall negative cls then (List.map negate cls,False)::baseClause 
        else baseClause

// pg. 220
// ------------------------------------------------------------------------- //
// The core of MESON: ancestor unification or Prolog-style extension.        //
// ------------------------------------------------------------------------- //

    let rec mexpand001 rules ancestors g cont (env,n,k) =
        if n < 0 then failwith "Too deep" 
        else
            let rec tryfind f l =
                match l with
                | [] -> failwith "tryfind"
                | h :: t ->
                    try f h
                    with _ ->
                        tryfind f t
            try 
                tryfind (fun a -> cont (unify_literals env (g, negate a), n, k)) ancestors
            with _ -> 
                tryfind (fun rule -> 
                    let (asm, c) ,k' = renamerule k rule
                    itlist (mexpand001 rules (g :: ancestors)) asm cont
                        (unify_literals env (g, c), n - List.length asm, k'))
                    rules
                    
// pg. 220
// ------------------------------------------------------------------------- //
// Full MESON procedure.                                                     //
// ------------------------------------------------------------------------- //

    let puremeson001 fm =
        let cls = simpcnf(specialize(pnf fm))
        let rules = itlist ((@) >>|> contrapositives) cls []
        deepen (fun n -> mexpand001 rules [] False (fun x -> x) (undefined,n,0) |> ignore; n) 0

    let meson001 fm =
        let fm1 = askolemize(Not(generalize fm))
        List.map (puremeson001 >>|> list_conj) (simpdnf fm1)

// pg. 221
// ------------------------------------------------------------------------- //
// With repetition checking and divide-and-conquer search.                   //
// ------------------------------------------------------------------------- //

    let rec equal env fm1 fm2 =
        try unify_literals env (fm1,fm2) = env
        with _ -> false

    let expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
        expfn goals1 (fun (e1,r1,k1) ->
            expfn goals2 (fun (e2,r2,k2) ->
                            if n2 + r1 <= n3 + r2 then failwith "pair"
                            else cont(e2,r2,k2))
                    (e1,n2+r1,k1))
            (env,n1,k)

    let rec mexpand002 rules ancestors g cont (env,n,k) =

        let rec mexpands002 rules ancestors gs cont (env,n,k) =
            if n < 0 then failwith "Too deep" 
            else
                let m = List.length gs
                if m <= 1 then itlist (mexpand002 rules ancestors) gs cont (env,n,k) 
                else
                    let n1 = n / 2
                    let n2 = n - n1
                    let goals1,goals2 = chop_list (m / 2) gs
                    let expfn = expand2 (mexpands002 rules ancestors)
                    try expfn goals1 n1 goals2 n2 -1 cont env k
                    with _ -> expfn goals2 n1 goals1 n2 n1 cont env k

        if n < 0 then
            failwith "Too deep"
        elif List.exists (equal env g) ancestors then
            failwith "repetition" 
        else
            let rec tryfind f l =
                match l with
                | [] -> failwith "tryfind"
                | h :: t ->
                    try f h
                    with _ -> tryfind f t
            try tryfind (fun a -> cont (unify_literals env (g, negate a), n, k)) ancestors with 
            | Failure _ -> 
                tryfind (fun r -> 
                    let (asm, c), k' = renamerule k r 
                    mexpands002 rules (g :: ancestors) asm cont (unify_literals env (g, c), n - List.length asm, k')) 
                    rules

    let puremeson002 fm =   
        let cls = simpcnf (specialize (pnf fm))
        let rules = itlist ((@) >>|> contrapositives) cls []
        deepen (fun n -> mexpand002 rules [] False id (undefined, n, 0) |> ignore; n) 0

    let meson002 fm =
        let fm1 = askolemize (Not (generalize fm))
        List.map (puremeson002 >>|> list_conj) (simpdnf fm1)