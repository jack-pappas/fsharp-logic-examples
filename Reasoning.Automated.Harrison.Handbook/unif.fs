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

module unif =

    open lib
    open intro
//    open formulas
//    open prop
//    open propexamples
//    open defcnf 
//    open dp
//    open stal
//    open bdd
    open folMod
//    open skolem
//    open herbrand

// pg. 167
// ========================================================================= //
// Unification for first order terms.                                        //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

    let rec istriv env x t =
        match t with
        | Var y ->
            y = x
            || defined env y
            && istriv env x (apply env y)
        | Fn(f,args) ->
            if List.exists (istriv env x) args then true
            else
                failwith "cyclic"
        
// ------------------------------------------------------------------------- //
// Main unification procedure                                                //
// ------------------------------------------------------------------------- //

    let rec unify (env : func<string, term>) eqs =
        match eqs with
        | [] -> env
        | (Fn(f,fargs),Fn(g,gargs))::oth ->
            if f = g && List.length fargs = List.length gargs
            then unify env (List.zip fargs gargs @ oth)
            else failwith "impossible unification"
        | (Var x,t)::oth | (t,Var x)::oth ->
            if defined env x then unify env ((apply env x,t)::oth)
            else unify (if istriv env x t then env else (x |-> t) env) oth

// pg. 169
// ------------------------------------------------------------------------- //
// Solve to obtain a single instantiation.                                   //
// ------------------------------------------------------------------------- //

    let rec solve env =
        let env' = mapf (tsubst env) env
        if env' = env then env 
        else solve env'

// pg. 171
// ------------------------------------------------------------------------- //
// Unification reaching a final solved form (often this isn't needed).       //
// ------------------------------------------------------------------------- //

    let fullunify eqs = solve (unify undefined eqs)

// pg. 171
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

    let unify_and_apply eqs =
        let i = fullunify eqs
        let apply (t1,t2) = tsubst i t1,tsubst i t2
        List.map apply eqs



    

