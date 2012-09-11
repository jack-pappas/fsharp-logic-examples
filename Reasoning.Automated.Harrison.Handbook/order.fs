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

module order =

    open lib
//    open intro
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
//    open unif
//    open tableaux
//    open resolution
//    open prolog
//    open meson
//    open skolems
//    open equal
//    open cong
//    open rewrite

// pg. 265
// ========================================================================= //
// Term orderings.                                                           //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

    let rec termsize tm =
        match tm with
        | Var x -> 1
        | Fn(f,args) -> itlist (fun t n -> termsize t + n) args 1

// pg. 267
// ------------------------------------------------------------------------- //
// Lexicographic path order.                                                 //
// ------------------------------------------------------------------------- //

    let rec lexord ord l1 l2 =
        match (l1,l2) with
        | (h1::t1,h2::t2) -> 
            if ord h1 h2 then List.length t1 = List.length t2
            else h1 = h2 && lexord ord t1 t2
        | _ -> false

    let rec lpo_gt w s t =
        match (s,t) with
        | (_,Var x) ->
            not(s = t) && mem x (fvt s)
        | (Fn(f,fargs),Fn(g,gargs)) ->
            List.exists (fun si -> lpo_ge w si t) fargs ||
            List.forall (lpo_gt w s) gargs &&
            (f = g && lexord (lpo_gt w) fargs gargs ||
                w (f,List.length fargs) (g,List.length gargs))
        | _ -> false

    and lpo_ge w s t = (s = t) || lpo_gt w s t

// pg. 267
// ------------------------------------------------------------------------- //
// More convenient way of specifying weightings.                             //
// ------------------------------------------------------------------------- //

    let weight lis (f,n) (g,m) = if f = g then n > m else earlier lis g f


