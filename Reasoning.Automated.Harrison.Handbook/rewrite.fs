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

module rewrite =
    open formulas
    open folMod
    open resolution

//
// ========================================================================= //
// Rewriting.                                                                //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //
//
// pg. 262
// ------------------------------------------------------------------------- //
// Rewriting at the top level with first of list of equations.               //
// ------------------------------------------------------------------------- //

    let rec rewrite1 eqs t =
        match eqs with
        | Atom (R ("=", [l; r])) :: oeqs -> 
            try 
                tsubst (term_match undefined [l, t]) r
            with _ ->
                rewrite1 oeqs t
        | _ -> failwith "rewrite1"

// pg. 263
// ------------------------------------------------------------------------- //
// Rewriting repeatedly and at depth (top-down).                             //
// ------------------------------------------------------------------------- //

    // TODO : Optimize using continuation-passing style.
    let rec rewrite eqs tm =
        try rewrite eqs (rewrite1 eqs tm)
        with _ ->
            match tm with
            | Var x -> tm
            | Fn (f, args) -> 
                let tm' = Fn (f, List.map (rewrite eqs) args)
                if tm' = tm then tm 
                else rewrite eqs tm'
                
// ------------------------------------------------------------------------- //
// Note that ML doesn't accept nonlinear patterns.                           //
// ------------------------------------------------------------------------- //
//
//********** Point being that CAML doesn't accept nonlinear patterns
//
//function (x,x) -> 0
//
// *********** Actually fun x x -> 0 works, but the xs seem to be
// *********** considered distinct
// *********//
