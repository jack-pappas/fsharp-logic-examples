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

module defcnf =
    open intro
    open formulas
    open prop

// ========================================================================= //
// Definitional CNF.                                                         //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

// pg. 75
// ------------------------------------------------------------------------- //
// Make a stylized variable and update the index.                            //
// ------------------------------------------------------------------------- //

    let mkprop n = Atom(P("p_" + (string n))), n + 1

// pg. 75
// ------------------------------------------------------------------------- //
// Core definitional CNF procedure.                                          //
// ------------------------------------------------------------------------- //

    let rec maincnf (fm,defs,n as trip) =
        match fm with
        | And(p,q) -> defstep mk_and (p,q) trip
        | Or(p,q) -> defstep mk_or (p,q) trip
        | Iff(p,q) -> defstep mk_iff (p,q) trip
        | _ -> trip

    and defstep op (p,q) (fm,defs,n) =
        let fm1,defs1,n1 = maincnf (p,defs,n)
        let fm2,defs2,n2 = maincnf (q,defs1,n1)
        let fm' = op fm1 fm2
        try (fst(apply defs2 fm'),defs2,n2) with 
        | Failure _ -> 
            let v,n3 = mkprop n2 
            (v,(fm'|->(v,Iff(v,fm'))) defs2,n3)

// pg. 76
// ------------------------------------------------------------------------- //
// Make n large enough that "v_m" won't clash with s for any m >= n          //
// ------------------------------------------------------------------------- //

    let max_varindex pfx =
        let m = String.length pfx
        fun s n ->
            let l = String.length s
            if l <= m || s.[0..m] <> pfx then n else
            let s' = s.[m.. (l - m)]
            if List.forall numeric (explode s') then max n (int s')
            else n

// pg. 77
// ------------------------------------------------------------------------- //
// Overall definitional CNF.                                                 //
// ------------------------------------------------------------------------- //

    let mk_defcnf fn fm =
        let fm' = nenf fm
        let n = int 1 + overatoms (max_varindex "p_" ** pname) fm' (int 0)
        let (fm'',defs,_) = fn (fm',undefined,n)
        let deflist = List.map (snd ** snd) (graph defs)
        unions(simpcnf fm'' :: List.map simpcnf deflist)

    // Note: added space after list_disj
    let defcnfOrig fm = list_conj(List.map list_disj (mk_defcnf maincnf fm))

// pg. 78
// ------------------------------------------------------------------------- //
// Version tweaked to exploit initial structure.                             //
// ------------------------------------------------------------------------- //

    let subcnf sfn op (p,q) (fm,defs,n) =
        let fm1,defs1,n1 = sfn(p,defs,n)
        let fm2,defs2,n2 = sfn(q,defs1,n1) 
        (op fm1 fm2,defs2,n2)

    let rec orcnf (fm,defs,n as trip) =
        match fm with
        | Or(p,q) -> subcnf orcnf mk_or (p,q) trip
        | _       -> maincnf trip

    let rec andcnf (fm,defs,n as trip) =
        match fm with
        | And(p,q) -> subcnf andcnf mk_and (p,q) trip
        | _        -> orcnf trip

    let defcnfs fm = mk_defcnf andcnf fm

    let defcnf fm = list_conj (List.map list_disj (defcnfs fm))

// pg. 78
// ------------------------------------------------------------------------- //
// Version that guarantees 3-CNF.                                            //
// ------------------------------------------------------------------------- //

    let rec andcnf3 (fm,defs,n as trip) =
        match fm with
        | And(p,q) -> subcnf andcnf3 mk_and (p,q) trip
        | _        -> maincnf trip

    // Note: added space after list_disj
    let defcnf3 fm = list_conj (List.map list_disj (mk_defcnf andcnf3 fm))


