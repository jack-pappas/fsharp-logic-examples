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

module paramodulation =
    open formulas
    open prop
    open folMod
    open skolem
    open resolution
    open equal
    open completion

// ========================================================================= //
// Paramodulation.                                                           //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

// pg. 301
// ------------------------------------------------------------------------- //
// Find paramodulations with l = r inside a literal fm.                      //
// ------------------------------------------------------------------------- //

    let rec overlapl (l, r) fm rfn =
        match fm with
        | Atom (R (f, args)) ->
            listcases (overlaps (l, r)) (fun i a -> rfn i (Atom (R (f, a)))) args []
        | Not p ->
            overlapl (l,r) p (fun i p -> rfn i (Not p))
        | _ -> failwith "overlapl: not a literal"
  
// pg. 301
// ------------------------------------------------------------------------- //
// Now find paramodulations within a clause.                                 //
// ------------------------------------------------------------------------- //

    let overlapc (l, r) cl rfn acc =
        listcases (overlapl (l, r)) rfn cl acc

// pg. 301
// ------------------------------------------------------------------------- //
// Overall paramodulation of ocl by equations in pcl.                        //
// ------------------------------------------------------------------------- //

    let paramodulate pcl ocl =
        itlist (fun eq ->
            let pcl' = subtract pcl [eq]
            let l, r = dest_eq eq
            let rfn i ocl' = image (subst i) (pcl' @ ocl')
            overlapc (l, r) ocl rfn >>|> overlapc (r, l) ocl rfn)
            (List.filter is_eq pcl) []

    let para_clauses cls1 cls2 =
        let cls1' = rename "x" cls1
        let cls2' = rename "y" cls2
        paramodulate cls1' cls2' @ paramodulate cls2' cls1'
  
// pg. 302
// ------------------------------------------------------------------------- //
// Incorporation into resolution loop.                                       //
// ------------------------------------------------------------------------- //

    let rec paraloop (used, unused) =
        match unused with
        | cls::ros ->
            printf "%s" (string(List.length used) + " used; " + string(List.length unused) + " unused.");
            printfn "";
            let used' = insert cls used
            let news =
                itlist (@) (mapfilter (resolve_clauses cls) used')
                    (itlist (@) (mapfilter (para_clauses cls) used') [])
            if mem [] news then true 
            else
                paraloop (used', itlist (incorporate cls) news ros)

    let pure_paramodulation fm =
      paraloop ([], [mk_eq (Var "x") (Var "x")] :: simpcnf (specialize (pnf fm)))

    let paramodulation fm =
      let fm1 = askolemize (Not (generalize fm))
      List.map (pure_paramodulation >>|> list_conj) (simpdnf fm1)
