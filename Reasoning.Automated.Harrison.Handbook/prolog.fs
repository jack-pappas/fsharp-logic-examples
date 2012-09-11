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

module prolog =

    open lib
    open intro
    open formulas
    open prop
//    open propexamples
//    open defcnf 
//    open dp
//    open stal
//    open bdd
    open folMod
    open skolem
//    open herbrand
    open unif
    open tableaux
//    open resolution

// ========================================================================= //
// Backchaining procedure for Horn clauses, and toy Prolog implementation.   //
// ========================================================================= //

// pg. 207
// ------------------------------------------------------------------------- //
// Rename a rule.                                                            //
// ------------------------------------------------------------------------- //

    let renamerule k (asm,c) =
        let fvs = fv(list_conj(c::asm))
        let n = List.length fvs
        let vvs = List.map (fun i -> "_" + string i) (k -- (k+n-1))
        let inst = subst(fpf fvs (List.map (fun x -> Var x) vvs))
        (List.map inst asm,inst c),k+n
        
// pg. 207
// ------------------------------------------------------------------------- //
// Basic prover for Horn clauses based on backchaining with unification.     //
// ------------------------------------------------------------------------- //

    let rec backchain rules n k env goals =
        match goals with
        [] -> env
        | g::gs ->
            if n = 0 then failwith "Too deep" 
            else
                let rec tryfind f l =
                    match l with
                    | []     -> failwith "tryfind"
                    | (h::t) -> try f h with Failure _ -> tryfind f t
                tryfind (
                    fun rule ->
                        let (a,c),k' = 
                            renamerule k rule
                        backchain rules (n - 1) k' (unify_literals env (c,g)) (a @ gs))
                        rules

    let hornify cls =
        let pos,neg = List.partition positive cls
        if List.length pos > 1 then failwith "non-Horn clause"
        else (List.map negate neg,if pos = [] then False else List.head pos)

    let hornprove fm =
        let rules = List.map hornify (simpcnf(skolemize(Not(generalize fm))))
        deepen (fun n -> backchain rules n 0 undefined [False],n) 0

// pg. 210
// ------------------------------------------------------------------------- //
// Parsing rules in a Prolog-like syntax.                                    //
// ------------------------------------------------------------------------- //

    let parserule s =
        let c,rest =
            parse_formula (parse_infix_atom,parse_atom) [] (lex(explode s))
        let asm,rest1 =
            if rest <> [] && List.head rest = ":-"
            then parse_list ","
                    (parse_formula (parse_infix_atom,parse_atom) []) (List.tail rest)
            else [],rest
        if rest1 = [] then (asm,c) 
        else failwith "Extra material after rule"

// pg. 120
// ------------------------------------------------------------------------- //
// Prolog interpreter: just use depth-first search not iterative deepening.  //
// ------------------------------------------------------------------------- //

    let simpleprolog rules gl =
        backchain (List.map parserule rules) (-1) 0 undefined [parse gl]

// ------------------------------------------------------------------------- //
// With instantiation collection to produce a more readable result.          //
// ------------------------------------------------------------------------- //

    let prolog rules gl =
        let i = solve(simpleprolog rules gl) in
        mapfilter (fun x -> Atom(R("=",[Var x; apply i x]))) (fv(parse gl))                      


