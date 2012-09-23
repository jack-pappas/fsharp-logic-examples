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

module qelim =
    open intro
    open formulas
    open prop
    open defcnf
    open dp
    open stal
    open bdd
    open folMod
    open skolem
    open herbrand
    open unif
    open tableaux
    open resolution
    open prolog
    open meson
    open skolems
    open equal
    open cong
    open rewrite
    open order
    open completion
    open eqelim
    open paramodulation
    open decidable

//  ========================================================================= // 
//  Introduction to quantifier elimination.                                   // 
//                                                                            // 
//  Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  // 
//  ========================================================================= // 

// pg. 331
//  ------------------------------------------------------------------------- // 
//  Lift procedure given literal modifier, formula normalizer, and a  basic   // 
//  elimination procedure for existential formulas with conjunctive body.     // 
//  ------------------------------------------------------------------------- // 

    // OCaml : val qelim : (fol formula -> fol formula) -> string -> fol formula -> fol formula = <fun>
    // F#:     val qelim : (fol formula -> fol formula) -> string -> fol formula -> fol formula
    let qelim bfn x p =
        let cjs = conjuncts p
        let ycjs, ncjs = List.partition (mem x >>|> fv) cjs
        if ycjs = [] then p
        else
            let q = bfn (Exists (x, list_conj ycjs))
            List.foldBack mk_and ncjs q

//    // OCaml : val lift_qelim : (string list -> fol formula -> fol formula) -> (fol formula -> fol formula) -> (string list -> fol formula -> fol formula) -> fol formula -> fol formula = <fun>
//    // F# :    val lift_qelim : (string list -> fol formula -> fol formula) -> (fol formula -> fol formula) -> (string list -> fol formula -> fol formula) -> (fol formula -> fol formula)
//    // pg. 332
//    let lift_qelim afn nfn qfn =
//      let rec qelift vars fm =
//        match fm with
//        | Atom(R(_,_)) -> afn vars fm
//        | Not(p) -> Not(qelift vars p)
//        | And(p,q) -> And(qelift vars p,qelift vars q)
//        | Or(p,q) -> Or(qelift vars p,qelift vars q)
//        | Imp(p,q) -> Imp(qelift vars p,qelift vars q)
//        | Iff(p,q) -> Iff(qelift vars p,qelift vars q)
//        | Forall(x,p) -> Not(qelift vars (Exists(x,Not p)))
//        | Exists(x,p) ->
//              let djs = disjuncts(nfn(qelift (x::vars) p))
//              list_disj(List.map (qelim (qfn vars) x) djs)
//        | _ -> fm
//      fun fm -> simplify(qelift (fv fm) (miniscope fm))

    // OCaml : val lift_qelim : (string list -> fol formula -> fol formula) -> (fol formula -> fol formula) -> (string list -> fol formula -> fol formula) -> fol formula -> fol formula = <fun>
    // F# :    val lift_qelim : (string list -> fol formula -> fol formula) -> (fol formula -> fol formula) -> (string list -> fol formula -> fol formula) -> (fol formula -> fol formula)
    // pg. 332
    let lift_qelim afn nfn qfn =
        let rec qelift vars fm =
            match fm with
            | Atom (R (_,_)) ->
                afn vars fm
            | Not p ->
                Not (qelift vars p)
            | And (p, q) ->
                And (qelift vars p, qelift vars q)
            | Or (p, q) ->
                Or (qelift vars p, qelift vars q)
            | Imp (p, q) ->
                Imp (qelift vars p, qelift vars q)
            | Iff (p, q) ->
                Iff (qelift vars p, qelift vars q)
            | Forall (x, p) ->
                Not (qelift vars (Exists (x, Not p)))
            | Exists (x, p) ->
                  let djs = disjuncts (nfn (qelift (x :: vars) p))
                  list_disj (List.map (qelim (qfn vars) x) djs)
            | _ -> fm

        fun fm ->
            simplify (qelift (fv fm) (miniscope fm))
  
// pg. 333
//  ------------------------------------------------------------------------- // 
//  Cleverer (proposisional) NNF with conditional and literal modification.   // 
//  ------------------------------------------------------------------------- // 

    // OCaml : val cnnf : (fol formula -> fol formula) -> fol formula -> fol formula = <fun>
    // F# :    val cnnf : (fol formula -> fol formula) -> (fol formula -> fol formula)
    let cnnf lfn =
        let rec cnnf fm =
            match fm with
            | And (p, q) ->
                And (cnnf p, cnnf q)
            | Or (p, q) ->
                Or (cnnf p, cnnf q)
            | Imp (p, q) ->
                Or (cnnf(Not p), cnnf q)
            | Iff (p, q) ->
                Or (And (cnnf p, cnnf q), And (cnnf (Not p), cnnf (Not q)))
            | Not (Not p) ->
                cnnf p
            | Not (And (p, q)) ->
                Or (cnnf (Not p), cnnf (Not q))
            | Not (Or (And (p, q), And (p', r))) when p' = negate p ->
                Or (cnnf (And (p, Not q)), cnnf (And (p', Not r)))
            | Not (Or (p, q)) ->
                And (cnnf (Not p), cnnf (Not q))
            | Not (Imp (p, q)) ->
                And (cnnf p, cnnf (Not q))
            | Not (Iff (p, q)) ->
                Or (And (cnnf p, cnnf (Not q)), And (cnnf (Not p), cnnf q))
            | _ -> lfn fm
        simplify >>|> cnnf >>|> simplify
  
// pg. 334
//  ------------------------------------------------------------------------- // 
//  Initial literal simplifier and intermediate literal modifier.             // 
//  ------------------------------------------------------------------------- // 

    // OCaml : val lfn_dlo : fol formula -> fol formula = <fun>
    // F# :    val lfn_dlo : fol formula -> fol formula
    let lfn_dlo fm =
        match fm with
        | Not (Atom (R ("<", [s; t]))) ->
            Or (Atom (R ("=", [s; t])), Atom (R ("<", [t; s])))
        | Not (Atom (R ("=", [s; t]))) ->
            Or (Atom (R ("<", [s; t])), Atom (R ("<", [t; s])))
        | _ -> fm
  
// pg. 335
//  ------------------------------------------------------------------------- // 
//  Simple example of dense linear orderings; this is the base function.      // 
//  ------------------------------------------------------------------------- // 

    // OCaml : val dlobasic : fol formula -> fol formula = <fun>
    // F# :    val dlobasic : fol formula -> fol formula
    // Note: List.find throws expcetion it does not return failure
    //       so "try with failure" will not work with List.find
    let dlobasic fm =
        match fm with
        | Exists (x, p) ->
            let cjs = subtract (conjuncts p) [Atom (R ("=", [Var x; Var x]))]
            try
                let eqn = List.find is_eq cjs
                let s, t = dest_eq eqn
                let y = if s = Var x then t else s
                list_conj (List.map (subst (x |=> y)) (subtract cjs [eqn]))
            with 
            | :? System.Collections.Generic.KeyNotFoundException ->
                if mem (Atom (R ("<", [Var x; Var x]))) cjs then False
                else
                    let lefts, rights = List.partition (fun (Atom (R ("<", [s; t]))) -> t = Var x) cjs
                    let ls = List.map (fun (Atom (R ("<", [l;_]))) -> l) lefts
                    let rs = List.map (fun (Atom (R ("<", [_;r]))) -> r) rights
                    list_conj (allpairs (fun l r -> Atom (R ("<", [l; r]))) ls rs)
        | _ -> failwith "dlobasic"

// pg. 335
//  ------------------------------------------------------------------------- // 
//  Overall quelim procedure.                                                 // 
//  ------------------------------------------------------------------------- // 

    // OCaml : val afn_dlo : 'a -> fol formula -> fol formula = <fun>
    // F# :    val afn_dlo : 'a -> fol formula -> fol formula
    let afn_dlo vars fm =
        match fm with
        | Atom (R ("<=", [s; t])) ->
            Not (Atom (R ("<", [t; s])))
        | Atom (R (">=", [s; t])) ->
            Not (Atom (R ("<", [s; t])))
        | Atom (R (">", [s; t])) ->
            Atom (R ("<", [t; s]))
        | _ -> fm

    // OCaml : val quelim_dlo : fol formula -> fol formula = <fun>
    // F# :    val quelim_dlo : (fol formula -> fol formula)
    let quelim_dlo =
        lift_qelim afn_dlo (dnf >>|> cnnf lfn_dlo) (fun v -> dlobasic)


