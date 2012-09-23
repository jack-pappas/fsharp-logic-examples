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

module equal =
    open formulas
    open folMod
    open skolem

//
// pg. 235
// ========================================================================= //
// First order logic with equality.                                          //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

    let is_eq = function 
        | Atom (R ("=", _)) -> true 
        | _ -> false

    let mk_eq s t =
        Atom (R ("=", [s; t]))

    let dest_eq fm =
        match fm with
        | Atom (R ("=", [s;t])) ->
            s, t
        | _ ->
            failwith "dest_eq: not an equation"

    let lhs eq = fst <| dest_eq eq
    let rhs eq = snd <| dest_eq eq

// pg. 239
// ------------------------------------------------------------------------- //
// The set of predicates in a formula.                                       //
// ------------------------------------------------------------------------- //

    let rec predicates fm =
        atom_union (fun (R (p, a)) -> [p, List.length a]) fm

// pg. 239
// ------------------------------------------------------------------------- //
// Code to generate equality axioms for functions.                           //
// ------------------------------------------------------------------------- //

    let function_congruence (f, n) =
        if n = 0 then [] 
        else
            let argnames_x = List.map (fun n -> "x" + (string n)) (1 -- n)
            let argnames_y = List.map (fun n -> "y" + (string n)) (1 -- n)
            let args_x = List.map (fun x -> Var x) argnames_x
            let args_y = List.map (fun x -> Var x) argnames_y
            let ant = end_itlist mk_and (List.map2 mk_eq args_x args_y)
            let con = mk_eq (Fn (f, args_x)) (Fn (f, args_y))
            [List.foldBack mk_forall (argnames_x @ argnames_y) (Imp (ant, con))]

// pg. 240
// ------------------------------------------------------------------------- //
// And for predicates.                                                       //
// ------------------------------------------------------------------------- //

    let predicate_congruence (p, n) =
        if n = 0 then []
        else
            let argnames_x = List.map (fun n -> "x" + (string n)) (1 -- n)
            let argnames_y = List.map (fun n -> "y" + (string n)) (1 -- n)
            let args_x = List.map (fun x -> Var x) argnames_x
            let args_y = List.map (fun x -> Var x) argnames_y
            let ant = end_itlist mk_and (List.map2 mk_eq args_x args_y)
            let con = Imp (Atom (R (p, args_x)), Atom (R (p, args_y)))
            [List.foldBack mk_forall (argnames_x @ argnames_y) (Imp (ant, con))]

// pg. 240
// ------------------------------------------------------------------------- //
// Hence implement logic with equality just by adding equality "axioms".     //
// ------------------------------------------------------------------------- //

    let equivalence_axioms =
        [(parse "forall x. x = x"); (parse "forall x y z. x = y /\ x = z ==> y = z")]

    let equalitize fm =
        let allpreds = predicates fm
        if not (mem ("=", 2) allpreds) then fm
        else
            let preds = subtract allpreds ["=", 2]
            let funcs = functions fm
            let axioms = List.foldBack (union >>|> function_congruence) funcs
                                (List.foldBack (union >>|> predicate_congruence) preds
                                        equivalence_axioms)
            Imp (end_itlist mk_and axioms, fm)
