//  Copyright (c) 2003-2007, John Harrison
//  All rights reserved.
//  
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the following disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the following disclaimer in the
//  IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
//  By downloading, copying, installing or using the software you agree
//  to this license.  If you do not agree to this license, do not
//  download, install, copy or use the software.
//  
//  Copyright (c) 2003-2007, John Harrison
//  All rights reserved.
//  
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the following disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the following disclaimer in the
//  documentation and/or other materials provided with the distribution.
//  
//  * The name of John Harrison may not be used to endorse or promote
//  products derived from this software without specific prior written
//  permission.
//  
//  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
//  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
//  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
//  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
//  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
//  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
//  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
//  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
//  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
//  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
//  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
//  SUCH DAMAGE.
// 
//  ===================================================================
// 
//  Converted to F# 2.0
// 
//  Copyright (c) 2012, Jack Pappas, Eric Taucher
//  All rights reserved.
// 
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the previous disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the previous disclaimer in the
//  documentation and/or other materials provided with the distribution.
//  
//  * The name of Eric Taucher may not be used to endorse or promote
//  products derived from this software without specific prior written
//  permission.
// 
//  ===================================================================

// ========================================================================= //
// LCF-style basis for Tarski-style Hilbert system of first order logic.     //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module lcf =

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
    open qelim
    open cooper
    open complex
    open real
    open grobner
    open geom
    open interpolation
    open combining

// pg. 474
// ------------------------------------------------------------------------- //
// Basic first order deductive system.                                       //
//                                                                           //
// This is based on Tarski's trick for avoiding use of a substitution        //
// primitive. It seems about the simplest possible system we could use.      //
//                                                                           //
//  if |- p ==> q and |- p then |- q                                         //
//  if |- p then |- forall x. p                                              //
//                                                                           //
//  |- p ==> (q ==> p)                                                       //
//  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           //
//  |- ((p ==> false) ==> false) ==> p                                       //
//  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               //
//  |- p ==> forall x. p                            [x not free in p]        //
//  |- exists x. x = t                              [x not free in t]        //
//  |- t = t                                                                 //
//  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             //
//  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           //
//                                                                           //
//  |- (p <=> q) ==> p ==> q                                                 //
//  |- (p <=> q) ==> q ==> p                                                 //
//  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 //
//  |- true <=> (false ==> false)                                            //
//  |- ~p <=> (p ==> false)                                                  //
//  |- p /\ q <=> (p ==> q ==> false) ==> false                              //
//  |- p \/ q <=> ~(~p /\ ~q)                                                //
//  |- (exists x. p) <=> ~(forall x. ~p)                                     //
// ------------------------------------------------------------------------- //

// module type Proofsystem =
//    sig type thm
//        val modusponens : thm -> thm -> thm
//        val gen : string -> thm -> thm
//        val axiom_addimp : fol formula -> fol formula -> thm
//        val axiom_distribimp :
//             fol formula -> fol formula -> fol formula -> thm
//        val axiom_doubleneg : fol formula -> thm
//        val axiom_allimp : string -> fol formula -> fol formula -> thm
//        val axiom_impall : string -> fol formula -> thm
//        val axiom_existseq : string -> term -> thm
//        val axiom_eqrefl : term -> thm
//        val axiom_funcong : string -> term list -> term list -> thm
//        val axiom_predcong : string -> term list -> term list -> thm
//        val axiom_iffimp1 : fol formula -> fol formula -> thm
//        val axiom_iffimp2 : fol formula -> fol formula -> thm
//        val axiom_impiff : fol formula -> fol formula -> thm
//        val axiom_true : thm6
//        val axiom_not : fol formula -> thm
//        val axiom_and : fol formula -> fol formula -> thm
//        val axiom_or : fol formula -> fol formula -> thm
//        val axiom_exists : string -> fol formula -> thm
//        val concl : thm -> fol formula
//    end;;

    // TODO : Change this to an interface (IProofSystem)
//    type IProofSystem<'thm> = interface
//        abstract member modusponens : 'thm -> 'thm -> 'thm
//        abstract member gen : string -> 'thm -> 'thm
//        abstract member axiom_addimp : formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_distribimp : formula<fol> -> formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_doubleneg : formula<fol> -> 'thm
//        abstract member axiom_allimp : string -> formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_impall : string -> formula<fol> -> 'thm
//        abstract member axiom_existseq : string -> term -> 'thm
//        abstract member axiom_eqrefl : term -> 'thm
//        abstract member axiom_funcong : string -> term list -> term list -> 'thm
//        abstract member axiom_predcong : string -> term list -> term list -> 'thm
//        abstract member axiom_iffimp1 : formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_iffimp2 : formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_impiff : formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_true : 'thm
//        abstract member axiom_not : formula<fol> -> 'thm
//        abstract member axiom_and : formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_or : formula<fol> -> formula<fol> -> 'thm
//        abstract member axiom_exists : string -> formula<fol> -> 'thm
//        abstract member concl : 'thm -> formula<fol>
//    end
    
    // ------------------------------------------------------------------------- //
    // Auxiliary functions.                                                      //
    // ------------------------------------------------------------------------- //

    let rec occurs_in s t =
        s = t ||
        match t with
        | Var y -> false
        | Fn (f, args) ->
            List.exists (occurs_in s) args

    let rec free_in t fm =
        match fm with
        | False
        | True ->
            false
        | Not p ->
            free_in t p
        | And (p, q)
        | Or (p, q)
        | Imp (p, q)
        | Iff (p, q) ->
            free_in t p
            || free_in t q
        | Forall (y, p)
        | Exists (y, p) ->
            not (occurs_in (Var y) t)
            && free_in t p
        | Atom (R (p, args)) ->
            List.exists (occurs_in t) args

    /// Implementation of the abstract data type of theorems.
//    type Proven = class
//        interface IProofSystem<formula<fol>> with
//            member __.modusponens pq p =
//                match pq with
//                | Imp (p', q) when p = p' -> q
//                | _ -> failwith "modusponens"
//
//            member __.gen x p =
//                Forall (x, p)
//
//            member __.axiom_addimp p q =
//                Imp (p,Imp (q, p))
//
//            member __.axiom_distribimp p q r =
//                Imp (Imp (p, Imp (q, r)), Imp (Imp (p, q), Imp (p, r)))
//
//            member __.axiom_doubleneg p =
//                Imp (Imp (Imp (p, False), False), p)
//
//            member __.axiom_allimp x p q =
//                Imp (Forall (x, Imp (p, q)), Imp (Forall (x, p), Forall (x, q)))
//
//            member __.axiom_impall x p =
//                if free_in (Var x) p then
//                    failwith "axiom_impall: variable free in formula"
//                else
//                    Imp (p, Forall (x, p))
//
//            member __.axiom_existseq x t =
//                if occurs_in (Var x) t then
//                    failwith "axiom_existseq: variable free in term"
//                else
//                    Exists (x, mk_eq (Var x) t)
//                
//            member __.axiom_eqrefl t =
//                mk_eq t t
//
//            member __.axiom_funcong f lefts rights =
//                itlist2 (fun s t p -> Imp (mk_eq s t, p)) lefts rights
//                    (mk_eq (Fn (f, lefts)) (Fn (f, rights)))
//
//            member __.axiom_predcong p lefts rights =
//                itlist2 (fun s t p -> Imp (mk_eq s t, p)) lefts rights
//                    (Imp (Atom (R (p, lefts)), Atom (R (p, rights))))
//
//            member __.axiom_iffimp1 p q =
//                Imp (Iff (p, q), Imp (p, q))
//
//            member __.axiom_iffimp2 p q =
//                Imp (Iff (p, q), Imp (q, p))
//
//            member __.axiom_impiff p q =
//                Imp (Imp (p, q), Imp (Imp (q, p), Iff (p, q)))
//
//            member __.axiom_true =
//                Iff (True, Imp (False, False))
//
//            member __.axiom_not p =
//                Iff (Not p, Imp (p, False))
//
//            member __.axiom_and p q =
//                Iff (And (p, q), Imp (Imp (p, Imp (q, False)), False))
//
//            member __.axiom_or p q =
//                Iff (Or (p, q), Not (And (Not p, Not q)))
//
//            member __.axiom_exists x p =
//                Iff (Exists (x, p), Not (Forall (x, Not p)))
//
//            member __.concl c = c
//      end

    // TEMP : Until we modify the consuming code to use functions which are parameterized
    // by an instance of IProofSystem (so they don't just rely on the functions being in scope).
    [<AutoOpen>]
    module ProverOperators =
        type thm = formula<fol>

        let modusponens (pq : thm) (p : thm) : thm =
            match pq with
            | Imp (p', q) when p = p' -> q
            | _ -> failwith "modusponens"

        let gen x (p : thm) : thm =
            Forall (x, p)

        let axiom_addimp p q : thm =
            Imp (p,Imp (q, p))

        let axiom_distribimp p q r : thm =
            Imp (Imp (p, Imp (q, r)), Imp (Imp (p, q), Imp (p, r)))

        let axiom_doubleneg p : thm =
            Imp (Imp (Imp (p, False), False), p)

        let axiom_allimp x p q : thm =
            Imp (Forall (x, Imp (p, q)), Imp (Forall (x, p), Forall (x, q)))

        let axiom_impall x p : thm =
            if free_in (Var x) p then
                failwith "axiom_impall: variable free in formula"
            else
                Imp (p, Forall (x, p))

        let axiom_existseq x t : thm =
            if occurs_in (Var x) t then
                failwith "axiom_existseq: variable free in term"
            else
                Exists (x, mk_eq (Var x) t)
                
        let axiom_eqrefl t : thm =
            mk_eq t t

        let axiom_funcong f lefts rights : thm =
            itlist2 (fun s t p -> Imp (mk_eq s t, p)) lefts rights
                (mk_eq (Fn (f, lefts)) (Fn (f, rights)))

        let axiom_predcong p lefts rights : thm =
            itlist2 (fun s t p -> Imp (mk_eq s t, p)) lefts rights
                (Imp (Atom (R (p, lefts)), Atom (R (p, rights))))

        let axiom_iffimp1 p q : thm =
            Imp (Iff (p, q), Imp (p, q))

        let axiom_iffimp2 p q : thm =
            Imp (Iff (p, q), Imp (q, p))

        let axiom_impiff p q : thm =
            Imp (Imp (p, q), Imp (Imp (q, p), Iff (p, q)))

        let axiom_true : thm =
            Iff (True, Imp (False, False))

        let axiom_not p : thm =
            Iff (Not p, Imp (p, False))

        let axiom_and p q : thm =
            Iff (And (p, q), Imp (Imp (p, Imp (q, False)), False))

        let axiom_or p q : thm =
            Iff (Or (p, q), Not (And (Not p, Not q)))

        let axiom_exists x p : thm =
            Iff (Exists (x, p), Not (Forall (x, Not p)))

        let concl (c : thm) : formula<fol> = c

    // ------------------------------------------------------------------------- //
    // A printer for theorems.                                                   //
    // ------------------------------------------------------------------------- //

//    include Proven;;

    let print_thm th =
//        open_box 0
        printfn "|-"
//        print_space ()
//        open_box 0
        print_formula print_atom (concl th)
//        close_box ()
//        close_box ()

    //#install_printer print_thm;;
