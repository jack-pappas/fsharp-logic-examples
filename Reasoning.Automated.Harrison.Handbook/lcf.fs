// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Jack Pappas, Eric Taucher                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// LCF-style basis for Tarski-style Hilbert system of first order logic.     //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.lcf

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


(*
module type Proofsystem =
    sig type thm
        val modusponens : thm -> thm -> thm
        val gen : string -> thm -> thm
        val axiom_addimp : fol formula -> fol formula -> thm
        val axiom_distribimp :
             fol formula -> fol formula -> fol formula -> thm
        val axiom_doubleneg : fol formula -> thm
        val axiom_allimp : string -> fol formula -> fol formula -> thm
        val axiom_impall : string -> fol formula -> thm
        val axiom_existseq : string -> term -> thm
        val axiom_eqrefl : term -> thm
        val axiom_funcong : string -> term list -> term list -> thm
        val axiom_predcong : string -> term list -> term list -> thm
        val axiom_iffimp1 : fol formula -> fol formula -> thm
        val axiom_iffimp2 : fol formula -> fol formula -> thm
        val axiom_impiff : fol formula -> fol formula -> thm
        val axiom_true : thm6
        val axiom_not : fol formula -> thm
        val axiom_and : fol formula -> fol formula -> thm
        val axiom_or : fol formula -> fol formula -> thm
        val axiom_exists : string -> fol formula -> thm
        val concl : thm -> fol formula
    end;;
*)

// Implementation of the Proofsystem signature; this is done "manually"
// because F# doesn't allow for type-parameterized modules.
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
        List.foldBack2 (fun s t p -> Imp (mk_eq s t, p)) lefts rights
            (mk_eq (Fn (f, lefts)) (Fn (f, rights)))

    let axiom_predcong p lefts rights : thm =
        List.foldBack2 (fun s t p -> Imp (mk_eq s t, p)) lefts rights
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

let fprint_thm sw th =
//    open_box 0
    fprintf sw "|- " // write on the same line
//    print_space ()
//    open_box 0
    fprint_formula sw (fprint_atom sw) (concl th)
//    close_box ()
//    close_box ()

// Add printing facility
let inline print_thm th = fprint_thm stdout th
let inline sprint_thm th = writeToString (fun sw -> fprint_thm sw th)

//#install_printer print_thm;;
