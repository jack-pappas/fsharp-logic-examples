// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.qelim

open intro
open formulas
open prop
open defcnf
open dp
open stal
open bdd
open fol
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
//  ========================================================================= // 

// pg. 331
//  ------------------------------------------------------------------------- // 
//  Lift procedure given literal modifier, formula normalizer, and a  basic   // 
//  elimination procedure for existential formulas with conjunctive body.     // 
//  ------------------------------------------------------------------------- // 

let qelim bfn x p =
    let ycjs, ncjs =
        conjuncts p
        |> List.partition (mem x << fv)

    if ycjs = [] then p
    else
        let q = bfn (Exists (x, list_conj ycjs))
        List.foldBack mk_and ncjs q

let lift_qelim afn nfn qfn =
    let rec qelift vars fm cont =
        match fm with
        | Atom (R (_,_)) ->
            cont (afn vars fm)
        | Not p ->
            qelift vars p <| fun qelift_p ->
                cont (Not qelift_p)
        | And (p, q) ->
            qelift vars p <| fun qelift_p ->
            qelift vars q <| fun qelift_q ->
                cont (And (qelift_p, qelift_q))
        | Or (p, q) ->
            qelift vars p <| fun qelift_p ->
            qelift vars q <| fun qelift_q ->
                cont (Or (qelift_p, qelift_q))
        | Imp (p, q) ->
            qelift vars p <| fun qelift_p ->
            qelift vars q <| fun qelift_q ->
                cont (Imp (qelift_p, qelift_q))
        | Iff (p, q) ->
            qelift vars p <| fun qelift_p ->
            qelift vars q <| fun qelift_q ->
                cont (Iff (qelift_p, qelift_q))
        | Forall (x, p) ->
            qelift vars (Exists (x, Not p)) <| fun result ->
                cont (Not result)
        | Exists (x, p) ->
            qelift (x :: vars) p <| fun qelift_p ->
                qelift_p
                |> nfn
                |> disjuncts
                |> List.map (qelim (qfn vars) x)
                |> list_disj
                |> cont
        | _ ->
            cont fm

    fun fm ->
        qelift (fv fm) (miniscope fm) id
        |> simplify004
  
// pg. 333
//  ------------------------------------------------------------------------- // 
//  Cleverer (proposisional) NNF with conditional and literal modification.   // 
//  ------------------------------------------------------------------------- //

let cnnf lfn =
    let rec cnnf fm cont =
        match fm with
        | And (p, q) ->
            cnnf p <| fun cnnf_p ->
            cnnf q <| fun cnnf_q ->
                And (cnnf_p, cnnf_q)
                |> cont
        | Or (p, q) ->
            cnnf p <| fun cnnf_p ->
            cnnf q <| fun cnnf_q ->
                Or (cnnf_p, cnnf_q)
                |> cont
        | Imp (p, q) ->
            cnnf (Not p) <| fun cnnf_not_p ->
            cnnf q <| fun cnnf_q ->
                Or (cnnf_not_p, cnnf_q)
                |> cont
        | Iff (p, q) ->
            cnnf p <| fun cnnf_p ->
            cnnf q <| fun cnnf_q ->
            cnnf (Not p) <| fun cnnf_not_p ->
            cnnf (Not q) <| fun cnnf_not_q ->
                Or (And (cnnf_p, cnnf_q), And (cnnf_not_p, cnnf_not_q))
                |> cont
        | Not (Not p) ->
            cnnf p cont
        | Not (And (p, q)) ->
            cnnf (Not p) <| fun cnnf_not_p ->
            cnnf (Not q) <| fun cnnf_not_q ->
                Or (cnnf_not_p, cnnf_not_q)
                |> cont
        | Not (Or (And (p, q), And (p', r))) when p' = negate p ->
            cnnf (And (p, Not q)) <| fun left ->
            cnnf (And (p', Not r)) <| fun right ->
                Or (left, right)
                |> cont
        | Not (Or (p, q)) ->
            cnnf (Not p) <| fun cnnf_not_p ->
            cnnf (Not q) <| fun cnnf_not_q ->
                And (cnnf_not_p, cnnf_not_q)
                |> cont
        | Not (Imp (p, q)) ->
            cnnf p <| fun cnnf_p ->
            cnnf (Not q) <| fun cnnf_not_q ->
                And (cnnf_p, cnnf_not_q)
                |> cont
        | Not (Iff (p, q)) ->
            cnnf p <| fun cnnf_p ->
            cnnf q <| fun cnnf_q ->
            cnnf (Not p) <| fun cnnf_not_p ->
            cnnf (Not q) <| fun cnnf_not_q ->
                Or (And (cnnf_p, cnnf_not_q), And (cnnf_not_p, cnnf_q))
                |> cont
        | _ ->
            cont (lfn fm)

    fun fm ->
        let fm = simplify004 fm
        cnnf fm id
        |> simplify004
  
// pg. 334
//  ------------------------------------------------------------------------- // 
//  Initial literal simplifier and intermediate literal modifier.             // 
//  ------------------------------------------------------------------------- // 

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

// Note: List.find throws expcetion it does not return failure
//       so "try with failure" will not work with List.find
let dlobasic fm =
    match fm with
    | Exists (x, p) ->
        let cjs = subtract (conjuncts p) [Atom (R ("=", [Var x; Var x]))]
        try
            // OPTIMIZE : Use List.tryFind instead of List.find and the try/catch.
            let eqn = List.find is_eq cjs                
            let y =
                let s, t = dest_eq eqn
                if s = Var x then t else s
            list_conj (List.map (subst (x |=> y)) (subtract cjs [eqn]))
        with 
        | Failure _ ->
        //| :? System.Collections.Generic.KeyNotFoundException -> // List.find is modified to return failure again
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

let afn_dlo vars fm =
    match fm with
    | Atom (R ("<=", [s; t])) ->
        Not (Atom (R ("<", [t; s])))
    | Atom (R (">=", [s; t])) ->
        Not (Atom (R ("<", [s; t])))
    | Atom (R (">", [s; t])) ->
        Atom (R ("<", [t; s]))
    | _ -> fm

let quelim_dlo =
    lift_qelim afn_dlo (dnf << cnnf lfn_dlo) (fun _ -> dlobasic)
