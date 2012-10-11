// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// Real quantifier elimination (using Cohen-Hormander algorithm).            //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.real

open FSharpx.Compatibility.OCaml.Num

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
open qelim
open cooper
open complex

// pg. 368
// ------------------------------------------------------------------------- //
// Formal derivative of polynomial.                                          //
// ------------------------------------------------------------------------- //

// OPTIMIZE : Optimize using continuation-passing style.
let rec poly_diffn x n p =
    match p with
    | Fn ("+", [c; Fn ("*", [y; q])])
        when y = x ->
        Fn ("+", [poly_cmul (Int n) c; Fn ("*", [x; poly_diffn x (n + 1) q])])
    | _ ->
        poly_cmul (Int n) p

let poly_diff vars p =
    match p with
    | Fn ("+", [c; Fn ("*", [Var x; q])])
        when x = List.head vars ->
        poly_diffn (Var x) 1 q
    | _ -> zero
        
// pg. 369
// ------------------------------------------------------------------------- //
// Evaluate a quantifier-free formula given a sign matrix row for its polys. //
// ------------------------------------------------------------------------- //

let rel_signs = [
    "=", [Zero];
    "<=", [Zero; Negative];
    ">=", [Zero; Positive];
    "<", [Negative];
    ">", [Positive]; ]

let testform pmat fm =
    eval fm (fun (R (a, [p; z])) ->
        mem (assoc p pmat) (assoc a rel_signs))
            
// pg. 370
// ------------------------------------------------------------------------- //
// Infer sign of p(x) at points from corresponding qi(x) with pi(x) = 0      //
// ------------------------------------------------------------------------- //

let inferpsign (pd, qd) =
    try let i = index Zero pd
        List.nth qd i :: pd
    with Failure _ ->
        Nonzero :: pd
            
// pg. 370
// ------------------------------------------------------------------------- //
// Condense subdivision by removing points with no relevant zeros.           //
// ------------------------------------------------------------------------- //

// OPTIMIZE : Optimize with CPS.
let rec condense ps =
    match ps with
    | int :: pt :: other ->
        let rest = condense other
        if mem Zero pt then
            int :: pt :: rest
        else rest
    | _ -> ps
        
// pg. 372
// ------------------------------------------------------------------------- //
// Infer sign on intervals (use with infinities at end) and split if needed  //
// ------------------------------------------------------------------------- //

// OPTIMIZE : Optimize with CPS.
let rec inferisign ps =
    match ps with
    | ((l::ls) as x) :: (_ :: ints) :: ((r :: rs) :: xs as pts) ->
        match l, r with
        | Zero, Zero ->
            failwith "inferisign: inconsistent"
        | Nonzero, _
        | _, Nonzero ->
            failwith "inferisign: indeterminate"
        | Zero, _ ->
            x :: (r :: ints) :: inferisign pts
        | _, Zero ->
            x :: (l :: ints) :: inferisign pts
        | Negative, Negative
        | Positive, Positive ->
            x :: (l :: ints) :: inferisign pts
        | _ ->
            x :: (l :: ints) :: (Zero :: ints) :: (r :: ints) :: inferisign pts
    | _ -> ps
        
// pg. 372
// ------------------------------------------------------------------------- //
// Deduce matrix for p,p1,...,pn from matrix for p',p1,...,pn,q0,...,qn      //
// where qi = rem(p,pi) with p0 = p'                                         //
// ------------------------------------------------------------------------- //

let dedmatrix cont mat =
    let mat2 =
        let mat1 =
            let l = List.length (List.head mat) / 2
            condense (List.map (inferpsign << chop_list l) mat)
        [swap true (List.nth (List.head mat1) 1)] :: mat1 @ [[List.nth (last mat1) 1]]
           
    inferisign mat2 
    |> List.tail
    |> butlast
    |> List.map (fun l ->
        // OPTIMIZE : Replace 'fun l ->' with 'function hd :: _ :: tl'
        List.head l :: List.tail (List.tail l))
    |> condense
    |> cont
        
// pg. 373
// ------------------------------------------------------------------------- //
// Pseudo-division making sure the remainder has the same sign.              //
// ------------------------------------------------------------------------- //

let pdivide_pos vars sgns s p =
    let a = head vars p
    let k, r = pdivide vars s p
    match findsign sgns a with
    | Zero ->
        failwith "pdivide_pos: zero head coefficient"
    | Positive ->
        r
    | _ when k % 2 = 0 ->
        r
    | Negative ->
        poly_neg r
    | _ ->
        poly_mul vars a r
        
// pg. 373
// ------------------------------------------------------------------------- //
// Case splitting for positive/negative (assumed nonzero).                   //
// ------------------------------------------------------------------------- //

let split_sign sgns pol cont =
    match findsign sgns pol with
    | Nonzero ->
        let fm = Atom (R (">", [pol; zero]))
        Or (And (fm, cont (assertsign sgns (pol, Positive))),
            And (Not fm,cont (assertsign sgns (pol, Negative))))
    | _ -> cont sgns

let split_trichotomy sgns pol cont_z cont_pn =
    split_zero sgns pol cont_z <| fun s' ->
        split_sign s' pol cont_pn
        
// pg. 374
// ------------------------------------------------------------------------- //
// Main recursive evaluation of sign matrices.                               //
// ------------------------------------------------------------------------- //

let rec casesplit vars dun pols cont sgns =
    match pols with
    | [] -> matrix vars dun cont sgns
    | p :: ops ->
        split_trichotomy sgns (head vars p)
            (if is_constant vars p then delconst vars dun p ops cont
                else casesplit vars dun (behead vars p :: ops) cont)
            (if is_constant vars p then delconst vars dun p ops cont
                else casesplit vars (dun @ [p]) ops cont)

and delconst vars dun p ops cont sgns =
    let cont' m = cont (List.map (insertat (List.length dun) (findsign sgns p)) m)
    casesplit vars dun ops cont' sgns

and matrix vars pols cont sgns =
    match pols with
    | [] ->
        try
            cont [[]]
        with Failure _ ->
            False
    | _ ->
        let p = List.head (sort (decreasing (degree vars)) pols)
        let rec p' = poly_diff vars p
        and i = index p pols
        let qs =
            let p1, p2 = chop_list i pols
            p' :: p1 @ List.tail p2
        let gs = List.map (pdivide_pos vars sgns p) qs
        let cont' m = cont (List.map (fun l -> insertat i (List.head l) (List.tail l)) m)
        casesplit vars [] (qs @ gs) (dedmatrix cont') sgns
            
// pg. 375
// ------------------------------------------------------------------------- //
// Now the actual quantifier elimination code.                               //
// ------------------------------------------------------------------------- //

let basic_real_qelim vars (Exists (x, p)) =
    let pols = atom_union (function (R (a, [t; Fn ("0", [])])) -> [t] | _ -> []) p
    let cont mat =
        if List.exists (fun m -> testform (List.zip pols m) p) mat then
            True
        else False
    casesplit (x :: vars) [] pols cont init_sgns

let real_qelim =
    simplify004
    << evalc
    << lift_qelim polyatom (simplify004 << evalc) basic_real_qelim
           
// pg. 377
// OPTIMIZE : Optimize with CPS.
let rec grpterm tm =
    match tm with
    | Var x -> tm
    | Fn ("*", [s; t]) ->
        let t2 = Fn ("*", [Fn ("2", []); grpterm t])
        Fn ("*", [grpterm s; Fn ("+", [Fn("1", []); t2])])
    | Fn ("i", [t]) ->
        Fn ("^", [grpterm t; Fn ("2", [])])
    | Fn ("1", []) ->
        Fn ("2", [])

let grpform (Atom (R ("=", [s; t]))) =
    generalize (Atom (R (">", [grpterm s; grpterm t])))
    |> relativize (fun x ->
        Atom (R (">", [Var x; Fn("1",[])])))
   
// pg. 379
// ------------------------------------------------------------------------- //
// A case where using DNF is an improvement.                                 //
// ------------------------------------------------------------------------- //

let real_qelim' =
    simplify004 << evalc <<
    lift_qelim polyatom (dnf << cnnf id << evalc) basic_real_qelim

// ------------------------------------------------------------------------- //
// Didn't seem worth it in the book, but monicization can help a lot.        //
// Now this is just set as an exercise.                                      //
// ------------------------------------------------------------------------- //
    
//let rec casesplit vars dun pols cont sgns =
//    match pols with
//    | [] ->
//        monicize vars dun cont sgns
//    | p :: ops ->
//        split_trichotomy sgns (head vars p)
//            (if is_constant vars p then delconst vars dun p ops cont else casesplit vars dun (behead vars p :: ops) cont)
//            (if is_constant vars p then delconst vars dun p ops cont else casesplit vars (dun @ [p]) ops cont)
//
//and delconst vars dun p ops cont sgns =
//    let cont' m = cont (List.map (insertat (List.length dun) (findsign sgns p)) m)
//    casesplit vars dun ops cont' sgns
//
//and matrix vars pols cont sgns =
//    if pols = [] then
//        try cont [[]]
//        with Failure _ -> False
//    else
//        let p = List.head (sort (decreasing (degree vars)) pols)
//        let rec p' = poly_diff vars p
//        and i = index p pols in
//        let qs =
//            let p1, p2 = chop_list i pols
//            p' :: p1 @ List.tail p2
//        let gs = List.map (pdivide_pos vars sgns p) qs
//        let cont' m = cont (List.map (fun l -> insertat i (List.head l) (List.tail l)) m)
//        casesplit vars [] (qs @ gs) (dedmatrix cont') sgns
//
//and monicize vars pols cont sgns =
//    let mols,swaps = List.unzip (List.map monic pols)
//    let sols = setify mols
//    let indices = List.map (fun p -> index p sols) mols
//    let transform m =
//        List.map2 (fun sw i -> swap sw (List.nth m i)) swaps indices
//    let cont' mat = cont (List.map transform mat)
//    matrix vars sols cont' sgns
//
//let basic_real_qelim vars (Exists (x, p)) =
//    let pols = atom_union (function (R (a, [t; Fn ("0", [])])) -> [t] | _ -> []) p
//    let cont mat =
//        if List.exists (fun m -> testform (List.zip pols m) p) mat then True else False
//    casesplit (x::vars) [] pols cont init_sgns
//
//let real_qelim =
//    simplify004 << evalc <<
//    lift_qelim polyatom (simplify004 << evalc) basic_real_qelim
//
//let real_qelim' =
//    simplify004 << evalc <<
//    lift_qelim polyatom (dnf << cnnf (fun x -> x) << evalc) basic_real_qelim
