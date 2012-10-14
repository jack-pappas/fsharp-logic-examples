// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.decidable

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

// pg. 309
// ========================================================================= //
// Special procedures for decidable subsets of first order logic.            //
// ========================================================================= //

// pg. 310
// ------------------------------------------------------------------------- //
// However, we can just form all the ground instances.                       //
// ------------------------------------------------------------------------- //

let aedecide fm =
    let sfm = skolemize (Not fm)        
    let cnsts, funcs =
        functions sfm
        |> List.partition (fun (_, ar) -> ar = 0)

    match funcs with
    | [] ->
        let cntms =
            let consts =
                match cnsts with
                | [] -> ["c", 0]
                | x -> x
            consts
            |> List.map (fun (c, _) -> Fn (c, []))

        let fvs = fv sfm
        let cjs = simpcnf sfm            
        groundtuples cntms [] 0 (List.length fvs)
        |> List.map (fun tup ->
            image (image (subst (fpf fvs tup))) cjs)
        |> unions
        |> dpll
        |> not

    | _ ->
        failwith "Not decidable"
 
// pg. 314
// ------------------------------------------------------------------------- //
// Simple-minded miniscoping procedure.                                      //
// ------------------------------------------------------------------------- //

let separate x cjs =
    match List.partition (mem x << fv) cjs with
    | [], no ->
        list_conj no
    | yes, [] ->
        Exists (x, list_conj yes)
    | yes, no ->
        And (Exists (x, list_conj yes), list_conj no)

let pushquant x p =
    if not <| mem x (fv p) then p
    else
        nnf p
        |> purednf
        |> List.map (separate x)
        |> list_disj

//
let rec private miniscopeImpl fm cont =
    match fm with
    | Not p ->
        miniscopeImpl p <| fun miniscoped_p ->
            Not miniscoped_p
            |> cont
    | And (p, q) ->
        miniscopeImpl p <| fun miniscoped_p ->
        miniscopeImpl q <| fun miniscoped_q ->
            And (miniscoped_p, miniscoped_q)
            |> cont
    | Or (p, q) ->
        miniscopeImpl p <| fun miniscoped_p ->
        miniscopeImpl q <| fun miniscoped_q ->
            Or (miniscoped_p, miniscoped_q)
            |> cont
    | Forall (x, p) ->
        miniscopeImpl p <| fun miniscoped_p ->
            Not miniscoped_p
            |> pushquant x
            |> Not
            |> cont
    | Exists (x, p) ->
        miniscopeImpl p <| fun miniscoped_p ->
            miniscoped_p
            |> pushquant x
            |> cont
    | fm ->
        cont fm

//
let miniscope fm =
    miniscopeImpl fm id

// pg. 316
// ------------------------------------------------------------------------- //
// Stronger version of "aedecide" similar to Wang's classic procedure.       //
// ------------------------------------------------------------------------- //

let wang fm =
    simplify004 fm
    |> nnf
    |> miniscope
    |> aedecide

// pg. 318
// ------------------------------------------------------------------------- //
// Checking classic Aristotelean syllogisms.                                 //
// ------------------------------------------------------------------------- //

let atom p x = Atom (R (p, [Var x]))

let premiss_A (p, q) = Forall ("x", Imp (atom p "x", atom q "x"))
let premiss_E (p, q) = Forall ("x", Imp (atom p "x", Not (atom q "x")))
let premiss_I (p, q) = Exists ("x", And (atom p "x", atom q "x"))
let premiss_O (p, q) = Exists ("x", And (atom p "x", Not (atom q "x")))

let anglicize_premiss fm =
    match fm with
    | Forall (_, Imp (Atom (R (p, _)), Atom (R (q, _)))) ->
        sprintf "all %s are %s" p q
    | Forall (_, Imp (Atom (R (p, _)), Not (Atom (R (q, _))))) ->
        sprintf "no %s are %s" p q
    | Exists (_, And (Atom (R (p, _)), Atom (R (q, _)))) ->
        sprintf "some %s are %s" p q
    | Exists (_, And (Atom (R (p, _)), Not (Atom (R (q, _))))) ->
        sprintf "some %s are not %s" p q

let anglicize_syllogism (Imp (And (t1, t2), t3)) =
    sprintf "If %s and %s, then %s"
        (anglicize_premiss t1) (anglicize_premiss t2) (anglicize_premiss t3)

// Phan: should this be moved to fsx?
let all_possible_syllogisms =
    let sylltypes = [premiss_A; premiss_E; premiss_I; premiss_O]
    let prems1 = allpairs id sylltypes ["M","P"; "P","M"]
    let prems2 = allpairs id sylltypes ["S","M"; "M","S"]
    let prems3 = allpairs id sylltypes ["S","P"]
    allpairs mk_imp (allpairs mk_and prems1 prems2) prems3

// pg. 319
// ------------------------------------------------------------------------- //
// We can "fix" the traditional list by assuming nonemptiness.               //
// ------------------------------------------------------------------------- //

let all_possible_syllogisms' =
    let p = parse "(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x))"
    all_possible_syllogisms
    |> List.map (fun t ->
        Imp (p, t))

// pg. 322
// ------------------------------------------------------------------------- //
// Decide a formula on all models of size n.                                 //
// ------------------------------------------------------------------------- //

(* OPTIMIZE :   Some of these functions use intermediate lists when they could
                be optimized using other functions like List.init or List.fold. *)

let rec alltuples n l =
    if n = 0 then [[]] 
    else
        let tups = alltuples (n - 1) l
        allpairs (fun h t -> h :: t) l tups

let allmappings dom ran =
    List.foldBack (fun p -> allpairs (valmod p) ran) dom [undef]

let alldepmappings dom ran =
    List.foldBack (fun (p, n) -> allpairs (valmod p) (ran n)) dom [undef]

let allfunctions dom n =
    allmappings (alltuples n dom) dom

let allpredicates dom n =
    allmappings (alltuples n dom) [false; true]

let decide_finite n fm =
    let interps =
        let dom = [1 .. n]
        let fints =
            allfunctions dom
            |> alldepmappings (functions fm)
        let pints =
            allpredicates dom
            |> alldepmappings (predicates fm)
        allpairs (fun f p -> dom, f, p) fints pints

    let fm' = generalize fm
    interps
    |> List.forall (fun md ->
        holds md undefined fm')
  
// pg. 323
// ------------------------------------------------------------------------- //
// Decision procedure in principle for formulas with finite model property.  //
// ------------------------------------------------------------------------- //

let limmeson n fm =        
    let rules =
        let cls =
            pnf fm
            |> specialize
            |> simpcnf
        List.foldBack ((@) << contrapositives) cls []
    mexpand002 rules [] False id (undefined, n, 0)

let limited_meson n fm =
    Not (generalize fm)
    |> askolemize
    |> simpdnf
    |> List.map (limmeson n << list_conj)

let decide_fmp fm =
    let rec test n =
        try limited_meson n fm |> ignore
            true
        with _ ->
            if decide_finite n fm then
                test (n + 1)
            else false
    test 1

// pg. 325
// ------------------------------------------------------------------------- //
// Semantic decision procedure for the monadic fragment.                     //
// ------------------------------------------------------------------------- //

let decide_monadic fm =
    let monadic, other =
        predicates fm
        |> List.partition (fun (_, ar) -> ar = 1)

    let funcs = functions fm
    if not (List.isEmpty funcs) || List.exists (fun (_, ar) -> ar > 1) other then
        failwith "Not in the monadic subset"
    else
        // OPTIMIZE : The 'let n = ...' code here looks like it's equivalent
        // to (1 <<< List.length monadic).
        let n = funpow (List.length monadic) (( * ) 2) 1
        decide_finite n fm
