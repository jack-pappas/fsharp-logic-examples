// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.decidable

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
    let fvs = fv sfm
    let cnsts, funcs =
        functions sfm
        |> List.partition (fun (_, ar) -> ar = 0)
    if funcs <> [] then
        failwith "Not decidable"
    else
        let consts = if cnsts = [] then ["c", 0] else cnsts
        let cntms = List.map (fun (c, _) -> Fn (c, [])) consts
        let alltuples = groundtuples cntms [] 0 (List.length fvs)
        let cjs = simpcnf sfm
        let grounds = List.map (fun tup -> image (image (subst (fpf fvs tup))) cjs) alltuples
        not(dpll(unions grounds))
 
// pg. 314
// ------------------------------------------------------------------------- //
// Simple-minded miniscoping procedure.                                      //
// ------------------------------------------------------------------------- //

let separate x cjs =
    let yes, no = List.partition (mem x >>|> fv) cjs
    if yes = [] then list_conj no
    elif no = [] then Exists (x, list_conj yes)
    else And (Exists (x, list_conj yes), list_conj no)

let rec pushquant x p =
    if not (mem x (fv p)) then p
    else
        let djs = purednf (nnf p)
        list_disj (List.map (separate x) djs)

let rec miniscope fm =
    match fm with
    | Not p ->
        Not (miniscope p)
    | And (p, q) ->
        And (miniscope p, miniscope q)
    | Or (p, q) ->
        Or (miniscope p, miniscope q)
    | Forall (x, p) ->
        Not (pushquant x (Not (miniscope p)))
    | Exists (x, p) ->
        pushquant x (miniscope p)
    | _ -> fm

// pg. 316
// ------------------------------------------------------------------------- //
// Stronger version of "aedecide" similar to Wang's classic procedure.       //
// ------------------------------------------------------------------------- //

let wang fm = aedecide (miniscope (nnf (simplify004 fm)))

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
    List.map (fun t -> Imp (p, t)) all_possible_syllogisms

// pg. 322
// ------------------------------------------------------------------------- //
// Decide a formula on all models of size n.                                 //
// ------------------------------------------------------------------------- //

let rec alltuples n l =
    if n = 0 then [[]] 
    else
        let tups = alltuples (n - 1) l
        allpairs (fun h t -> h :: t) l tups

let allmappings dom ran =
    List.foldBack (fun p -> allpairs (valmod p) ran) dom [undef]

let alldepmappings dom ran =
    List.foldBack (fun (p, n) -> allpairs (valmod p) (ran n)) dom [undef]

let allfunctions dom n = allmappings (alltuples n dom) dom

let allpredicates dom n = allmappings (alltuples n dom) [false; true]

let decide_finite n fm =
    let interps =
        let dom = 1 -- n
        let fints =
            let funcs = functions fm
            alldepmappings funcs (allfunctions dom)
        let pints =
            let preds = predicates fm
            alldepmappings preds (allpredicates dom)
        allpairs (fun f p -> dom, f, p) fints pints
    let fm' = generalize fm
    List.forall (fun md -> holds md undefined fm') interps
  
// pg. 323
// ------------------------------------------------------------------------- //
// Decision procedure in principle for formulas with finite model property.  //
// ------------------------------------------------------------------------- //

let limmeson n fm =
    let cls = simpcnf (specialize (pnf fm))
    let rules = List.foldBack ((@) >>|> contrapositives) cls []
    mexpand002 rules [] False id (undefined, n, 0)

let limited_meson n fm =
    let fm1 = askolemize (Not (generalize fm))
    List.map (limmeson n >>|> list_conj) (simpdnf fm1)

let decide_fmp fm =
    let rec test n =
        try limited_meson n fm |> ignore
            true
        with _ ->
            if decide_finite n fm then test (n + 1) else false
    test 1

// pg. 325
// ------------------------------------------------------------------------- //
// Semantic decision procedure for the monadic fragment.                     //
// ------------------------------------------------------------------------- //

let decide_monadic fm =
    let funcs = functions fm
    let preds = predicates fm
    let monadic, other = List.partition (fun (_, ar) -> ar = 1) preds
    if funcs <> [] || List.exists (fun (_, ar) -> ar > 1) other
    then failwith "Not in the monadic subset"
    else
        let n = funpow (List.length monadic) (( * ) 2) 1
        decide_finite n fm
