// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
//                                                                           //
// NOTE: Stalmarck's method is protected by patents covering commercial use. //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.stal

open FSharpx.Compatibility.OCaml.Num

open intro
open formulas
open prop
open defcnf

// ========================================================================= //
// Simple implementation of Stalmarck's algorithm.                           //
//                                                                           //
// NB! This algorithm is patented for commercial use (not that a toy version //
// like this would actually be useful in practice).                          //
// ========================================================================= //

// pg. 92
// ------------------------------------------------------------------------- //
// Triplet transformation, using functions defined earlier.                  //
// ------------------------------------------------------------------------- //

let triplicate fm =
    let p, defs, _ =
        let fm' = nenf fm
        let n = (num_of_int 1) + overatoms (max_varindex "p_" << pname) fm' (num_of_int 0)
        maincnf (fm', undefined, n)
    p, List.map (snd << snd) (graph defs)

// pg. 92
// ------------------------------------------------------------------------- //
// Automatically generate triggering rules to save writing them out.         //
// ------------------------------------------------------------------------- //

let atom lit =
    if negative lit then negate lit else lit

let rec align (p, q) =
    if atom p < atom q then
        align (q, p)
    elif negative p then
        negate p, negate q
    else p, q

let equate2 (p, q) eqv =
    equate (negate p, negate q) (equate (p, q) eqv)

let rec irredundant rel eqs =
    match eqs with
    | [] -> []
    | (p, q) :: oth ->
        if canonize rel p = canonize rel q then
            irredundant rel oth
        else
            insert (p, q) (irredundant (equate2 (p, q) rel) oth)

let consequences (p, q as peq) fm eqs =
    let follows (r, s) =
        tautology <| Imp (And (Iff (p, q), fm), Iff (r, s))

    irredundant (equate2 peq unequal) (List.filter follows eqs)

let triggers fm =
    let poslits = insert True (List.map (fun p -> Atom p) (atoms fm))
    let lits = union poslits (List.map negate poslits)
    let pairs = allpairs (fun p q -> p, q) lits lits
    let npairs = List.filter (fun (p, q) -> atom p <> atom q) pairs
    let eqs = setify <| List.map align npairs
    let raw = List.map (fun p -> p, consequences p fm eqs) eqs
    List.filter (fun (p, c) -> not <| List.isEmpty c) raw

// pg. 94
// ------------------------------------------------------------------------- //
// Precompute and instantiate triggers for standard triplets.                //
// ------------------------------------------------------------------------- //

let trigger =
    match List.map triggers
            [parse_prop_formula "p <=> q /\ r";
            parse_prop_formula "p <=> q \/ r";
            parse_prop_formula "p <=> (q ==> r)";
            parse_prop_formula "p <=> (q <=> r)"; ] with
    | [trig_and; trig_or; trig_imp; trig_iff] ->
        let p = parse_prop_formula "p"
        let q = parse_prop_formula "q"
        let r = parse_prop_formula "r"
        let ddnegate fm =
            match fm with
            | Not (Not p) -> p
            | _ -> fm
        // TODO: Figure out how to use match with with this let to remove warning
        let inst_fn [x; y; z] =
            let subfn = fpf [P"p"; P"q"; P"r"] [x; y; z]
            ddnegate << psubst subfn
        let inst2_fn i (p, q) =
            align (inst_fn i p, inst_fn i q)
        let instn_fn i (a, c) =
            inst2_fn i a, List.map (inst2_fn i) c
        let inst_trigger = List.map << instn_fn
        function
        | Iff (x, And (y, z)) ->
            inst_trigger [x; y; z] trig_and
        | Iff (x, Or (y, z)) ->
            inst_trigger [x; y; z] trig_or
        | Iff (x, Imp (y, z)) ->
            inst_trigger [x; y; z] trig_imp
        | Iff (x, Iff (y, z)) ->
            inst_trigger [x; y; z] trig_iff
        | _ ->
            failwith "How did we get here?"
    | _ ->
        failwith "How did we get here?"

// pg. 95
// ------------------------------------------------------------------------- //
// Compute a function mapping each variable/true to relevant triggers.       //
// ------------------------------------------------------------------------- //

let relevance trigs =
    let insert_relevant p trg f = (p |-> insert trg (tryapplyl f p)) f
    let insert_relevant2 ((p, q),_ as trg) f =
        insert_relevant p trg (insert_relevant q trg f)
    List.foldBack insert_relevant2 trigs undefined

// pg. 96
// ------------------------------------------------------------------------- //
// Merging of equiv classes and relevancies.                                 //
// ------------------------------------------------------------------------- //

let equatecons (p0, q0) (eqv, rfn as erf) =
    let p = canonize eqv p0
    let q = canonize eqv q0
    if p = q then [], erf
    else
        let p' = canonize eqv (negate p0)
        let q' = canonize eqv (negate q0)
        let eqv' = equate2 (p, q) eqv
        let sp_pos = tryapplyl rfn p
        let sp_neg = tryapplyl rfn p'
        let sq_pos = tryapplyl rfn q
        let sq_neg = tryapplyl rfn q'
        let rfn' =
            (canonize eqv' p |-> union sp_pos sq_pos)
                ((canonize eqv' p' |-> union sp_neg sq_neg) rfn)
        let nw = union (intersect sp_pos sq_pos) (intersect sp_neg sq_neg)
        List.foldBack (union << snd) nw [], (eqv', rfn')

// pg. 96
// ------------------------------------------------------------------------- //
// Zero-saturation given an equivalence/relevance and new assignments.       //
// ------------------------------------------------------------------------- //

let rec zero_saturate erf assigs =
    match assigs with
    | [] -> erf
    | (p, q) :: ts ->
        let news, erf' = equatecons (p, q) erf
        zero_saturate erf' (union ts news)

// pg. 96
// ------------------------------------------------------------------------- //
// Zero-saturate then check for contradictoriness.                           //
// ------------------------------------------------------------------------- //

let zero_saturate_and_check erf trigs =
    let (eqv', rfn' as erf') = zero_saturate erf trigs
    let vars = List.filter positive (equated eqv')
    if List.exists (fun x -> canonize eqv' x = canonize eqv' (Not x)) vars then
        snd <| equatecons (True, Not True) erf'
    else erf'

// pg. 96
// ------------------------------------------------------------------------- //
// Now we can quickly test for contradiction.                                //
// ------------------------------------------------------------------------- //

let truefalse pfn =
    canonize pfn (Not True) = canonize pfn True

// pg. 97
// ------------------------------------------------------------------------- //
// Iterated equivalening over a set.                                         //
// ------------------------------------------------------------------------- //

let rec equateset s0 eqfn =
    match s0 with
    | a :: (b :: s2 as s1) ->
        equateset s1 (snd (equatecons (a, b) eqfn))
    | _ -> eqfn

// pg. 97
// ------------------------------------------------------------------------- //
// Intersection operation on equivalence classes and relevancies.            //
// ------------------------------------------------------------------------- //

let rec inter els (eq1,_ as erf1) (eq2,_ as erf2) rev1 rev2 erf =
    match els with
    | [] -> erf
    | x :: xs ->
        let b1 = canonize eq1 x
        let b2 = canonize eq2 x
        let s1 = apply rev1 b1
        let s2 = apply rev2 b2
        let s = intersect s1 s2
        inter (subtract xs s) erf1 erf2 rev1 rev2 (equateset s erf)

// pg. 97
// ------------------------------------------------------------------------- //
// Reverse the equivalence mappings.                                         //
// ------------------------------------------------------------------------- //

let reverseq domain eqv =
    let al = List.map (fun x -> x, canonize eqv x) domain
    List.foldBack (fun (y, x) f -> (x |-> insert y (tryapplyl f x)) f)
        al undefined

// pg. 97
// ------------------------------------------------------------------------- //
// Special intersection taking contradictoriness into account.               //
// ------------------------------------------------------------------------- //

let stal_intersect (eq1,_ as erf1) (eq2,_ as erf2) erf =
    if truefalse eq1 then erf2
    elif truefalse eq2 then erf1
    else
        let dom1 = equated eq1
        let dom2 = equated eq2
        let comdom = intersect dom1 dom2
        let rev1 = reverseq dom1 eq1
        let rev2 = reverseq dom2 eq2
        inter comdom erf1 erf2 rev1 rev2 erf

// pg. 98
// ------------------------------------------------------------------------- //
// General n-saturation for n >= 1                                           //
// ------------------------------------------------------------------------- //

let rec saturate n erf assigs allvars =
    let (eqv',_ as erf') = zero_saturate_and_check erf assigs
    if n = 0 || truefalse eqv' then erf'
    else
        let (eqv'',_ as erf'') = splits n erf' allvars allvars
        if eqv'' = eqv' then erf''
        else saturate n erf'' [] allvars

and splits n (eqv,_ as erf) allvars vars =
    match vars with
    | [] -> erf
    | p :: ovars ->
        if canonize eqv p <> p then
            splits n erf allvars ovars
        else
            let erf0 = saturate (n - 1) erf [p, Not True] allvars
            let erf1 = saturate (n - 1) erf [p, True] allvars
            let (eqv',_ as erf') = stal_intersect erf0 erf1 erf
            if truefalse eqv' then erf'
            else splits n erf' allvars ovars

// pg. 98
// ------------------------------------------------------------------------- //
// Saturate up to a limit.                                                   //
// ------------------------------------------------------------------------- //

let rec saturate_upto vars n m trigs assigs =
    if n > m then
        failwithf "Not %i-easy" m
    else
        printfn "*** Starting %i-saturation" n
        let eqv, _ =
            saturate n (unequal, relevance trigs) assigs vars

        truefalse eqv
        || saturate_upto vars (n + 1) m trigs assigs

// pg. 98
// ------------------------------------------------------------------------- //
// Overall function.                                                         //
// ------------------------------------------------------------------------- //

let stalmarck fm =
    let include_trig (e, cqs) f =
        (e |-> union cqs (tryapplyl f e)) f
    let fm' = psimplify <| Not fm
    if fm' = False then true
    elif fm' = True then false
    else
        let p, triplets = triplicate fm'
        let trigfn =
            List.foldBack (List.foldBack include_trig << trigger) triplets undefined
        let vars = List.map (fun p -> Atom p) (unions (List.map atoms triplets))
        saturate_upto vars 0 2 (graph trigfn) [p, True]

