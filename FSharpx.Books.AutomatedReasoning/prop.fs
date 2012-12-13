// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.prop

open intro
open formulas

// pg. 28
// ========================================================================= //
// Basic stuff for propositional logic: datatype, parsing and printing.      //
// ========================================================================= //

type prop = P of string

let inline pname (P s) = s

// pg. 29
// ------------------------------------------------------------------------- //
// Parsing of propositional formulas.                                        //
// ------------------------------------------------------------------------- //

let parse_propvar vs inp =
    match inp with
    | p :: oinp when p <> "(" ->
        Atom (P p), oinp
    | _ ->
        failwith "parse_propvar"
        
let parse_prop_formula =
    parse_formula ((fun _ _ -> failwith ""), parse_propvar) []
    |> make_parser
                
// pg. 29
// ------------------------------------------------------------------------- //
// Printer.                                                                  //
// ------------------------------------------------------------------------- //

let fprint_propvar sw prec p =
    fprintf sw "%O" (pname p)

let inline print_propvar prec p = fprint_propvar stdout prec p
let inline sprint_propvar prec p = writeToString (fun sw -> fprint_propvar sw prec p)
        
let fprint_prop_formula sw = 
    fprint_qformula sw (fprint_propvar sw)

let inline print_prop_formula f = fprint_prop_formula stdout f
let inline sprint_prop_formula f = writeToString (fun sw -> fprint_prop_formula sw f)

// pg. 32
// ------------------------------------------------------------------------- //
// Interpretation of formulas.                                               //
// ------------------------------------------------------------------------- //

// NOTE: added cases for Exists and Forall to avoid compiler warning
let rec eval fm v =
    match fm with
    | False -> false
    | True -> true
    | Atom x -> v x
    | Not p ->
        not <| eval p v
    | And (p, q) ->
        (eval p v) && (eval q v)
    | Or (p, q) ->
        (eval p v) || (eval q v)
    | Imp (p, q) ->
        not(eval p v) || (eval q v)
    | Iff (p, q) ->
        (eval p v) = (eval q v)
    | Exists _
    | Forall _ ->
        failwith "Not part of propositional logic."

// pg. 35
// ------------------------------------------------------------------------- //
// Return the set of propositional variables in a formula.                   //
// ------------------------------------------------------------------------- //

let atoms fm = 
    atom_union (fun a -> [a]) fm

// pg. 35
// ------------------------------------------------------------------------- //
// Code to print out truth tables.                                           //
// ------------------------------------------------------------------------- //

let rec onallvaluations subfn v ats =
    match ats with
    | [] -> subfn v
    | p :: ps ->
        let v' t q =
            if q = p then t
            else v q
        onallvaluations subfn (v' false) ps
        && onallvaluations subfn (v' true) ps

let fprint_truthtable sw fm =
    // [P "p"; P "q"; P "r"]
    let ats = atoms fm
    // 5 + 1 = length of false + length of space
    let width = List.foldBack (max << String.length << pname) ats 5 + 1
    let fixw s = s + String.replicate (width - String.length s) " "
    let truthstring p = fixw (if p then "true" else "false")
    let mk_row v =
        let lis = List.map (fun x -> truthstring (v x)) ats
        let ans = truthstring (eval fm v)
        fprintf sw "%s" (List.foldBack (+) lis ("| " + ans))
        fprintfn sw ""
        true
    let seperator = String.replicate (width * (List.length ats) + 9) "-"
    fprintfn sw "%s" (List.foldBack (fun s t -> fixw(pname s) + t) ats "| formula")
    fprintfn sw "%s" seperator
    let _ = onallvaluations mk_row (fun x -> false) ats
    fprintfn sw "%s" seperator
    fprintfn sw ""

// Actuals functions to call from other modules
let inline print_truthtable f = fprint_truthtable stdout f
let inline sprint_truthtable f = writeToString (fun sw -> fprint_truthtable sw f)

// pg. 41
// ------------------------------------------------------------------------- //
// Recognizing tautologies.                                                  //
// ------------------------------------------------------------------------- //

let tautology fm =
    onallvaluations (eval fm) (fun s -> false) (atoms fm)

// pg. 41
// ------------------------------------------------------------------------- //
// Related concepts.                                                         //
// ------------------------------------------------------------------------- //

let unsatisfiable fm = 
    tautology <| Not fm
        
let satisfiable fm = 
    not <| unsatisfiable fm

// pg. 41
// ------------------------------------------------------------------------- //
// Substitution operation.                                                   //
// ------------------------------------------------------------------------- //

let psubst subfn =
    onatoms <| fun p ->
        tryapplyd subfn p (Atom p)

// pg. 48
// ------------------------------------------------------------------------- //
// Dualization.                                                              //
// ------------------------------------------------------------------------- //

let rec dual fm =
    match fm with
    | False -> True
    | True -> False
    | Atom p -> fm
    | Not p ->
        Not (dual p)
    | And (p, q) ->
        Or (dual p, dual q)
    | Or (p, q) ->
        And (dual p, dual q)
    | _ ->
        failwith "Formula involves connectives ==> or <=>"


// pg. 50
// ------------------------------------------------------------------------- //
// Routine simplification.                                                   //
// ------------------------------------------------------------------------- //

let psimplify1 fm =
    match fm with
    | Not True ->
        False
    | And (p, False)
    | And (False, p) ->
        False

    | Not False
    | Iff (False, False) -> // From Errata
        True
    | Or (p, True)
    | Or (True, p)
    | Imp (False, p)
    | Imp (p, True) ->
        True

    | And (p, True)
    | Not (Not p)
    | And (True, p)
    | Or (p, False)
    | Or (False, p)
    | Imp (True, p)
    | Iff (p, True)
    | Iff (True, p) -> p
        
    | Imp (p, False)
    | Iff (p, False)
    | Iff (False, p) ->
        Not p

    | fm -> fm
        
let rec psimplify fm =
    match fm with
    | Not p ->
        psimplify1 (Not (psimplify p))
    | And (p, q) ->
        psimplify1 (And (psimplify p, psimplify q))
    | Or (p, q) ->
        psimplify1 (Or (psimplify p, psimplify q))
    | Imp (p, q) ->
        psimplify1 (Imp (psimplify p, psimplify q))
    | Iff (p, q) ->
        psimplify1 (Iff (psimplify p, psimplify q))
    | fm -> fm

// pg. 51
// ------------------------------------------------------------------------- //
// Some operations on literals.                                              //
// ------------------------------------------------------------------------- //

let negative = function
    | Not p -> true
    | _ -> false
    
let positive lit = not <| negative lit
    
let negate = function
    | Not p -> p
    | p -> Not p

// pg. 52
// ------------------------------------------------------------------------- //
// Negation normal form.                                                     //
// ------------------------------------------------------------------------- //

// NOTE: Changed name from nnf to nnfOrig to avoid F# compiler error.
let rec nnfOrig fm =
    match fm with
    | And (p, q) ->
        And (nnfOrig p, nnfOrig q)
    | Or (p, q) ->
        Or (nnfOrig p, nnfOrig q)
    | Imp (p, q) ->
        Or (nnfOrig (Not p), nnfOrig q)
    | Iff (p, q) ->
        Or (And (nnfOrig p, nnfOrig q),
            And (nnfOrig (Not p), nnfOrig (Not q)))
    | Not (Not p) ->
        nnfOrig p
    | Not (And (p, q)) ->
        Or (nnfOrig (Not p), nnfOrig (Not q))
    | Not (Or (p, q)) ->
        And (nnfOrig (Not p), nnfOrig (Not q))
    | Not (Imp (p, q)) ->
        And (nnfOrig p, nnfOrig (Not q))
    | Not (Iff (p, q)) ->
        Or (And (nnfOrig p, nnfOrig (Not q)),
            And (nnfOrig (Not p), nnfOrig q))
    | fm -> fm

// pg. 52
// ------------------------------------------------------------------------- //
// Roll in simplification.                                                   //
// ------------------------------------------------------------------------- //

let nnf fm =
    nnfOrig <| psimplify fm

// pg. 53
// ------------------------------------------------------------------------- //
// Simple negation-pushing when we don't care to distinguish occurrences.    //
// ------------------------------------------------------------------------- //

// NOTE: Changed name from nenf to nenfOrig to avoid F# compiler error.
let rec nenfOrig fm =
    match fm with
    | Not (Not p) ->
        nenfOrig p
    | Not (And (p, q)) ->
        Or (nenfOrig (Not p), nenfOrig (Not q))
    | Not (Or (p, q)) ->
        And (nenfOrig (Not p), nenfOrig (Not q))
    | Not (Imp (p, q)) ->
        And (nenfOrig p, nenfOrig (Not q))
    | Not (Iff (p, q)) ->
        Iff (nenfOrig p, nenfOrig (Not q))
    | And (p, q) ->
        And (nenfOrig p, nenfOrig q)
    | Or (p, q) ->
        Or (nenfOrig p, nenfOrig q)
    | Imp (p, q) ->
        Or (nenfOrig (Not p), nenfOrig q)
    | Iff (p, q) ->
        Iff (nenfOrig p, nenfOrig q)
    | fm -> fm
        
let nenf fm =
    nenfOrig <| psimplify fm

// pg. 55
// ------------------------------------------------------------------------- //
// Disjunctive normal form (DNF) via truth tables.                           //
// ------------------------------------------------------------------------- //

let list_conj l =
    if l = [] then True
    else List.reduceBack mk_and l

let list_disj l = 
    if l = [] then False 
    else List.reduceBack mk_or l
   
let mk_lits pvs v =
    list_conj (List.map (fun p -> if eval p v then p else Not p) pvs)
        
let rec allsatvaluations subfn v pvs =
    match pvs with
    | [] ->
        if subfn v then [v] else []
    | p :: ps -> 
        let v' t q =
            if q = p then t
            else v q
        allsatvaluations subfn (v' false) ps @
        allsatvaluations subfn (v' true) ps
            
// NOTE: Changed name from distrib to distribOrig to avoid F# compiler error.
let dnfOrig fm =
    let pvs = atoms fm
    let satvals = allsatvaluations (eval fm) (fun s -> false) pvs
    list_disj (List.map (mk_lits (List.map (fun p -> Atom p) pvs)) satvals)

// pg. 57
// ------------------------------------------------------------------------- //
// DNF via distribution.                                                     //
// ------------------------------------------------------------------------- //

// NOTE: Changed name from distrib to distribOrig to avoid F# compiler error.
let rec distribOrig fm =
    match fm with
    | And (p, Or (q, r)) ->
        Or (distribOrig (And (p, q)), distribOrig (And (p, r)))
    | And (Or (p, q), r) ->
        Or (distribOrig (And (p, r)), distribOrig (And (q, r)))
    | _ -> fm
 
let rec rawdnf fm =
    match fm with
    | And (p, q) ->
        distribOrig <| And (rawdnf p, rawdnf q)
    | Or (p, q) ->
        Or (rawdnf p, rawdnf q)
    | _ -> fm

// pg. 58
// ------------------------------------------------------------------------- //
// A version using a list representation.                                    //
// ------------------------------------------------------------------------- //

let distrib s1 s2 =
    setify <| allpairs union s1 s2
    
let rec purednf fm =
    match fm with
    | And (p, q) ->
        distrib (purednf p) (purednf q)
    | Or (p, q) ->
        union (purednf p) (purednf q)
    | _ -> [[fm]]

// pg. 59
// ------------------------------------------------------------------------- //
// Filtering out trivial disjuncts (in this guise, contradictory).           //
// ------------------------------------------------------------------------- //

let trivial lits =
    let pos, neg = List.partition positive lits
    intersect pos (image negate neg) <> []

// pg. 59
// ------------------------------------------------------------------------- //
// With subsumption checking, done very naively (quadratic).                 //
// ------------------------------------------------------------------------- //

let simpdnf fm =
    if fm = False then [] 
    elif fm = True then [[]] 
    else
        let djs = List.filter (non trivial) (purednf (nnf fm))
        List.filter (fun d -> not (List.exists (fun d' -> psubset d' d) djs)) djs

// pg. 59
// ------------------------------------------------------------------------- //
// Mapping back to a formula.                                                //
// ------------------------------------------------------------------------- //

let dnf fm =
    List.map list_conj (simpdnf fm)
    |> list_disj

// pg. 60
// ------------------------------------------------------------------------- //
// Conjunctive normal form (CNF) by essentially the same code.               //
// ------------------------------------------------------------------------- //

let purecnf fm = image (image negate) (purednf (nnf (Not fm)))
    
let simpcnf fm =
    if fm = False then [[]]
    elif fm = True then []
    else
        let cjs = List.filter (non trivial) (purecnf fm)
        List.filter (fun c -> not (List.exists (fun c' -> psubset c' c) cjs)) cjs
            
let cnf fm =
    List.map list_disj (simpcnf fm)
    |> list_conj

