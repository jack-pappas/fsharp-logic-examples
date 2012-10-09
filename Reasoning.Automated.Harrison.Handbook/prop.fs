// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.prop

open intro
open formulas

// pg. 28
// ========================================================================= //
// Basic stuff for propositional logic: datatype, parsing and printing.      //
// ========================================================================= //

type prop = P of string

// OCaml: val pname : prop -> string = <fun>
// F#:    val pname : prop -> string
let inline pname (P s) = s

// pg. 29
// ------------------------------------------------------------------------- //
// Parsing of propositional formulas.                                        //
// ------------------------------------------------------------------------- //

// OCaml: val parse_propvar : 'a -> string list -> prop formula * string list = <fun>
// F#:    val parse_propvar : 'a -> string list -> prop formula * string list
let parse_propvar vs inp =
    match inp with
    | p :: oinp when p <> "(" ->
        Atom (P p), oinp
    | _ ->
        failwith "parse_propvar"
        
// OCaml: val parse_prop_formula : string -> prop formula = <fun>
// F#:    val parse_prop_formula : (string -> prop formula)
let parse_prop_formula =
    parse_formula ((fun _ _ -> failwith ""), parse_propvar) []
    |> make_parser
                
// pg. 29
// ------------------------------------------------------------------------- //
// Printer.                                                                  //
// ------------------------------------------------------------------------- //

// OCaml: val print_propvar : 'a -> prop -> unit = <fun>
// F#:    val print_propvar : 'a -> prop -> unit
let fprint_propvar sw prec p =
    fprintf sw "%O" (pname p)

let inline print_propvar prec p = fprint_propvar stdout prec p
let inline sprint_propvar prec p = writeToString (fun sw -> fprint_propvar sw prec p)
        
// OCaml: val print_prop_formula : prop formula -> unit = <fun>
// F#:    val print_prop_formula : (prop formula -> unit)
let fprint_prop_formula sw = 
    fprint_qformula sw (fprint_propvar sw)

let inline print_prop_formula f = fprint_prop_formula stdout f
let inline sprint_prop_formula f = writeToString (fun sw -> fprint_prop_formula sw f)

// Added by EGT, updated by Phan
let inline fprint_prop_list sw xs = List.iter (fprint_prop_formula sw) xs

let inline print_prop_list fs = fprint_prop_list stdout fs
let inline sprint_prop_list fs = writeToString (fun sw -> fprint_prop_list sw fs)

// pg. 32
// ------------------------------------------------------------------------- //
// Interpretation of formulas.                                               //
// ------------------------------------------------------------------------- //

// Note: added cases for Exists and Forall to avoid compiler warning
// OCaml: val eval : 'a formula -> ('a -> bool) -> bool = <fun>
// F#:    val eval : 'a formula -> ('a -> bool) -> bool
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

// OCaml: val atoms : 'a formula -> 'a list = <fun>
// F#:    val atoms : 'a formula -> 'a list when 'a : comparison
let atoms fm = 
    atom_union (fun a -> [a]) fm

// pg. 35
// ------------------------------------------------------------------------- //
// Code to print out truth tables.                                           //
// ------------------------------------------------------------------------- //

// OCaml: val onallvaluations : (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> bool = <fun>
// F#:    val onallvaluations : (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> bool when 'a : equality
let rec onallvaluations subfn v ats =
    match ats with
    | [] -> subfn v
    | p :: ps ->
        let v' t q =
            if q = p then t
            else v q
        onallvaluations subfn (v' false) ps
        && onallvaluations subfn (v' true) ps
            
// OCaml: val print_truthtable : prop formula -> unit = <fun>
// F#:    val print_truthtable : prop formula -> unit
let print_truthtable fm =
    // [P "p"; P "q"; P "r"]
    let ats = atoms fm
    // 5 + 1 = length of false + length of space
    let width = List.foldBack (max >>|> String.length >>|> pname) ats 5 + 1
    let fixw s = s + String.replicate (width - String.length s) " "
    let truthstring p = fixw (if p then "true" else "false")
    let mk_row v =
        let lis = List.map (fun x -> truthstring (v x)) ats
        let ans = truthstring (eval fm v)
        printf "%s" (List.foldBack (+) lis ("| " + ans))
        printfn ""
        true
    let seperator = String.replicate (width * (List.length ats) + 9) "-"
    printfn "%s" (List.foldBack (fun s t -> fixw(pname s) + t) ats "| formula")
    printfn "%s" seperator
    let _ = onallvaluations mk_row (fun x -> false) ats
    printfn "%s" seperator
    printfn ""

// pg. 41
// ------------------------------------------------------------------------- //
// Recognizing tautologies.                                                  //
// ------------------------------------------------------------------------- //

// OCaml: val tautology : 'a formula -> bool = <fun>
// F#:    val tautology : 'a formula -> bool when 'a : comparison
let tautology fm =
    onallvaluations (eval fm) (fun s -> false) (atoms fm)

// pg. 41
// ------------------------------------------------------------------------- //
// Related concepts.                                                         //
// ------------------------------------------------------------------------- //

// OCaml: val unsatisfiable : 'a formula -> bool = <fun>
// F#:    val unsatisfiable : 'a formula -> bool when 'a : comparison
let unsatisfiable fm = 
    tautology <| Not fm
        
// OCaml: val satisfiable : 'a formula -> bool = <fun>
// F#:    val satisfiable : 'a formula -> bool when 'a : comparison
let satisfiable fm = 
    not <| unsatisfiable fm

// pg. 41
// ------------------------------------------------------------------------- //
// Substitution operation.                                                   //
// ------------------------------------------------------------------------- //

// OCaml: val psubst : ('a, 'a formula) func -> 'a formula -> 'a formula = <fun>
// F#:    val psubst : func<'a,'a formula>   -> ('a formula -> 'a formula) when 'a : comparison
let psubst subfn =
    onatoms <| fun p ->
        tryapplyd subfn p (Atom p)

// pg. 48
// ------------------------------------------------------------------------- //
// Dualization.                                                              //
// ------------------------------------------------------------------------- //

// OCaml: val dual : 'a formula -> 'a formula = <fun>
// F#:    val dual : 'a formula -> 'a formula
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

// OCaml: val psimplify1 : 'a formula -> 'a formula = <fun>
// F#:    val psimplify1 : 'a formula -> 'a formula
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
        
// OCaml: val psimplify : 'a formula -> 'a formula = <fun>
// F#:    val psimplify : 'a formula -> 'a formula
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

// OCaml: val negative : 'a formula -> bool = <fun>
// F#:    val negative : 'a formula -> bool
let negative = function
    | Not p -> true
    | _ -> false
    
// OCaml: val positive : 'a formula -> bool
// F#:    val positive : 'a formula -> bool
let positive lit = not <| negative lit
    
// OCaml: val negate : 'a formula -> 'a formula = <fun>
// F#:    val negate : 'a formula -> 'a formula
let negate = function
    | Not p -> p
    | p -> Not p

// pg. 52
// ------------------------------------------------------------------------- //
// Negation normal form.                                                     //
// ------------------------------------------------------------------------- //

// Note: Changed name from nnf to nnfOrig to avoid F# compiler error.
// OCaml: val nnf :     'a formula -> 'a formula = <fun>
// F#:    val nnfOrig : 'a formula -> 'a formula
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

// OCaml: val nnf : 'a formula -> 'a formula = <fun>
// F#:    val nnf : 'a formula -> 'a formula
let nnf fm =
    nnfOrig <| psimplify fm

// pg. 53
// ------------------------------------------------------------------------- //
// Simple negation-pushing when we don't care to distinguish occurrences.    //
// ------------------------------------------------------------------------- //

// Note: Changed name from nenf to nenfOrig to avoid F# compiler error.
// OCaml: val nenf :     'a formula -> 'a formula = <fun>
// F#:    val nenfOrig : 'a formula -> 'a formula
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
        
// OCaml: val nenf : 'a formula -> 'a formula = <fun>
// F#:    val nenf : 'a formula -> 'a formula
let nenf fm =
    nenfOrig <| psimplify fm

// pg. 55
// ------------------------------------------------------------------------- //
// Disjunctive normal form (DNF) via truth tables.                           //
// ------------------------------------------------------------------------- //

// OCaml: val list_conj : 'a formula list -> 'a formula = <fun>
// F#:    val list_conj : 'a formula list -> 'a formula when 'a : equality
let list_conj l =
    if l = [] then True
    else end_itlist mk_and l

// OCaml: val list_disj : 'a formula list -> 'a formula = <fun>
// F#:    val list_disj : 'a formula list -> 'a formula when 'a : equality
let list_disj l = 
    if l = [] then False 
    else end_itlist mk_or l
        
// OCaml: val mk_lits : 'a formula list -> ('a -> bool) -> 'a formula = <fun>
// F#:    val mk_lits : 'a formula list -> ('a -> bool) -> 'a formula when 'a : equality
let mk_lits pvs v =
    list_conj (List.map (fun p -> if eval p v then p else Not p) pvs)
        
// OCaml: val allsatvaluations : (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> ('a -> bool) list = <fun>
// F#:    val allsatvaluations :  (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> ('a -> bool) list when 'a : equality
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
            
// Note: Changed name from distrib to distribOrig to avoid F# compiler error.
// OCaml: val dnf :     'a formula -> 'a formula = <fun>
// F#:    val dnfOrig : 'a formula -> 'a formula when 'a : comparison
let dnfOrig fm =
    let pvs = atoms fm
    let satvals = allsatvaluations (eval fm) (fun s -> false) pvs
    list_disj (List.map (mk_lits (List.map (fun p -> Atom p) pvs)) satvals)

// pg. 57
// ------------------------------------------------------------------------- //
// DNF via distribution.                                                     //
// ------------------------------------------------------------------------- //

// Note: Changed name from distrib to distribOrig to avoid F# compiler error.
// OCaml: val distrib :     'a formula -> 'a formula = <fun>
// F#:    val distribOrig : 'a formula -> 'a formula
let rec distribOrig fm =
    match fm with
    | And (p, Or (q, r)) ->
        Or (distribOrig (And (p, q)), distribOrig (And (p, r)))
    | And (Or (p, q), r) ->
        Or (distribOrig (And (p, r)), distribOrig (And (q, r)))
    | _ -> fm
        
// OCaml: val rawdnf : 'a formula -> 'a formula = <fun>
// F#:    val rawdnf : 'a formula -> 'a formula
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

// OCaml: val distrib : 'a list list -> 'a list list -> 'a list list = <fun>
// F#:    val distrib : 'a list list -> 'a list list -> 'a list list when 'a : comparison
let distrib s1 s2 =
    setify <| allpairs union s1 s2
    
// OCaml: val purednf : 'a formula -> 'a formula list list = <fun>
// F#:    val purednf : 'a formula -> 'a formula list list when 'a : comparison
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

// OCaml: val trivial : 'a formula list -> bool = <fun>
// F#:    val trivial : 'a formula list -> bool when 'a : comparison
let trivial lits =
    let pos, neg = List.partition positive lits
    intersect pos (image negate neg) <> []

// pg. 59
// ------------------------------------------------------------------------- //
// With subsumption checking, done very naively (quadratic).                 //
// ------------------------------------------------------------------------- //

// OCaml: val simpdnf : 'a formula -> 'a formula list list = <fun>
// F#:    val simpdnf : 'a formula -> 'a formula list list when 'a : comparison
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

// OCaml: val dnf : 'a formula -> 'a formula = <fun>
// F:     val dnf : 'a formula -> 'a formula when 'a : comparison
let dnf fm =
    List.map list_conj (simpdnf fm)
    |> list_disj

// pg. 60
// ------------------------------------------------------------------------- //
// Conjunctive normal form (CNF) by essentially the same code.               //
// ------------------------------------------------------------------------- //

// OCaml: val purecnf : 'a formula -> 'a formula list list = <fun>
// F#:    val purecnf : 'a formula -> 'a formula list list when 'a : comparison
let purecnf fm = image (image negate) (purednf (nnf (Not fm)))
    
// OCaml: val simpcnf : 'a formula -> 'a formula list list = <fun>
// F#:    val simpcnf : 'a formula -> 'a formula list list when 'a : comparison
let simpcnf fm =
    if fm = False then [[]]
    elif fm = True then []
    else
        let cjs = List.filter (non trivial) (purecnf fm)
        List.filter (fun c -> not (List.exists (fun c' -> psubset c' c) cjs)) cjs
            
// OCaml: val cnf : 'a formula -> 'a formula = <fun>
// F#:    val cnf : 'a formula -> 'a formula when 'a : comparison
let cnf fm =
    List.map list_disj (simpcnf fm)
    |> list_conj

