// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module prop =
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
    let print_propvar prec p =
        printf "%O" (pname p)
        
    // OCaml: val print_prop_formula : prop formula -> unit = <fun>
    // F#:    val print_prop_formula : (prop formula -> unit)
    let print_prop_formula : (prop formula -> unit) = 
        print_qformula print_propvar

    // Added by EGT
    let rec print_prop_list x =
        match x with
        | []   -> ()
        | h::t -> 
            print_prop_formula h
            print_prop_list t

// pg. 32
// ------------------------------------------------------------------------- //
// Interpretation of formulas.                                               //
// ------------------------------------------------------------------------- //

    let rec private evalImpl fm v cont =
        match fm with
        | False ->
            cont false
        | True ->
            cont true
        | Atom x ->
            cont (v x)
        | Not p ->
            evalImpl p v <| fun p' ->
                cont (not p')
        | And (p, q) ->
            evalImpl p v <| fun p' ->
            evalImpl q v <| fun q' ->
                cont (p' && q')
        | Or (p, q) ->
            evalImpl p v <| fun p' ->
            evalImpl q v <| fun q' ->
                cont (p' || q')
        | Imp (p, q) ->
            evalImpl p v <| fun p' ->
            evalImpl q v <| fun q' ->
                cont (not p' || q')
        | Iff (p, q) ->
            evalImpl p v <| fun p' ->
            evalImpl q v <| fun q' ->
                cont (p' = q')
        | Exists _
        | Forall _ ->
            failwith "Not part of propositional logic."

    // Note: added cases for Exists and Forall to avoid compiler warning
    // OCaml: val eval : 'a formula -> ('a -> bool) -> bool = <fun>
    // F#:    val eval : 'a formula -> ('a -> bool) -> bool
    let eval fm v =
        evalImpl fm v id

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

    let rec onallvaluationsImpl subfn v ats cont =
        match ats with
        | [] ->
            cont (subfn v)
        | p :: ps ->
            let v' t q =
                if q = p then t else v q

            onallvaluationsImpl subfn (v' false) ps <| fun lhs ->
            onallvaluationsImpl subfn (v' true) ps <| fun rhs ->
                cont (lhs && rhs)

    // OCaml: val onallvaluations : (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> bool = <fun>
    // F#:    val onallvaluations : (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> bool when 'a : equality
    let onallvaluations subfn v ats =
        onallvaluationsImpl subfn v ats id
            
    // OCaml: val print_truthtable : prop formula -> unit = <fun>
    // F#:    val print_truthtable : prop formula -> unit
    let print_truthtable fm =
        // [P "p"; P "q"; P "r"]
        let ats = atoms fm
        // 5 + 1 = length of false + length of space
        // OPTIMIZE : Use List.maxBy instead of List.foldBack here.
        let width = List.foldBack (max << String.length << pname) ats 5 + 1
        // OPTIMIZE : Use String.PadRight instead of String.replicate
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
        onallvaluations (eval fm) (fun _ -> false) (atoms fm)

// pg. 41
// ------------------------------------------------------------------------- //
// Related concepts.                                                         //
// ------------------------------------------------------------------------- //

    // OCaml: val unsatisfiable : 'a formula -> bool = <fun>
    // F#:    val unsatisfiable : 'a formula -> bool when 'a : comparison
    let inline unsatisfiable fm =
        tautology <| Not fm
        
    // OCaml: val satisfiable : 'a formula -> bool = <fun>
    // F#:    val satisfiable : 'a formula -> bool when 'a : comparison
    let inline satisfiable fm =
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

    let rec private dualImpl fm cont =
        match fm with
        | False ->
            cont True
        | True ->
            cont False
        | Atom p ->
            cont fm
        | Not p ->
            dualImpl p <| fun p' ->
                cont (Not p')
        | And (p, q) ->
            dualImpl p <| fun p' ->
            dualImpl q <| fun q' ->
                cont (Or (p', q'))
        | Or (p, q) ->
            dualImpl p <| fun p' ->
            dualImpl q <| fun q' ->
                cont (And (p', q'))
        | _ ->
            failwith "Formula involves connectives ==> or <=>"

    // OCaml: val dual : 'a formula -> 'a formula = <fun>
    // F#:    val dual : 'a formula -> 'a formula
    let dual fm =
        dualImpl fm id

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

    let rec private psimplifyImpl fm cont =
        match psimplify1 fm with
        (* Cases which need to be recursively simplified. *)
        | Not p ->
            psimplifyImpl p <| fun p' ->
                cont (psimplify1 (Not p'))
        | And (p, q) ->
            psimplifyImpl p <| fun p' ->
            psimplifyImpl q <| fun q' ->
                cont (psimplify1 (And (p', q')))
        | Or (p, q) ->
            psimplifyImpl p <| fun p' ->
            psimplifyImpl q <| fun q' ->
                cont (psimplify1 (Or (p', q')))
        | Imp (p, q) ->
            psimplifyImpl p <| fun p' ->
            psimplifyImpl q <| fun q' ->
                cont (psimplify1 (Imp (p', q')))
        | Iff (p, q) ->
            psimplifyImpl p <| fun p' ->
            psimplifyImpl q <| fun q' ->
                cont (psimplify1 (Iff (p', q')))

        (* This formula can't be simplified any further. *)
        | fm ->
            cont fm

    // OCaml: val psimplify : 'a formula -> 'a formula = <fun>
    // F#:    val psimplify : 'a formula -> 'a formula
    let psimplify fm =
        psimplifyImpl fm id


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

    let rec private nnfOrigImpl fm cont =
        match fm with
        | And (p, q) ->
            nnfOrigImpl p <| fun p' ->
            nnfOrigImpl q <| fun q' ->
                cont (And (p', q'))
        | Or (p, q) ->
            nnfOrigImpl p <| fun p' ->
            nnfOrigImpl q <| fun q' ->
                cont (Or (p', q'))
        | Imp (p, q) ->
            nnfOrigImpl (Not p) <| fun p' ->
            nnfOrigImpl q <| fun q' ->
                cont (Or (p', q'))
        | Iff (p, q) ->
            nnfOrigImpl p <| fun p' ->
            nnfOrigImpl q <| fun q' ->
            nnfOrigImpl (Not p) <| fun not_p' ->
            nnfOrigImpl (Not q) <| fun not_q' ->
                cont (Or (And (p', q'), And (not_p', not_q')))
        | Not (Not p) ->
            nnfOrigImpl p cont
        | Not (And (p, q)) ->
            nnfOrigImpl (Not p) <| fun not_p' ->
            nnfOrigImpl (Not q) <| fun not_q' ->
                cont (Or (not_p', not_q'))
        | Not (Or (p, q)) ->
            nnfOrigImpl (Not p) <| fun not_p' ->
            nnfOrigImpl (Not q) <| fun not_q' ->
                cont (And (not_p', not_q'))
        | Not (Imp (p, q)) ->
            nnfOrigImpl p <| fun p' ->
            nnfOrigImpl (Not q) <| fun not_q' ->
                cont (And (p', not_q'))
        | Not (Iff (p, q)) ->
            nnfOrigImpl p <| fun p' ->
            nnfOrigImpl (Not q) <| fun not_q' ->
            nnfOrigImpl (Not p) <| fun not_p' ->
            nnfOrigImpl q <| fun q' ->
                cont (Or (And (p', not_q'), And (not_p', q')))
        | fm ->
            cont fm

    // Note: Changed name from nnf to nnfOrig to avoid F# compiler error.
    // OCaml: val nnf :     'a formula -> 'a formula = <fun>
    // F#:    val nnfOrig : 'a formula -> 'a formula
    let nnfOrig fm =
        nnfOrigImpl fm id


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

    //
    let rec private nenfOrigImpl fm cont =
        match fm with
        | Not (Not p) ->
            nenfOrigImpl p cont
        | Not (And (p, q)) ->
            nenfOrigImpl (Not p) <| fun not_p' ->
            nenfOrigImpl (Not q) <| fun not_q' ->
                cont (Or (not_p', not_q'))
        | Not (Or (p, q)) ->
            nenfOrigImpl (Not p) <| fun not_p' ->
            nenfOrigImpl (Not q) <| fun not_q' ->
                cont (And (not_p', not_q'))
        | Not (Imp (p, q)) ->
            nenfOrigImpl p <| fun p' ->
            nenfOrigImpl (Not q) <| fun not_q' ->
                cont (And (p', not_q'))
        | Not (Iff (p, q)) ->
            nenfOrigImpl p <| fun p' ->
            nenfOrigImpl (Not q) <| fun not_q' ->
                cont (Iff (p', not_q'))
        | And (p, q) ->
            nenfOrigImpl p <| fun p' ->
            nenfOrigImpl q <| fun q' ->
                cont (And (p', q'))
        | Or (p, q) ->
            nenfOrigImpl p <| fun p' ->
            nenfOrigImpl q <| fun q' ->
                cont (Or (p', q'))
        | Imp (p, q) ->
            nenfOrigImpl q <| fun q' ->
            nenfOrigImpl (Not p) <| fun not_p' ->
                cont (Or (not_p', q'))
        | Iff (p, q) ->
            nenfOrigImpl p <| fun p' ->
            nenfOrigImpl q <| fun q' ->
                cont (Iff (p', q'))
        | fm ->
            cont fm

    // Note: Changed name from nenf to nenfOrig to avoid F# compiler error.
    // OCaml: val nenf :     'a formula -> 'a formula = <fun>
    // F#:    val nenfOrig : 'a formula -> 'a formula
    let nenfOrig fm =
        nenfOrigImpl fm id
        
    // OCaml: val nenf : 'a formula -> 'a formula = <fun>
    // F#:    val nenf : 'a formula -> 'a formula
    let nenf fm =
        psimplify fm
        |> nenfOrig

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
        pvs
        |> List.map (fun p ->
            if eval p v then p else Not p)
        |> list_conj
        
    // OCaml: val allsatvaluations : (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> ('a -> bool) list = <fun>
    // F#:    val allsatvaluations :  (('a -> bool) -> bool) -> ('a -> bool) -> 'a list -> ('a -> bool) list when 'a : equality
    // TODO : Optimize using continuation-passing style.
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
        allsatvaluations (eval fm) (fun _ -> false) pvs
        |> List.map (mk_lits (List.map Atom pvs))
        |> list_disj

// pg. 57
// ------------------------------------------------------------------------- //
// DNF via distribution.                                                     //
// ------------------------------------------------------------------------- //

    let rec private distribOrigImpl fm cont =
        match fm with
        | And (p, Or (q, r)) ->
            distribOrigImpl (And (p, q)) <| fun p' ->
            distribOrigImpl (And (p, r)) <| fun q' ->
                cont (Or (p', q'))
        | And (Or (p, q), r) ->
            distribOrigImpl (And (p, r)) <| fun p' ->
            distribOrigImpl (And (q, r)) <| fun q' ->
                cont (Or (p', q'))
        | fm ->
            cont fm

    // Note: Changed name from distrib to distribOrig to avoid F# compiler error.
    // OCaml: val distrib :     'a formula -> 'a formula = <fun>
    // F#:    val distribOrig : 'a formula -> 'a formula
    let distribOrig fm =
        distribOrigImpl fm id

    //
    let rec private rawdnfImpl fm cont =
        match fm with
        | And (p, q) ->
            rawdnfImpl p <| fun p' ->
            rawdnfImpl q <| fun q' ->
                cont (distribOrig (And (p, q)))
        | Or (p, q) ->
            rawdnfImpl p <| fun p' ->
            rawdnfImpl q <| fun q' ->
                cont (Or (p', q'))
        | fm ->
            cont fm

    // OCaml: val rawdnf : 'a formula -> 'a formula = <fun>
    // F#:    val rawdnf : 'a formula -> 'a formula
    let rawdnf fm =
        rawdnfImpl fm id

// pg. 58
// ------------------------------------------------------------------------- //
// A version using a list representation.                                    //
// ------------------------------------------------------------------------- //

    // OCaml: val distrib : 'a list list -> 'a list list -> 'a list list = <fun>
    // F#:    val distrib : 'a list list -> 'a list list -> 'a list list when 'a : comparison
    let distrib s1 s2 =
        allpairs union s1 s2
        |> setify

    //
    let rec private purednfImpl fm cont =
        match fm with
        | And (p, q) ->
            purednfImpl p <| fun p' ->
            purednfImpl q <| fun q' ->
                cont (distrib p' q')
        | Or (p, q) ->
            purednfImpl p <| fun p' ->
            purednfImpl q <| fun q' ->
                cont (union p' q')
        | _ ->
            cont [[fm]]

    // OCaml: val purednf : 'a formula -> 'a formula list list = <fun>
    // F#:    val purednf : 'a formula -> 'a formula list list when 'a : comparison
    let purednf fm =
        purednfImpl fm id

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
            let djs =
                nnf fm
                |> purednf
                |> List.filter (non trivial)
            List.filter (fun d -> not (List.exists (fun d' -> psubset d' d) djs)) djs

// pg. 59
// ------------------------------------------------------------------------- //
// Mapping back to a formula.                                                //
// ------------------------------------------------------------------------- //

    // OCaml: val dnf : 'a formula -> 'a formula = <fun>
    // F:     val dnf : 'a formula -> 'a formula when 'a : comparison
    let dnf fm =
        simpdnf fm
        |> List.map list_conj
        |> list_disj

// pg. 60
// ------------------------------------------------------------------------- //
// Conjunctive normal form (CNF) by essentially the same code.               //
// ------------------------------------------------------------------------- //

    // OCaml: val purecnf : 'a formula -> 'a formula list list = <fun>
    // F#:    val purecnf : 'a formula -> 'a formula list list when 'a : comparison
    let purecnf fm =
        nnf (Not fm)
        |> purednf
        |> image (image negate)
    
    // OCaml: val simpcnf : 'a formula -> 'a formula list list = <fun>
    // F#:    val simpcnf : 'a formula -> 'a formula list list when 'a : comparison
    let simpcnf fm =
        if fm = False then [[]]
        elif fm = True then []
        else
            let cjs =
                purecnf fm
                |> List.filter (non trivial)
            List.filter (fun c -> not (List.exists (fun c' -> psubset c' c) cjs)) cjs
            
    // OCaml: val cnf : 'a formula -> 'a formula = <fun>
    // F#:    val cnf : 'a formula -> 'a formula when 'a : comparison
    let cnf fm =
        simpcnf fm
        |> List.map list_disj
        |> list_conj

