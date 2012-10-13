// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.formulas

// pg. 26
// ========================================================================= //
// Polymorphic type of formulas with parser and printer.                     //
// ========================================================================= //

type formula<'a> =
    | False
    | True
    | Atom of 'a
    | Not of formula<'a>
    | And of formula<'a> * formula<'a>
    | Or of formula<'a> * formula<'a>
    | Imp of formula<'a> * formula<'a>
    | Iff of formula<'a> * formula<'a>
    | Forall of string * formula<'a>
    | Exists of string * formula<'a>

// pg. 623
// ------------------------------------------------------------------------- //
// General parsing of iterated infixes.                                      //
// ------------------------------------------------------------------------- //

let rec parse_ginfix opsym opupdate sof subparser inp =
    let e1, inp1 = subparser inp
    match inp1 with
    | hd :: tl when hd = opsym ->
        parse_ginfix opsym opupdate (opupdate sof e1) subparser tl
    | _ ->
        sof e1, inp1

let parse_left_infix opsym opcon =
    parse_ginfix opsym (fun f e1 e2 -> opcon (f e1, e2)) id

let parse_right_infix opsym opcon =
    parse_ginfix opsym (fun f e1 e2 -> f <| opcon (e1, e2)) id

let parse_list opsym =
    parse_ginfix opsym (fun f e1 e2 -> (f e1) @ [e2]) (fun x -> [x])

// pg. 624
// ------------------------------------------------------------------------- //
// Other general parsing combinators.                                        //
// ------------------------------------------------------------------------- //

let inline papply f (ast, rest) =
    f ast, rest

let nextin inp tok =
    match inp with
    | hd :: _ when hd = tok -> true
    | _ -> false

let parse_bracketed subparser cbra inp =
    let ast, rest = subparser inp
    if nextin rest cbra then
        ast, List.tail rest
    else failwith "Closing bracket expected"

// pg. 625
// ------------------------------------------------------------------------- //
// Parsing of formulas, parametrized by atom parser "pfn".                   //
// ------------------------------------------------------------------------- //

let rec parse_atomic_formula (ifn, afn) vs inp =
    match inp with
    | [] ->
        failwith "formula expected"
    | "false" :: rest ->
        False, rest
    | "true" :: rest ->
        True, rest
    | "(" :: rest -> 
        try ifn vs inp
        with _ ->
            parse_bracketed (parse_formula (ifn, afn) vs) ")" rest
    | "~" :: rest ->
        papply Not (parse_atomic_formula (ifn, afn) vs rest)
    | "forall" :: x :: rest ->
        parse_quant (ifn, afn) (x :: vs) Forall x rest
    | "exists" :: x :: rest ->
        parse_quant (ifn, afn) (x :: vs) Exists x rest
    | _ -> afn vs inp

and parse_quant (ifn, afn) vs qcon x inp =
    match inp with
    | [] ->
        failwith "Body of quantified term expected"
    | y :: rest ->
        if y = "." then
            parse_formula (ifn, afn) vs rest
        else
            parse_quant (ifn, afn) (y :: vs) qcon y rest
        |> papply (fun fm ->
            qcon (x, fm))

and parse_formula (ifn, afn) vs inp =
    parse_right_infix "<=>" Iff
        (parse_right_infix "==>" Imp
            (parse_right_infix "\\/" Or
                (parse_right_infix "/\\" And
                    (parse_atomic_formula (ifn, afn) vs)))) inp

// pg. 626
// ------------------------------------------------------------------------- //
// Printing of formulas, parametrized by atom printer.                       //
// ------------------------------------------------------------------------- //

// NOTE: No use of OCaml format module. i.e. print_box removed during conversion
let fbracket tw p n f x y =
    if p then fprintf tw "("
    f x y
    if p then fprintf tw ")"

let rec strip_quant fm =
    match fm with
    | Forall (x, (Forall (y, p) as yp))
    | Exists (x, (Exists (y, p) as yp)) ->
        let xs, q = strip_quant yp
        (x :: xs), q
    | Forall (x, p)
    | Exists (x, p) ->
        [x], p
    | _ ->
        [], fm


// NOTE: No use of OCaml format module. i.e. print_box removed during conversion
let fprint_formula tw pfn =
    let rec print_formula pr fm =
        match fm with
        | False ->
            fprintf tw "false"
        | True ->
            fprintf tw "true"
        | Atom pargs ->
            pfn pr pargs
        | Not p ->
            fbracket tw (pr > 10) 1 (print_prefix 10) "~" p
        | And (p, q) ->
            fbracket tw (pr > 8) 0 (print_infix 8 "/\\") p q
        | Or (p, q) ->
            fbracket tw (pr > 6) 0 (print_infix  6 "\\/") p q
        | Imp (p, q) ->
            fbracket tw (pr > 4) 0 (print_infix 4 "==>") p q
        | Iff (p, q) ->
            fbracket tw (pr > 2) 0 (print_infix 2 "<=>") p q
        | Forall (x, p) ->
            fbracket tw (pr > 0) 2 print_qnt "forall" (strip_quant fm)
        | Exists (x, p) ->
            fbracket tw (pr > 0) 2 print_qnt "exists" (strip_quant fm)

    and print_qnt qname (bvs, bod) =
        fprintf tw "%s" qname
        List.iter (fprintf tw " %s") bvs
        fprintf tw ". "
        print_formula 0 bod

    and print_prefix newpr sym p =
        fprintf tw "%s" sym
        print_formula (newpr + 1) p

    and print_infix newpr sym p q =
        print_formula (newpr + 1) p
        fprintf tw " %s " sym
        print_formula newpr q

    print_formula 0

// NOTE: No use of OCaml format module. i.e. print_box removed during conversion
// pg. 28
let fprint_qformula tw pfn fm =
    fprintf tw "<<"
    fprint_formula tw pfn fm
    fprintf tw ">>"

// Actuals functions to call from other modules
let inline print_formula pfn fm = fprint_formula stdout pfn fm
let inline sprint_formula pfn fm = writeToString (fun sw -> fprint_formula sw pfn fm)
    
let inline print_qformula pfn fm = fprint_qformula stdout pfn fm
let inline sprint_qformula pfn fm = writeToString (fun sw -> fprint_qformula sw pfn fm)

// pg.30
// ------------------------------------------------------------------------- //
// OCaml won't let us use the constructors.                                  //
// ------------------------------------------------------------------------- //

let inline mk_and p q = And (p, q)

let inline mk_or p q = Or (p, q)

let inline mk_imp p q = Imp (p, q)

let inline mk_iff p q = Iff (p, q)

let inline mk_forall x p = Forall (x, p)

let inline mk_exists x p = Exists (x, p)

// pg. 30
// ------------------------------------------------------------------------- //
// Destructors.                                                              //
// ------------------------------------------------------------------------- //

let dest_iff = function
    | Iff (p, q) ->
        p, q
    | _ ->
        failwith "dest_iff"

let dest_and = function
    | And (p, q) ->
        p, q
    | _ ->
        failwith "dest_and"

let rec conjuncts = function
    | And (p, q) ->
        conjuncts p @ conjuncts q 
    | fm -> [fm]

let dest_or = function
    | Or (p, q) ->
        p, q
    | _ ->
        failwith "dest_or"

let rec disjuncts = function
    | Or (p, q) ->
        disjuncts p @ disjuncts q 
    | fm -> [fm]

let dest_imp = function
    | Imp (p, q) ->
        p, q
    | _ ->
        failwith "dest_imp"

let inline antecedent fm =
    fst <| dest_imp fm

let inline consequent fm =
    snd <| dest_imp fm

// pg. 31
// ------------------------------------------------------------------------- //
// Apply a function to the atoms, otherwise keeping structure.               //
// ------------------------------------------------------------------------- //

let rec onatoms f fm =
    match fm with
    | Atom a ->
        f a
    | Not p ->
        Not (onatoms f p)
    | And (p, q) ->
        And (onatoms f p, onatoms f q)
    | Or (p, q) ->
        Or (onatoms f p,onatoms f q)
    | Imp (p, q) ->
        Imp (onatoms f p, onatoms f q)
    | Iff (p, q) ->
        Iff (onatoms f p, onatoms f q)
    | Forall (x, p) ->
        Forall (x, onatoms f p)
    | Exists (x, p) ->
        Exists (x, onatoms f p)
    | _ -> fm

// pg. 31
// ------------------------------------------------------------------------- //
// Formula analog of list iterator "List.foldBack".                          //
// ------------------------------------------------------------------------- //

let rec overatoms f fm b =
    match fm with
    | Atom a ->
        f a b
    | Not p ->
        overatoms f p b
    | And (p, q)
    | Or (p, q)
    | Imp (p, q)
    | Iff (p, q) ->
        overatoms f p (overatoms f q b)
    | Forall (x, p)
    | Exists (x, p) ->
        overatoms f p b
    | _ -> b

// pg. 32
// ------------------------------------------------------------------------- //
// Special case of a union of the results of a function over the atoms.      //
// ------------------------------------------------------------------------- //

let atom_union f fm =
    (fm, [])
    ||> overatoms (fun h t ->
        (f h) @ t)
    |> setify


    

