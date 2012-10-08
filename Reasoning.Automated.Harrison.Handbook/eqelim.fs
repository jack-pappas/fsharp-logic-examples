// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.eqelim

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

// ========================================================================= //
// Equality elimination including Brand transformation and relatives.        //
// ========================================================================= //

// pg.291
// ------------------------------------------------------------------------- //
// Brand's S and T modifications on clauses.                                 //
// ------------------------------------------------------------------------- //

// val modify_S : fol formula list -> fol formula list list
let rec modify_S cl =
        // val dest_eq : fol formula -> (term * term) option
        let dest_eq fm =
            match fm with
            | Atom (R ("=", [s;t])) ->
                Some(s, t)
            | _ -> None

        // val tryfind : ('a -> ('b * 'c) option) -> 'a list -> ('b * 'c) option
        let rec tryfind dest_eq l =
            match l with
            | [] -> None
            | h :: t ->
                match dest_eq h with
                | Some _ as x -> x
                | None -> tryfind dest_eq t

        match tryfind dest_eq cl with
        | None -> [cl]
        | Some (s, t) -> 
            let eq1 = mk_eq s t 
            let eq2 = mk_eq t s
            let sub = modify_S (subtract cl [eq1])
            List.map (insert eq1) sub @ List.map (insert eq2) sub

let rec modify_T cl =
    match cl with
    | [] -> []
    | (Atom (R ("=", [s; t])) as eq) :: ps ->
        let ps' = modify_T ps
        let w = Var (variant "w" (List.foldBack (union >>|> fv) ps' (fv eq)))
        Not (mk_eq t w) :: (mk_eq s w) :: ps'
    | p :: ps ->
        p :: (modify_T ps)


// pg. 294
// ------------------------------------------------------------------------- //
// Finding nested non-variable subterms.                                     //
// ------------------------------------------------------------------------- //

// val is_nonvar : term -> bool
let is_nonvar = function
    | Var x -> false
    | _ -> true

let find_nestnonvar tm =
    match tm with
    | Var x -> failwith "findnvsubt"
    | Fn (f, args) ->
        List.find is_nonvar args

let rec find_nvsubterm fm =
    match fm with
    | Atom (R ("=", [s; t])) ->
        tryfind find_nestnonvar [s;t]
    | Atom (R (p, args)) ->
        List.find is_nonvar args
    | Not p ->
        find_nvsubterm p

// pg. 295
// ------------------------------------------------------------------------- //
// Replacement (substitution for non-variable) in term and literal.          //
// ------------------------------------------------------------------------- //

// OCaml: val replacet : (term, term) func      -> term -> term = <fun>
// F#:  val replacet : func<term,term>        -> term -> term
let rec replacet rfn tm =
    try apply rfn tm
    with Failure _ ->
        match tm with
        | Fn (f, args) ->
            Fn (f, List.map (replacet rfn) args)
        | _ -> tm

let replace rfn =
    onformula (replacet rfn)

// pg. 295
// ------------------------------------------------------------------------- //
// E-modification of a clause.                                               //
// ------------------------------------------------------------------------- //

let rec emodify fvs cls =
    try
        let t = tryfind find_nvsubterm cls
        let w = variant "w" fvs
        let cls' = List.map (replace (t |=> Var w)) cls
        emodify (w :: fvs) (Not (mk_eq t (Var w)) :: cls')
    with Failure _ ->
        cls

let modify_E cls = emodify (List.foldBack (union >>|> fv) cls []) cls

// pg. 296
// ------------------------------------------------------------------------- //
// Overall Brand transformation.                                             //
// ------------------------------------------------------------------------- //

let brand cls =
    let cls1 = List.map modify_E cls
    let cls2 = List.foldBack (union >>|> modify_S) cls1 []
    [mk_eq (Var "x") (Var "x")] :: (List.map modify_T cls2)

// pg. 296
// ------------------------------------------------------------------------- //
// Incorporation into MESON.                                                 //
// ------------------------------------------------------------------------- //

let bpuremeson fm =
    let cls = brand (simpcnf (specialize (pnf fm)))
    let rules = List.foldBack ((@) >>|> contrapositives) cls []
    deepen (fun n ->
        mexpand002 rules [] False id (undefined, n, 0)
        |> ignore
        n) 0

let bmeson fm =
    let fm1 = askolemize (Not (generalize fm))
    List.map (bpuremeson >>|> list_conj) (simpdnf fm1)

// Moved from section - Older stuff not now in the text
// to here because it is still in the text.  EGT
let emeson fm = meson002 (equalitize fm)



