// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module order =
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

// pg. 265
// ========================================================================= //
// Term orderings.                                                           //
// ========================================================================= //

    let rec termsize tm =
        match tm with
        | Var x -> 1
        | Fn (f, args) ->
            (args, 1)
            ||> List.foldBack (fun t n ->
                termsize t + n)

// pg. 267
// ------------------------------------------------------------------------- //
// Lexicographic path order.                                                 //
// ------------------------------------------------------------------------- //

    let rec lexord ord l1 l2 =
        match l1, l2 with
        | h1 :: t1, h2 :: t2 ->
            if ord h1 h2 then
                List.length t1 = List.length t2
            else h1 = h2 && lexord ord t1 t2
        | _ -> false

    let rec lpo_gt w s t =
        match s, t with
        | _, Var x ->
            not (s = t)
            && mem x (fvt s)
        | Fn (f, fargs), Fn (g, gargs) ->
            List.exists (fun si -> lpo_ge w si t) fargs
            || List.forall (lpo_gt w s) gargs
            && (f = g
                && lexord (lpo_gt w) fargs gargs
                || w (f, List.length fargs) (g ,List.length gargs))
        | _ -> false

    and lpo_ge w s t =
        (s = t) || lpo_gt w s t

// pg. 267
// ------------------------------------------------------------------------- //
// More convenient way of specifying weightings.                             //
// ------------------------------------------------------------------------- //

    let weight lis (f, n) (g, m) =
        if f = g then
            n > m
        else
            earlier lis g f
