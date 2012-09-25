// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module skolem =
    open intro
    open formulas
    open prop
    open folMod

// ========================================================================= //
// Prenex and Skolem normal forms.                                           //
// ========================================================================= //
//
// pg. 140
// ------------------------------------------------------------------------- //
// Routine simplification. Like "psimplify" but with quantifier clauses.     //
// ------------------------------------------------------------------------- //

    // OCaml:  val simplify003 : expression  -> expression = <fun>
    // F#:     val simplify003 : fol formula -> fol formula
    let simplify003 fm =
        match fm with
        | Forall (x, p) ->
            if mem x (fv p) then fm else p
        | Exists (x, p) ->
            if mem x (fv p) then fm else p
        | _ ->
            psimplify1 fm

    let rec private simplifyImpl fm cont =
        match simplify1 fm with
        (* Cases which need to be recursively simplified. *)
        | Not p ->
            simplifyImpl p <| fun p' ->
                cont (simplify1 (Not p'))
        | And (p, q) ->
            simplifyImpl p <| fun p' ->
            simplifyImpl q <| fun q' ->
                cont (simplify1 (And (p', q')))
        | Or (p, q) ->
            simplifyImpl p <| fun p' ->
            simplifyImpl q <| fun q' ->
                cont (simplify1 (Or (p', q')))
        | Imp (p, q) ->
            simplifyImpl p <| fun p' ->
            simplifyImpl q <| fun q' ->
                cont (simplify1 (Imp (p', q')))
        | Iff (p, q) ->
            simplifyImpl p <| fun p' ->
            simplifyImpl q <| fun q' ->
                cont (simplify1 (Iff (p', q')))
        | Forall (x, p) ->
            simplifyImpl p <| fun p' ->
                cont (simplify1 (Forall (x, p')))
        | Exists (x, p) ->
            simplifyImpl p <| fun p' ->
                cont (simplify1 (Exists (x, p')))

        (* This formula can't be simplified any further. *)
        | fm ->
            cont fm

    // OCaml: val simplify : 'a formula -> 'a formula = <fun>
    // F#:    val simplify : 'a formula -> 'a formula
    let simplify fm =
        simplifyImpl fm id

// pg. 141
// ------------------------------------------------------------------------- //
// Negation normal form.                                                     //
// ------------------------------------------------------------------------- //

    let rec private nnfImpl fm cont =
        match fm with
        | And (p, q) ->
            nnfImpl p <| fun p' ->
            nnfImpl q <| fun q' ->
                cont (And (p', q'))
        | Or (p, q) ->
            nnfImpl p <| fun p' ->
            nnfImpl q <| fun q' ->
                cont (Or (p', q'))
        | Imp (p, q) ->
            nnfImpl (Not p) <| fun p' ->
            nnfImpl q <| fun q' ->
                cont (Or (p', q'))
        | Iff (p, q) ->
            nnfImpl p <| fun p' ->
            nnfImpl q <| fun q' ->
            nnfImpl (Not p) <| fun not_p' ->
            nnfImpl (Not q) <| fun not_q' ->
                cont (Or (And (p', q'), And (not_p', not_q')))
        | Not (Not p) ->
            nnfImpl p cont
        | Not (And (p, q)) ->
            nnfImpl (Not p) <| fun not_p' ->
            nnfImpl (Not q) <| fun not_q' ->
                cont (Or (not_p', not_q'))
        | Not (Or (p, q)) ->
            nnfImpl (Not p) <| fun not_p' ->
            nnfImpl (Not q) <| fun not_q' ->
                cont (And (not_p', not_q'))
        | Not (Imp (p, q)) ->
            nnfImpl p <| fun p' ->
            nnfImpl (Not q) <| fun not_q' ->
                cont (And (p', not_q'))
        | Not (Iff (p, q)) ->
            nnfImpl p <| fun p' ->
            nnfImpl (Not q) <| fun not_q' ->
            nnfImpl (Not p) <| fun not_p' ->
            nnfImpl q <| fun q' ->
                cont (Or (And (p', not_q'), And (not_p', q)))
        | Forall (x, p) ->
            nnfImpl p <| fun p' ->
                cont (Forall (x, p'))
        | Exists (x, p) ->
            nnfImpl p <| fun p' ->
                cont (Exists (x, p'))
        | Not (Forall (x, p)) ->
            nnfImpl (Not p) <| fun not_p' ->
                cont (Exists (x, not_p'))
        | Not (Exists (x, p)) ->
            nnfImpl (Not p) <| fun not_p' ->
                cont (Forall (x, not_p'))
        | fm ->
            cont fm

    let nnf fm =
        nnfImpl fm id

//    let rec nnf fm =
//        match fm with
//        | And (p, q) ->
//            And (nnf p, nnf q)
//        | Or (p, q) ->
//            Or (nnf p, nnf q)
//        | Imp (p, q) ->
//            Or (nnf (Not p), nnf q)
//        | Iff (p, q) ->
//            Or (And (nnf p, nnf q), And (nnf (Not p), nnf (Not q)))
//        | Not (Not p) ->
//            nnf p
//        | Not (And (p, q)) ->
//            Or (nnf (Not p), nnf (Not q))
//        | Not (Or (p, q)) ->
//            And (nnf (Not p), nnf (Not q))
//        | Not (Imp (p, q)) ->
//            And (nnf p, nnf (Not q))
//        | Not (Iff (p, q)) ->
//            Or (And (nnf p, nnf (Not q)), And (nnf (Not p), nnf q))
//        | Forall (x, p) ->
//            Forall (x, nnf p)
//        | Exists (x, p) ->
//            Exists (x, nnf p)
//        | Not (Forall (x, p)) ->
//            Exists (x, nnf (Not p))
//        | Not (Exists (x, p)) ->
//            Forall (x, nnf (Not p))
//        | _ -> fm

// pg. 143
// ------------------------------------------------------------------------- //
// Prenex normal form.                                                       //
// ------------------------------------------------------------------------- //

    let rec pullquants fm =
        match fm with
        | And (Forall (x, p), Forall (y, q)) ->
            pullq (true, true) fm mk_forall mk_and x y p q
        | Or (Exists(x, p), Exists(y, q)) ->
            pullq (true, true) fm mk_exists mk_or x y p q
        | And (Forall (x, p), q) ->
            pullq (true, false) fm mk_forall mk_and x x p q
        | And (p, Forall (y, q)) ->
            pullq (false, true) fm mk_forall mk_and y y p q
        | Or (Forall (x, p), q) ->
            pullq (true, false) fm mk_forall mk_or x x p q
        | Or (p, Forall (y, q)) ->
            pullq (false, true) fm mk_forall mk_or y y p q
        | And (Exists (x, p), q) ->
            pullq (true, false) fm mk_exists mk_and x x p q
        | And (p, Exists (y, q)) ->
            pullq (false, true) fm mk_exists mk_and y y p q
        | Or (Exists (x, p), q) ->
            pullq (true, false) fm mk_exists mk_or x x p q
        | Or (p, Exists (y, q)) ->
            pullq (false, true) fm mk_exists mk_or y y p q
        | _ -> fm

    and pullq(l,r) fm quant op x y p q =
        let z = variant x (fv fm)
        let p' = if l then subst (x |=> Var z) p else p
        let q' = if r then subst (y |=> Var z) q else q
        quant z (pullquants(op p' q'))


    let rec private prenexImpl fm cont =
        match fm with
        | Forall (x, p) ->
            prenexImpl p <| fun p' ->
                cont (Forall (x, p'))
        | Exists (x, p) ->
            prenexImpl p <| fun p' ->
                cont (Exists (x, p'))
        | And (p, q) ->
            prenexImpl p <| fun p' ->
            prenexImpl q <| fun q' ->
                cont (pullquants (And (p', q')))
        | Or (p, q) ->
            prenexImpl p <| fun p' ->
            prenexImpl q <| fun q' ->
                cont (pullquants (Or (p', q')))
        | _ ->
            cont fm

    let prenex fm =
        prenexImpl fm id

    let pnf fm =
        prenex (nnf (simplify004 fm))

// pg. 146
// ------------------------------------------------------------------------- //
// Get the functions in a term and formula.                                  //
// ------------------------------------------------------------------------- //

    let rec funcs tm =
        match tm with
        | Var x -> []
        | Fn (f, args) ->
            List.foldBack (union >>|> funcs) args [f,List.length args]

    let functions fm =
        atom_union (fun (R (p, a)) -> List.foldBack (union >>|> funcs) a []) fm

// pg. 149
// ------------------------------------------------------------------------- //
// Core Skolemization function.                                              //
// ------------------------------------------------------------------------- //

    let rec private skolemImpl fm fns cont =
        match fm with
        | Exists (y, p) ->
            let xs = fv fm
            let f = variant (if xs = [] then "c_" + y else "f_" + y) fns
            let fx = Fn (f, List.map Var xs)
            skolemImpl (subst (y |=> fx) p) (f :: fns) cont
        | Forall (x, p) ->
            skolemImpl p fns <| fun (p', fns') ->
                cont (Forall (x, p'), fns')
        | And (p, q) ->
            skolem2Impl And (p, q) fns cont
        | Or (p, q) ->
            skolem2Impl Or (p, q) fns cont
        | _ ->
            cont (fm, fns)

    and skolem2Impl cons (p, q) fns cont =
        skolemImpl p fns <| fun (p', fns') ->
        skolemImpl q fns' <| fun (q', fns'') ->
            cont (cons (p', q'), fns'')

    let skolem fm fns =
        skolemImpl fm fns id

    let skolem2 cons (p, q) fns =
        skolem2Impl cons (p, q) fns id

// pg. 149
// ------------------------------------------------------------------------- //
// Overall Skolemization function.                                           //
// ------------------------------------------------------------------------- //

    let askolemize fm =
        fst (skolem (nnf (simplify004 fm)) (List.map fst (functions fm)))

    let rec specialize fm =
        match fm with
        | Forall (x, p) ->
            specialize p
        | _ -> fm

    let skolemize fm =
        specialize (pnf (askolemize fm))
