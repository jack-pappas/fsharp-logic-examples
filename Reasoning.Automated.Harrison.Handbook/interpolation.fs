// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Jack Pappas, Eric Taucher                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// Implementation/proof of the Craig-Robinson interpolation theorem.         //
//                                                                           //
// This is based on the proof in Kreisel & Krivine, which works very nicely  //
// in our context.                                                           //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.interpolation

    open FSharpx.Compatibility.OCaml.Num

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
    open decidable
    open qelim
    open cooper
    open complex
    open real
    open grobner
    open geom

    // pg. 428
    // ------------------------------------------------------------------------- //
    // Interpolation for propositional logic.                                    //
    // ------------------------------------------------------------------------- //

    let pinterpolate p q =
        let orify a r = Or (psubst (a |=> False) r, psubst (a |=> True) r)
        psimplify (List.foldBack orify (subtract (atoms p) (atoms q)) p)
        
    // pg. 429
    // ------------------------------------------------------------------------- //
    // Relation-symbol interpolation for universal closed formulas.              //
    // ------------------------------------------------------------------------- //

    let urinterpolate p q =
        let fm = specialize (prenex (And (p, q)))
        let fvs = fv fm
        let consts, funcs = herbfuns fm
        let cntms = List.map (fun (c, _) -> Fn (c, [])) consts
        let tups = dp_refine_loop (simpcnf fm) cntms funcs fvs 0 [] [] []
        let fmis = List.map (fun tup -> subst (fpf fvs tup) fm) tups
        let ps, qs = List.unzip (List.map (fun (And (p, q)) -> p, q) fmis)
        pinterpolate (list_conj (setify ps)) (list_conj (setify qs))
    
    // pg. 432
    // ------------------------------------------------------------------------- //
    // Pick the topmost terms starting with one of the given function symbols.   //
    // ------------------------------------------------------------------------- //

    let rec toptermt fns tm =
        match tm with
        | Var x -> []
        | Fn (f, args) ->
            if mem (f, List.length args) fns then [tm]
            else List.foldBack (union << toptermt fns) args []

    let topterms fns =
        atom_union (fun (R (p, args)) -> List.foldBack (union << toptermt fns) args [])
        
    // pg. 433
    // ------------------------------------------------------------------------- //
    // Interpolation for arbitrary universal formulas.                           //
    // ------------------------------------------------------------------------- //

    let uinterpolate p q =
        let rec fp = functions p
        and fq = functions q
        let rec simpinter tms n c =
            match tms with
            | [] -> c
            | (Fn (f, args) as tm) :: otms ->
                let v = "v_" + (string n)
                let c' = replace (tm |=> Var v) c
                let c'' =
                    if mem (f, List.length args) fp
                    then Exists (v, c')
                    else Forall (v, c')
                simpinter otms (n + 1) c''
        let c = urinterpolate p q
        let tts = topterms (union (subtract fp fq) (subtract fq fp)) c
        let tms = sort (decreasing termsize) tts
        simpinter tms 1 c
    
    // pg. 434
    // ------------------------------------------------------------------------- //
    // Now lift to arbitrary formulas with no common free variables.             //
    // ------------------------------------------------------------------------- //

    let cinterpolate p q =
        let fm = nnf (And (p, q))
        let rec efm = List.foldBack mk_exists (fv fm) fm
        and fns = List.map fst (functions fm)
        let And (p', q'), _ = skolem efm fns
        uinterpolate p' q'
        
    // pg. 434
    // ------------------------------------------------------------------------- //
    // Now to completely arbitrary formulas.                                     //
    // ------------------------------------------------------------------------- //

    let interpolate p q =
        let rec vs = List.map (fun v -> Var v) (intersect (fv p) (fv q))
        and fns = functions (And (p, q))
        let n = List.foldBack (max_varindex "c_" << fst) fns (Int 0) + (Int 1)
        // OPTIMIZE : Implement a special version of List.init which uses 'num'
        // instead of 'int'. Then, use it to replace this call to List.map.
        let cs = List.map (fun i -> Fn ("c_" + i.ToString(), [])) [n .. (n + Int (List.length vs - 1))]
        let rec fn_vc = fpf vs cs
        and fn_cv = fpf cs vs
        let rec p' = replace fn_vc p
        and q' = replace fn_vc q
        replace fn_cv (cinterpolate p' q')
    
    // pg. 435
    // ------------------------------------------------------------------------- //
    // Lift to logic with equality.                                              //
    // ------------------------------------------------------------------------- //

    let einterpolate p q =
        let rec p'' =
            let p' = equalitize p
            if p' = p then p
            else And (fst (dest_imp p'), p)
        and q'' =
            let q' = equalitize q
            if q' = q then q
            else And (fst (dest_imp q'), q)
        interpolate p'' q''
