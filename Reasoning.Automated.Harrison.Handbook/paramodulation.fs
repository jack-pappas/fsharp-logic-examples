// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.paramodulation

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

// ========================================================================= //
// Paramodulation.                                                           //
// ========================================================================= //

// pg. 301
// ------------------------------------------------------------------------- //
// Find paramodulations with l = r inside a literal fm.                      //
// ------------------------------------------------------------------------- //

    let rec overlapl (l, r) fm rfn =
        match fm with
        | Atom (R (f, args)) ->
            listcases (overlaps (l, r)) (fun i a -> rfn i (Atom (R (f, a)))) args []
        | Not p ->
            overlapl (l, r) p (fun i p -> rfn i (Not p))
        | _ -> failwith "overlapl: not a literal"
  
// pg. 301
// ------------------------------------------------------------------------- //
// Now find paramodulations within a clause.                                 //
// ------------------------------------------------------------------------- //

    let overlapc (l, r) cl rfn acc =
        listcases (overlapl (l, r)) rfn cl acc

// pg. 301
// ------------------------------------------------------------------------- //
// Overall paramodulation of ocl by equations in pcl.                        //
// ------------------------------------------------------------------------- //

    let paramodulate pcl ocl =
        List.foldBack (fun eq ->
            let pcl' = subtract pcl [eq]
            let l, r = dest_eq eq
            let rfn i ocl' = image (subst i) (pcl' @ ocl')
            overlapc (l, r) ocl rfn >>|> overlapc (r, l) ocl rfn)
            (List.filter is_eq pcl) []

    let para_clauses cls1 cls2 =
        let cls1' = rename "x" cls1
        let cls2' = rename "y" cls2
        paramodulate cls1' cls2' @ paramodulate cls2' cls1'
  
// pg. 302
// ------------------------------------------------------------------------- //
// Incorporation into resolution loop.                                       //
// ------------------------------------------------------------------------- //

    let rec paraloop (used, unused) =
        match unused with
        | cls :: ros ->
            printfn "%i used; %i unused." (List.length used) (List.length unused)
            let used' = insert cls used
            let news =
                List.foldBack (@) (mapfilter (resolve_clauses cls) used')
                    (List.foldBack (@) (mapfilter (para_clauses cls) used') [])
            if mem [] news then true 
            else
                paraloop (used', List.foldBack (incorporate cls) news ros)

    let pure_paramodulation fm =
      paraloop ([], [mk_eq (Var "x") (Var "x")] :: simpcnf (specialize (pnf fm)))

    let paramodulation fm =
      let fm1 = askolemize (Not (generalize fm))
      List.map (pure_paramodulation >>|> list_conj) (simpdnf fm1)
