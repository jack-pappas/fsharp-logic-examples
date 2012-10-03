// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Jack Pappas, Eric Taucher                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// Grobner basis algorithm.                                                  //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module grobner =
    open LanguagePrimitives
    open FSharpx.Compatibility.OCaml
    open Num

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

    // pg. 384
    // ------------------------------------------------------------------------- //
    // Operations on monomials.                                                  //
    // ------------------------------------------------------------------------- //

    let mmul (c1, m1) (c2, m2) =
        (c1 * c2, List.map2 (+) m1 m2)

    let mdiv =
        let index_sub n1 n2 =
            if n1 < n2 then
                failwith "mdiv"
            else n1 - n2
        fun (c1, m1) (c2, m2) ->
            (c1 / c2, List.map2 index_sub m1 m2)

    let mlcm (c1, m1) (c2, m2) =
        (Int 1, List.map2 max m1 m2)
        
    // pg. 384
    // ------------------------------------------------------------------------- //
    // Monomial ordering.                                                        //
    // ------------------------------------------------------------------------- //

    let morder_lt m1 m2 =
        let rec n1 = List.foldBack (+) m1 0
        and n2 = List.foldBack (+) m2 0
        n1 < n2 || n1 = n2 && lexord (>) m1 m2
        
    // pg. 385
    // ------------------------------------------------------------------------- //
    // Arithmetic on canonical multivariate polynomials.                         //
    // ------------------------------------------------------------------------- //

    let inline mpoly_mmul cm pol = List.map (mmul cm) pol

    let mpoly_neg = List.map (fun (c, m) -> (-c, m))

    let mpoly_const vars (c : num) =
        if c = GenericZero then []
        else [c, List.map (fun _ -> 0) vars]

    let mpoly_var vars x =
        [Int 1, List.map (fun y -> if y = x then 1 else 0) vars]

    let rec mpoly_add l1 l2 =
      match l1, l2 with
      | [], x
      | x, [] -> x
        // NOTE : c1, c2 have type 'num'
      | ((c1, m1) :: o1, (c2, m2) :: o2) ->
            if m1 = m2 then
                let rec c = c1 + c2
                and rest = mpoly_add o1 o2
                // if c =/ Int 0
                if c = Int 0 then rest
                else (c, m1) :: rest
            elif morder_lt m2 m1 then
                (c1, m1) :: (mpoly_add o1 l2)
            else
                (c2, m2) :: (mpoly_add l1 o2)

    let mpoly_sub l1 l2 =
        mpoly_add l1 (mpoly_neg l2)

    let rec mpoly_mul l1 l2 =
        match l1 with
        | [] -> []
        | h1 :: t1 ->
            mpoly_add (mpoly_mmul h1 l2) (mpoly_mul t1 l2)

    let mpoly_pow vars l n =
        funpow n (mpoly_mul l) (mpoly_const vars (Int 1))

    let mpoly_inv p =
        match p with
        | [(c, m)] when List.forall (fun i -> i = 0) m ->
            // Int 1 // c
            [(Int 1 / c), m]
        | _ -> failwith "mpoly_inv: non-constant polynomial"

    let inline mpoly_div p q =
        mpoly_mul p (mpoly_inv q)
        
    // pg. 386
    // ------------------------------------------------------------------------- //
    // Convert formula into canonical form.                                      //
    // ------------------------------------------------------------------------- //

    let rec mpolynate vars tm =
        match tm with
        | Var x ->
            mpoly_var vars x
        | Fn ("-", [t]) ->
            mpoly_neg (mpolynate vars t)
        | Fn ("+", [s; t]) ->
            mpoly_add (mpolynate vars s) (mpolynate vars t)
        | Fn ("-", [s; t]) ->
            mpoly_sub (mpolynate vars s) (mpolynate vars t)
        | Fn ("*", [s; t]) ->
            mpoly_mul (mpolynate vars s) (mpolynate vars t)
        | Fn ("/", [s; t]) ->
            mpoly_div (mpolynate vars s) (mpolynate vars t)
        | Fn ("^", [t; Fn (n, [])]) ->
            mpoly_pow vars (mpolynate vars t) (System.Int32.Parse n)
        | _ ->
            mpoly_const vars (dest_numeral tm)

    let mpolyatom vars fm =
        match fm with
        | Atom (R ("=", [s; t])) ->
            mpolynate vars (Fn ("-", [s; t]))
        | _ ->
            failwith "mpolyatom: not an equation"

    // pg. 404
    // ------------------------------------------------------------------------- //
    // Reduce monomial cm by polynomial pol, returning replacement for cm.       //
    // ------------------------------------------------------------------------- //

    let reduce1 cm pol =
        match pol with
        | [] -> failwith "reduce1"
        | hm :: cms ->
            let c, m = mdiv cm hm
            mpoly_mmul (-c, m) cms
            
    // pg. 404
    // ------------------------------------------------------------------------- //
    // Try this for all polynomials in a basis.                                  //
    // ------------------------------------------------------------------------- //

    let inline reduceb cm pols =
        tryfind (reduce1 cm) pols
    
    // pg. 404
    // ------------------------------------------------------------------------- //
    // Reduction of a polynomial (always picking largest monomial possible).     //
    // ------------------------------------------------------------------------- //

    let rec reduce pols pol =
        match pol with
        | [] -> []
        | cm :: ptl ->
            try reduce pols (mpoly_add (reduceb cm pols) ptl)
            with Failure _ ->
                cm :: (reduce pols ptl)
                
    // pg. 408
    // ------------------------------------------------------------------------- //
    // Compute S-polynomial of two polynomials.                                  //
    // ------------------------------------------------------------------------- //

    let spoly pol1 pol2 =
        match pol1, pol2 with
        | [], _
        | _, [] -> []
        | m1 :: ptl1, m2 :: ptl2 ->
            let m = mlcm m1 m2
            mpoly_sub (mpoly_mmul (mdiv m m1) ptl1)
                      (mpoly_mmul (mdiv m m2) ptl2)
                      
    // pg. 411
    // ------------------------------------------------------------------------- //
    // Grobner basis algorithm.                                                  //
    // ------------------------------------------------------------------------- //

    let rec grobner basis pairs =
        printfn "%i basis elements and %i pairs" (List.length basis) (List.length pairs)
        match pairs with
        | [] -> basis
        | (p1, p2) :: opairs ->
            match reduce basis (spoly p1 p2) with
            | [] ->
                grobner basis opairs
            | sp when List.forall (snd >> List.forall ((=) 0)) sp ->
                [sp]
            | sp ->
                let newcps = List.map (fun p -> p, sp) basis
                grobner (sp :: basis) (opairs @ newcps)
            
    // pg. 412
    // ------------------------------------------------------------------------- //
    // Overall function.                                                         //
    // ------------------------------------------------------------------------- //

    let inline groebner basis =
        grobner basis (distinctpairs basis)
        
    // pg. 412
    // ------------------------------------------------------------------------- //
    // Use the Rabinowitsch trick to eliminate inequations.                      //
    // That is, replace p =/= 0 by exists v. 1 - v * p = 0                       //
    // ------------------------------------------------------------------------- //

    let rabinowitsch vars v p =
        mpoly_mul (mpoly_var vars v) p
        |> mpoly_sub (mpoly_const vars (Int 1))

    // pg. 413
    // ------------------------------------------------------------------------- //
    // Universal complex number decision procedure based on Grobner bases.       //
    // ------------------------------------------------------------------------- //

    let grobner_trivial fms =
        let vars0 = List.foldBack (union << fv) fms []
        let eqs, neqs = List.partition positive fms
        // OPTIMIZE : Change this call to List.map to use List.init instead.
        let rvs = List.map (fun n -> variant ("_" + string n) vars0)
                    [1 .. List.length neqs]
        let vars = vars0 @ rvs
        let rec poleqs = List.map (mpolyatom vars) eqs
        and polneqs = List.map (mpolyatom vars << negate) neqs
        let pols = poleqs @ List.map2 (rabinowitsch vars) rvs polneqs
        reduce (groebner pols) (mpoly_const vars (Int 1))
        |> List.isEmpty

    let grobner_decide fm =
        simplify004 fm
        |> nnf
        |> prenex
        |> specialize
        |> Not
        |> nnf
        |> simpdnf
        |> List.forall grobner_trivial

    // Not in book
    // ------------------------------------------------------------------------- //
    // For looking at things it's nice to map back to normal term.               //
    // ------------------------------------------------------------------------- //

    let term_of_varpow vars (x,k) =
        if k = 1 then Var x
        else Fn ("^", [Var x; mk_numeral (Int k)])

    let term_of_varpows vars lis =
        List.zip vars lis
        |> List.filter (fun (_, b) -> b <> 0)
        |> List.map (term_of_varpow vars)
        |> end_itlist (fun s t -> Fn ("*", [s;t]))

    let term_of_monomial vars (c,m) =
        if List.forall (fun x -> x = 0) m then
            mk_numeral c
        elif c =/ Int 1 then
            term_of_varpows vars m
        else
            Fn ("*", [mk_numeral c; term_of_varpows vars m])

    let term_of_poly vars pol =
        pol
        |> List.map (term_of_monomial vars)
        |> end_itlist (fun s t -> Fn("+",[s;t]))

    let grobner_basis vars pols =
        pols
        |> List.map (mpolyatom vars)
        |> groebner
        |> List.map (term_of_poly vars)

    