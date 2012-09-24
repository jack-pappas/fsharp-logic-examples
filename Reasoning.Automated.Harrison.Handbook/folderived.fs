// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Jack Pappas, Eric Taucher                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// First-order derived rules in the LCF setup.                               //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module folderived =
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
    open interpolation
    open combining
    open lcf
    open lcfprop

    // pg. 489
    // ------------------------------------------------------------------------- //
    //                         ******                                            //
    //         ------------------------------------------ eq_sym                 //
    //                      |- s = t ==> t = s                                   //
    // ------------------------------------------------------------------------- //

    let eq_sym s t =
        let rth = axiom_eqrefl s
        funpow 2 (fun th -> modusponens (imp_swap th) rth)
               (axiom_predcong "=" [s; s] [t; s])
               
    // pg. 489
    // ------------------------------------------------------------------------- //
    // |- s = t ==> t = u ==> s = u.                                             //
    // ------------------------------------------------------------------------- //

    let eq_trans s t u =
        let th1 = axiom_predcong "=" [t; u] [s; u]
        let th2 = modusponens (imp_swap th1) (axiom_eqrefl u)
        imp_trans (eq_sym s t) th2
        
    // pg. 490
    // ------------------------------------------------------------------------- //
    //         ---------------------------- icongruence                          //
    //          |- s = t ==> tm[s] = tm[t]                                       //
    // ------------------------------------------------------------------------- //

    let rec icongruence s t stm ttm =
        if stm = ttm then
            add_assum (mk_eq s t) (axiom_eqrefl stm)
        elif stm = s && ttm = t then
            imp_refl (mk_eq s t)
        else
            match stm, ttm with
            | Fn (fs, sa), Fn (ft, ta)
                when fs = ft && List.length sa = List.length ta ->
                let ths = List.map2 (icongruence s t) sa ta
                let ts = List.map (consequent >>|> concl) ths
                imp_trans_chain ths (axiom_funcong fs (List.map lhs ts) (List.map rhs ts))
            | _ -> failwith "icongruence: not congruent"
    
    // pg. 490
    // ------------------------------------------------------------------------- //
    // |- (forall x. p ==> q(x)) ==> p ==> (forall x. q(x))                      //
    // ------------------------------------------------------------------------- //

    let gen_right_th x p q =
        imp_swap (imp_trans (axiom_impall x p) (imp_swap (axiom_allimp x p q)))
        
    // pg. 490
    // ------------------------------------------------------------------------- //
    //                       |- p ==> q                                          //
    //         ------------------------------------- genimp "x"                  //
    //           |- (forall x. p) ==> (forall x. q)                              //
    // ------------------------------------------------------------------------- //

    let genimp x th =
        let p, q = dest_imp (concl th)
        modusponens (axiom_allimp x p q) (gen x th)
        
    // pg. 490
    // ------------------------------------------------------------------------- //
    // If |- p ==> q[x] then |- p ==> forall x. q[x]                             //
    // ------------------------------------------------------------------------- //

    let gen_right x th =
        let p, q = dest_imp (concl th)
        modusponens (gen_right_th x p q) (gen x th)
        
    // pg. 491
    // ------------------------------------------------------------------------- //
    // |- (forall x. p(x) ==> q) ==> (exists x. p(x)) ==> q                      //
    // ------------------------------------------------------------------------- //

    let exists_left_th x p q =
        let rec p' = Imp (p, False)
        and q' = Imp (q, False)
        let th1 = genimp x (imp_swap (imp_trans_th p q False))
        let th2 = imp_trans th1 (gen_right_th x q' p')
        let th3 = imp_swap (imp_trans_th q' (Forall (x, p')) False)
        let th4 = imp_trans2 (imp_trans th2 th3) (axiom_doubleneg q)
        let th5 = imp_add_concl False (genimp x (iff_imp2 (axiom_not p)))
        let th6 = imp_trans (iff_imp1 (axiom_not (Forall (x, Not p)))) th5
        let th7 = imp_trans (iff_imp1 (axiom_exists x p)) th6
        imp_swap (imp_trans th7 (imp_swap th4))
        
    // pg. 491
    // ------------------------------------------------------------------------- //
    // If |- p(x) ==> q then |- (exists x. p(x)) ==> q                           //
    // ------------------------------------------------------------------------- //

    let exists_left x th =
        let p, q = dest_imp (concl th)
        modusponens (exists_left_th x p q) (gen x th)
        
    // pg. 491
    // ------------------------------------------------------------------------- //
    //    |- x = t ==> p ==> q    [x not in t and not free in q]                 //
    //  --------------------------------------------------------------- subspec  //
    //                 |- (forall x. p) ==> q                                    //
    // ------------------------------------------------------------------------- //

    let subspec th =
        match concl th with
        | Imp (Atom (R ("=", [Var x; t])) as e, Imp (p, q)) ->
            let th1 = imp_trans (genimp x (imp_swap th)) (exists_left_th x e q)
            modusponens (imp_swap th1) (axiom_existseq x t)
        | _ ->
            failwith "subspec: wrong sort of theorem"
            
    // pg. 492
    // ------------------------------------------------------------------------- //
    //    |- x = y ==> p[x] ==> q[y]  [x not in FV(q); y not in FV(p) or x == y] //
    //  --------------------------------------------------------- subalpha       //
    //                 |- (forall x. p) ==> (forall y. q)                        //
    // ------------------------------------------------------------------------- //

    let subalpha th =
        match concl th with
        | Imp (Atom (R ("=", [Var x; Var y])), Imp (p, q)) ->
            if x = y then
                genimp x (modusponens th (axiom_eqrefl (Var x)))
            else
                gen_right y (subspec th)
        | _ -> failwith "subalpha: wrong sort of theorem"
        
    // pg. 492
    // ------------------------------------------------------------------------- //
    //         ---------------------------------- isubst                         //
    //            |- s = t ==> p[s] ==> p[t]                                     //
    // ------------------------------------------------------------------------- //

    let rec isubst s t sfm tfm =
        if sfm = tfm then
            add_assum (mk_eq s t) (imp_refl tfm)
        else
            match sfm, tfm with
            | Atom (R (p, sa)), Atom (R (p', ta))
                when p = p' && List.length sa = List.length ta ->
                let ths = List.map2 (icongruence s t) sa ta
                let ls, rs = List.unzip (List.map (dest_eq >>|> consequent >>|> concl) ths)
                imp_trans_chain ths (axiom_predcong p ls rs)

            | Imp (sp, sq), Imp (tp, tq) ->
                let rec th1 = imp_trans (eq_sym s t) (isubst t s tp sp)
                and th2 = isubst s t sq tq
                imp_trans_chain [th1; th2] (imp_mono_th sp tp sq tq)

            | Forall (x, p), Forall (y, q) ->
                if x = y then
                    imp_trans (gen_right x (isubst s t p q)) (axiom_allimp x p q)
                else
                    let z = Var (variant x (unions [fv p; fv q; fvt s; fvt t]))
                    let rec th1 = isubst (Var x) z p (subst (x |=> z) p)
                    and th2 = isubst z (Var y) (subst (y |=> z) q) q
                    let rec th3 = subalpha th1
                    and th4 = subalpha th2
                    let th5 = isubst s t (consequent (concl th3)) (antecedent (concl th4))
                    imp_swap (imp_trans2 (imp_trans th3 (imp_swap th5)) th4)

            | _ ->
                let rec sth = iff_imp1 (expand_connective sfm)
                and tth = iff_imp2 (expand_connective tfm)
                let th1 = isubst s t (consequent (concl sth))
                                     (antecedent (concl tth))
                imp_swap (imp_trans sth (imp_swap (imp_trans2 th1 tth)))
                
    // pg. 493
    // ------------------------------------------------------------------------- //
    //                                                                           //
    // -------------------------------------------- alpha "z" <<forall x. p[x]>> //
    //   |- (forall x. p[x]) ==> (forall z. p'[z])                               //
    //                                                                           //
    // [Restriction that z is not free in the initial p[x].]                     //
    // ------------------------------------------------------------------------- //

    let alpha z fm =
        match fm with
        | Forall (x, p) ->
            let p' = subst (x |=> Var z) p
            subalpha (isubst (Var x) (Var z) p p')
        | _ ->
            failwith "alpha: not a universal formula"
            
    // pg. 494
    // ------------------------------------------------------------------------- //
    //                                                                           //
    // -------------------------------- ispec t <<forall x. p[x]>>               //
    //   |- (forall x. p[x]) ==> p'[t]                                           //
    // ------------------------------------------------------------------------- //

    let rec ispec t fm =
        match fm with
        | Forall (x, p) ->
            if mem x (fvt t) then
                let th = alpha (variant x (union (fvt t) (var p))) fm
                imp_trans th (ispec t (consequent (concl th)))
            else
                subspec(isubst (Var x) t p (subst (x |=> t) p))
        | _ ->
            failwith "ispec: non-universal formula"
            
    // pg. 494
    // ------------------------------------------------------------------------- //
    // Specialization rule.                                                      //
    // ------------------------------------------------------------------------- //

    let spec t th = modusponens (ispec t (concl th)) th
