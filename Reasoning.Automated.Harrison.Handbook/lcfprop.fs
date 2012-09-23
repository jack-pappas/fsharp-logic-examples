//  Copyright (c) 2003-2007, John Harrison
//  All rights reserved.
//  
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the following disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the following disclaimer in the
//  IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
//  By downloading, copying, installing or using the software you agree
//  to this license.  If you do not agree to this license, do not
//  download, install, copy or use the software.
//  
//  Copyright (c) 2003-2007, John Harrison
//  All rights reserved.
//  
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the following disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the following disclaimer in the
//  documentation and/or other materials provided with the distribution.
//  
//  * The name of John Harrison may not be used to endorse or promote
//  products derived from this software without specific prior written
//  permission.
//  
//  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
//  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
//  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
//  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
//  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
//  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
//  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
//  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
//  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
//  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
//  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
//  SUCH DAMAGE.
// 
//  ===================================================================
// 
//  Converted to F# 2.0
// 
//  Copyright (c) 2012, Jack Pappas, Eric Taucher
//  All rights reserved.
// 
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the previous disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the previous disclaimer in the
//  documentation and/or other materials provided with the distribution.
//  
//  * The name of Eric Taucher may not be used to endorse or promote
//  products derived from this software without specific prior written
//  permission.
// 
//  ===================================================================

// ========================================================================= //
// Propositional reasoning by derived rules atop the LCF core.               //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module lcfprop =
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

    // pg. 478
    // ------------------------------------------------------------------------- //
    // |- p ==> p                                                                //
    // ------------------------------------------------------------------------- //

    let imp_refl p =
        modusponens (modusponens (axiom_distribimp p (Imp (p, p)) p)
                               (axiom_addimp p (Imp (p, p))))
                  (axiom_addimp p p)

    // Note: interactive items from book on pg. 479 missing in code
                  
    // pg. 479
    // ------------------------------------------------------------------------- //
    //                 |- p ==> p ==> q                                          //
    //               -------------------- imp_unduplicate                        //
    //                 |- p ==> q                                                //
    // ------------------------------------------------------------------------- //

    let imp_unduplicate th =
        let p, pq = dest_imp (concl th)
        let q = consequent pq
        modusponens (modusponens (axiom_distribimp p p q) th) (imp_refl p)
        
    // pg. 480
    // ------------------------------------------------------------------------- //
    // Some handy syntax operations.                                             //
    // ------------------------------------------------------------------------- //

    let negatef fm =
        match fm with
        | Imp (p, False) -> p
        | p -> Imp (p, False)

    let negativef fm =
        match fm with
        | Imp (p, False) -> true
        | _ -> false
        
    // pg. 480
    // ------------------------------------------------------------------------- //
    //                           |- q                                            //
    //         ------------------------------------------------ add_assum (p)    //
    //                         |- p ==> q                                        //
    // ------------------------------------------------------------------------- //

    let add_assum p th =
        modusponens (axiom_addimp (concl th) p) th
        
    // pg. 480
    // ------------------------------------------------------------------------- //
    //                   |- q ==> r                                              //
    //         --------------------------------------- imp_add_assum p           //
    //           |- (p ==> q) ==> (p ==> r)                                      //
    // ------------------------------------------------------------------------- //

    let imp_add_assum p th =
        let q, r = dest_imp (concl th)
        modusponens (axiom_distribimp p q r) (add_assum p th)
        
    // pg. 480
    // ------------------------------------------------------------------------- //
    //            |- p ==> q              |- q ==> r                             //
    //         ----------------------------------------- imp_trans               //
    //                 |- p ==> r                                                //
    // ------------------------------------------------------------------------- //

    let imp_trans th1 th2 =
        let p = antecedent (concl th1)
        modusponens (imp_add_assum p th2) th1
        
    // pg. 481
    // ------------------------------------------------------------------------- //
    //                 |- p ==> r                                                //
    //         -------------------------- imp_insert q                           //
    //              |- p ==> q ==> r                                             //
    // ------------------------------------------------------------------------- //

    let imp_insert q th =
        let p, r = dest_imp (concl th)
        imp_trans th (axiom_addimp r q)
        
    // pg. 481
    // ------------------------------------------------------------------------- //
    //                 |- p ==> q ==> r                                          //
    //              ---------------------- imp_swap                              //
    //                 |- q ==> p ==> r                                          //
    // ------------------------------------------------------------------------- //

    let imp_swap th =
        let p,qr = dest_imp(concl th)
        let q,r = dest_imp qr
        imp_trans (axiom_addimp q p)
            (modusponens (axiom_distribimp p q r) th)
            
    // pg. 481
    // ------------------------------------------------------------------------- //
    // |- (q ==> r) ==> (p ==> q) ==> (p ==> r)                                  //
    // ------------------------------------------------------------------------- //

    let imp_trans_th p q r =
        imp_trans (axiom_addimp (Imp (q, r)) p)
                    (axiom_distribimp p q r)
                    
    // pg. 481
    // ------------------------------------------------------------------------- //
    //                 |- p ==> q                                                //
    //         ------------------------------- imp_add_concl r                   //
    //          |- (q ==> r) ==> (p ==> r)                                       //
    // ------------------------------------------------------------------------- //

    let imp_add_concl r th =
        let p, q = dest_imp (concl th)
        modusponens (imp_swap (imp_trans_th p q r)) th
        
    // pg. 481
    // ------------------------------------------------------------------------- //
    // |- (p ==> q ==> r) ==> (q ==> p ==> r)                                    //
    // ------------------------------------------------------------------------- //

    let imp_swap_th p q r =
        imp_trans
            (axiom_distribimp p q r)
            (imp_add_concl (Imp (p, r)) (axiom_addimp q p))
            
    // pg. 481
    // ------------------------------------------------------------------------- //
    //  |- (p ==> q ==> r) ==> (s ==> t ==> u)                                   //
    // -----------------------------------------                                 //
    //  |- (q ==> p ==> r) ==> (t ==> s ==> u)                                   //
    // ------------------------------------------------------------------------- //

    let imp_swap2 th =
        match concl th with
        | Imp (Imp (p, Imp (q, r)), Imp (s, Imp (t, u))) ->
            imp_trans (imp_swap_th q p r) (imp_trans th (imp_swap_th s t u))
        | _ -> failwith "imp_swap2"
        
    // pg. 481
    // ------------------------------------------------------------------------- //
    // If |- p ==> q ==> r and |- p ==> q then |- p ==> r.                       //
    // ------------------------------------------------------------------------- //

    let right_mp ith th =
        imp_unduplicate (imp_trans th (imp_swap ith))
        
    // pg. 482
    // ------------------------------------------------------------------------- //
    //                 |- p <=> q                                                //
    //                ------------ iff_imp1                                      //
    //                 |- p ==> q                                                //
    // ------------------------------------------------------------------------- //

    let iff_imp1 th =
        let p, q = dest_iff (concl th)
        modusponens (axiom_iffimp1 p q) th
        
    // pg. 482
    // ------------------------------------------------------------------------- //
    //                 |- p <=> q                                                //
    //                ------------ iff_imp2                                      //
    //                 |- q ==> p                                                //
    // ------------------------------------------------------------------------- //

    let iff_imp2 th =
        let p, q = dest_iff (concl th)
        modusponens (axiom_iffimp2 p q) th
        
    // pg. 482
    // ------------------------------------------------------------------------- //
    //         |- p ==> q      |- q ==> p                                        //
    //        ---------------------------- imp_antisym                           //
    //              |- p <=> q                                                   //
    // ------------------------------------------------------------------------- //

    let imp_antisym th1 th2 =
        let p, q = dest_imp (concl th1)
        modusponens (modusponens (axiom_impiff p q) th1) th2
        
    // pg. 482
    // ------------------------------------------------------------------------- //
    //         |- p ==> (q ==> false) ==> false                                  //
    //       ----------------------------------- right_doubleneg                 //
    //               |- p ==> q                                                  //
    // ------------------------------------------------------------------------- //

    let right_doubleneg th =
        match concl th with
        | Imp (_, Imp (Imp (p, False), False)) ->
            imp_trans th (axiom_doubleneg p)
        | _ -> failwith "right_doubleneg"
        
    // pg. 482
    // ------------------------------------------------------------------------- //
    //                                                                           //
    //         ------------------------------------------- ex_falso (p)          //
    //                 |- false ==> p                                            //
    // ------------------------------------------------------------------------- //

    let ex_falso p =
        right_doubleneg (axiom_addimp False (Imp (p, False)))
        
    // pg. 482
    // ------------------------------------------------------------------------- //
    //  |- p ==> q ==> r        |- r ==> s                                       //
    // ------------------------------------ imp_trans2                           //
    //      |- p ==> q ==> s                                                     //
    // ------------------------------------------------------------------------- //

    let imp_trans2 th1 th2 =
        let p, q, r =
            match concl th1 with Imp (p, Imp (q, r)) -> p, q, r
        let r', s =
            match concl th2 with Imp (r', s) -> r', s
        let th = imp_add_assum p (modusponens (imp_trans_th q r s) th2)
        modusponens th th1
        
    // pg. 482
    // ------------------------------------------------------------------------- //
    //         |- p ==> q1   ...   |- p ==> qn   |- q1 ==> ... ==> qn ==> r      //
    //        --------------------------------------------------------------     //
    //                             |- p ==> r                                    //
    // ------------------------------------------------------------------------- //

    let imp_trans_chain ths th =
        List.foldBack (fun a b -> imp_unduplicate (imp_trans a (imp_swap b)))
             (List.rev (List.tail ths)) (imp_trans (List.head ths) th)
             
    // pg. 483
    // ------------------------------------------------------------------------- //
    // |- (q ==> false) ==> p ==> (p ==> q) ==> false                            //
    // ------------------------------------------------------------------------- //

    let imp_truefalse p q =
        imp_trans (imp_trans_th p q False) (imp_swap_th (Imp (p, q)) p False)
        
    // pg. 483
    // ------------------------------------------------------------------------- //
    //  |- (p' ==> p) ==> (q ==> q') ==> (p ==> q) ==> (p' ==> q')               //
    // ------------------------------------------------------------------------- //

    let imp_mono_th p p' q q' =
        let rec th1 = imp_trans_th (Imp (p, q)) (Imp (p', q)) (Imp (p', q'))
        and th2 = imp_trans_th p' q q'
        and th3 = imp_swap (imp_trans_th p' p q)
        imp_trans th3 (imp_swap (imp_trans th2 th1))
        
    // pg. 483
    // ------------------------------------------------------------------------- //
    // |- true                                                                   //
    // ------------------------------------------------------------------------- //

    let truth : formula<fol> =
        modusponens (iff_imp2 axiom_true) (imp_refl False)
        
    // pg. 483
    // ------------------------------------------------------------------------- //
    //         |- p ==> q                                                        //
    //      ----------------- contrapos                                          //
    //         |- ~q ==> ~p                                                      //
    // ------------------------------------------------------------------------- //

    let contrapos th =
        let p, q = dest_imp (concl th)
        imp_trans (imp_trans (iff_imp1 (axiom_not q)) (imp_add_concl False th))
            (iff_imp2 (axiom_not p))
            
    // pg. 483
    // ------------------------------------------------------------------------- //
    // |- p /\ q ==> p                                                           //
    // ------------------------------------------------------------------------- //

    let and_left p q =
        let th1 = imp_add_assum p (axiom_addimp False q)
        let th2 = right_doubleneg (imp_add_concl False th1)
        imp_trans (iff_imp1 (axiom_and p q)) th2
        
    // pg. 483
    // ------------------------------------------------------------------------- //
    // |- p /\ q ==> q                                                           //
    // ------------------------------------------------------------------------- //

    let and_right p q =
        let th1 = axiom_addimp (Imp (q, False)) p
        let th2 = right_doubleneg (imp_add_concl False th1)
        imp_trans (iff_imp1 (axiom_and p q)) th2
        
    // pg. 484
    // ------------------------------------------------------------------------- //
    // |- p1 /\ ... /\ pn ==> pi for each 1 <= i <= n (input term right assoc)   //
    // ------------------------------------------------------------------------- //

    let rec conjths fm =
        try
            let p, q = dest_and fm
            (and_left p q) :: List.map (imp_trans (and_right p q)) (conjths q)
        with Failure _ ->
            [imp_refl fm]
            
    // pg. 484
    // ------------------------------------------------------------------------- //
    // |- p ==> q ==> p /\ q                                                     //
    // ------------------------------------------------------------------------- //

    let and_pair p q =
        let rec th1 = iff_imp2 (axiom_and p q)
        and th2 = imp_swap_th (Imp (p, Imp (q, False))) q False
        let th3 = imp_add_assum p (imp_trans2 th2 th1)
        modusponens th3 (imp_swap (imp_refl (Imp (p, Imp (q, False)))))
        
    // pg. 484
    // ------------------------------------------------------------------------- //
    // If |- p /\ q ==> r then |- p ==> q ==> r                                  //
    // ------------------------------------------------------------------------- //

    let shunt th =
        let p, q = dest_and (antecedent (concl th))
        modusponens (List.foldBack imp_add_assum [p; q] th) (and_pair p q)
        
    // pg. 484
    // ------------------------------------------------------------------------- //
    // If |- p ==> q ==> r then |- p /\ q ==> r                                  //
    // ------------------------------------------------------------------------- //

    let unshunt th =
        let p, qr = dest_imp (concl th)
        let q, r = dest_imp qr
        imp_trans_chain [and_left p q; and_right p q] th
        
    // pg. 485
    // ------------------------------------------------------------------------- //
    // Produce |- (p <=> q) <=> (p ==> q) /\ (q ==> p)                           //
    // ------------------------------------------------------------------------- //

    // Not in book.
    // let iff_def p q =
    //     let th1 = and_pair (Imp (p, q)) (Imp (q, p))
    //     let th2 = imp_trans_chain [axiom_iffimp1 p q; axiom_iffimp2 p q] th1
    //     imp_antisym th2 (unshunt (axiom_impiff p q))

    let iff_def p q =
        let rec th = and_pair (Imp (p, q)) (Imp (q, p))
        and thl = [axiom_iffimp1 p q; axiom_iffimp2 p q]
        imp_antisym (imp_trans_chain thl th) (unshunt (axiom_impiff p q))
        
    // pg. 485
    // ------------------------------------------------------------------------- //
    // Produce "expansion" theorem for defined connectives.                      //
    // ------------------------------------------------------------------------- //

    let expand_connective fm =
        match fm with
        | True ->
            axiom_true
        | Not p ->
            axiom_not p
        | And (p, q) ->
            axiom_and p q
        | Or (p, q) ->
            axiom_or p q
        | Iff (p, q) ->
            iff_def p q
        | Exists (x, p) ->
            axiom_exists x p
        | _ ->
            failwith "expand_connective"

    let eliminate_connective fm =
        if negativef fm then
            imp_add_concl False (iff_imp2 (expand_connective (negatef fm)))
        else
            iff_imp1 (expand_connective fm)
            
    // pg. 486
    // ------------------------------------------------------------------------- //
    //                                                                           //
    //   ------------------------------------------------- imp_false_conseqs     //
    //      [|- ((p ==> q) ==> false) ==> (q ==> false);                         //
    //       |- ((p ==> q) ==> false) ==> p]                                     //
    // ------------------------------------------------------------------------- //

    let imp_false_conseqs p q = [
        right_doubleneg (imp_add_concl False (imp_add_assum p (ex_falso q)));
        imp_add_concl False (imp_insert p (imp_refl q)); ]
        
    // pg. 486
    // ------------------------------------------------------------------------- //
    //         |- p ==> (q ==> false) ==> r                                      //
    //        ------------------------------------ imp_false_rule                //
    //             |- ((p ==> q) ==> false) ==> r                                //
    // ------------------------------------------------------------------------- //

    let imp_false_rule th =
        let p, r = dest_imp (concl th)
        imp_trans_chain (imp_false_conseqs p (funpow 2 antecedent r)) th
        
    // pg. 486
    // ------------------------------------------------------------------------- //
    //         |- (p ==> false) ==> r          |- q ==> r                        //
    //       ---------------------------------------------- imp_true_rule        //
    //                      |- (p ==> q) ==> r                                   //
    // ------------------------------------------------------------------------- //

    let imp_true_rule th1 th2 =
        let rec p = funpow 2 antecedent (concl th1)
        and q = antecedent (concl th2)
        and th3 = right_doubleneg (imp_add_concl False th1)
        and th4 = imp_add_concl False th2
        let th5 = imp_swap (imp_truefalse p q)
        let rec th6 = imp_add_concl False (imp_trans_chain [th3; th4] th5)
        and th7 = imp_swap (imp_refl (Imp (Imp (p, q), False)))
        right_doubleneg (imp_trans th7 th6)
        
    // pg. 486
    // ------------------------------------------------------------------------- //
    //                                 *                                         //
    //                 -------------------------------------- imp_contr          //
    //                        |- p ==> -p ==> q                                  //
    // ------------------------------------------------------------------------- //

    let imp_contr p q =
        if negativef p then imp_add_assum (negatef p) (ex_falso q)
        else imp_swap (imp_add_assum p (ex_falso q))
        
    // pg. 487
    // ------------------------------------------------------------------------- //
    //                                                                           //
    // --------------------------------------------- imp_front (this antecedent) //
    //  |- (p0 ==> p1 ==> ... ==> pn ==> q)                                      //
    //     ==> pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                              //
    // ------------------------------------------------------------------------- //

    let rec imp_front_th n fm =
        if n = 0 then imp_refl fm
        else
            let p, qr = dest_imp fm
            let th1 = imp_add_assum p (imp_front_th (n - 1) qr)
            let q', r' = dest_imp (funpow 2 consequent (concl th1))
            imp_trans th1 (imp_swap_th p q' r')
            
    // pg. 487
    // ------------------------------------------------------------------------- //
    //           |- p0 ==> p1 ==> ... ==> pn ==> q                               //
    //         ------------------------------------------ imp_front n            //
    //           |- pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                         //
    // ------------------------------------------------------------------------- //

    let imp_front n th =
        modusponens (imp_front_th n (concl th)) th
        
    // pg. 487
    // ------------------------------------------------------------------------- //
    // Propositional tableaux procedure.                                         //
    // ------------------------------------------------------------------------- //

    let rec lcfptab fms lits =
        match fms with
        | False :: fl ->
            ex_falso (List.foldBack mk_imp (fl @ lits) False)

        | (Imp (p, q) as fm) :: fl when p = q ->
            add_assum fm (lcfptab fl lits)

        | Imp (Imp (p, q), False) :: fl ->
            imp_false_rule (lcfptab (p :: Imp (q, False) :: fl) lits)

        | Imp (p, q) :: fl when q <> False ->
            imp_true_rule (lcfptab (Imp (p, False) :: fl) lits)
                          (lcfptab (q :: fl) lits)

        | (Atom (_) as p) :: fl
        | (Forall(_,_) as p) :: fl
        | (Imp ((Atom _ | Forall (_,_)), False) as p) :: fl ->
            if mem (negatef p) lits then
                let l1, l2 = chop_list (index (negatef p) lits) lits
                let th = imp_contr p (List.foldBack mk_imp (List.tail l2) False)
                List.foldBack imp_insert (fl @ l1) th
            else
                imp_front (List.length fl) (lcfptab fl (p :: lits))

        | fm :: fl ->
            let th = eliminate_connective fm
            imp_trans th (lcfptab (consequent (concl th) :: fl) lits)

        | _ ->
            failwith "lcfptab: no contradiction"
            
    // pg. 488
    // ------------------------------------------------------------------------- //
    // In particular, this gives a tautology prover.                             //
    // ------------------------------------------------------------------------- //

    let lcftaut p =
        modusponens (axiom_doubleneg p) (lcfptab [negatef p] [])
