(* ========================================================================= *)
(* Propositional reasoning by derived rules atop the LCF core.               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

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

    (* ------------------------------------------------------------------------- *)
    (* |- p ==> p                                                                *)
    (* ------------------------------------------------------------------------- *)

    let imp_refl p =
        modusponens (modusponens (axiom_distribimp p (Imp (p, p)) p)
                               (axiom_addimp p (Imp (p, p))))
                  (axiom_addimp p p)

    (* ------------------------------------------------------------------------- *)
    (*                 |- p ==> p ==> q                                          *)
    (*               -------------------- imp_unduplicate                        *)
    (*                 |- p ==> q                                                *)
    (* ------------------------------------------------------------------------- *)

    let imp_unduplicate th =
        let p, pq = dest_imp (concl th)
        let q = consequent pq
        modusponens (modusponens (axiom_distribimp p p q) th) (imp_refl p)

    (* ------------------------------------------------------------------------- *)
    (* Some handy syntax operations.                                             *)
    (* ------------------------------------------------------------------------- *)

    let negatef fm =
        match fm with
        | Imp (p, False) -> p
        | p -> Imp (p, False)

    let negativef fm =
        match fm with
        | Imp (p, False) -> true
        | _ -> false

    (* ------------------------------------------------------------------------- *)
    (*                           |- q                                            *)
    (*         ------------------------------------------------ add_assum (p)    *)
    (*                         |- p ==> q                                        *)
    (* ------------------------------------------------------------------------- *)

    let add_assum p th =
        modusponens (axiom_addimp (concl th) p) th

    (* ------------------------------------------------------------------------- *)
    (*                   |- q ==> r                                              *)
    (*         --------------------------------------- imp_add_assum p           *)
    (*           |- (p ==> q) ==> (p ==> r)                                      *)
    (* ------------------------------------------------------------------------- *)

    let imp_add_assum p th =
        let q, r = dest_imp (concl th)
        modusponens (axiom_distribimp p q r) (add_assum p th)

    (* ------------------------------------------------------------------------- *)
    (*            |- p ==> q              |- q ==> r                             *)
    (*         ----------------------------------------- imp_trans               *)
    (*                 |- p ==> r                                                *)
    (* ------------------------------------------------------------------------- *)

    let imp_trans th1 th2 =
        let p = antecedent (concl th1)
        modusponens (imp_add_assum p th2) th1

    (* ------------------------------------------------------------------------- *)
    (*                 |- p ==> r                                                *)
    (*         -------------------------- imp_insert q                           *)
    (*              |- p ==> q ==> r                                             *)
    (* ------------------------------------------------------------------------- *)

    let imp_insert q th =
        let p, r = dest_imp (concl th)
        imp_trans th (axiom_addimp r q)

    (* ------------------------------------------------------------------------- *)
    (*                 |- p ==> q ==> r                                          *)
    (*              ---------------------- imp_swap                              *)
    (*                 |- q ==> p ==> r                                          *)
    (* ------------------------------------------------------------------------- *)

    let imp_swap th =
        let p,qr = dest_imp(concl th)
        let q,r = dest_imp qr
        imp_trans (axiom_addimp q p)
            (modusponens (axiom_distribimp p q r) th)

    (* ------------------------------------------------------------------------- *)
    (* |- (q ==> r) ==> (p ==> q) ==> (p ==> r)                                  *)
    (* ------------------------------------------------------------------------- *)

    let imp_trans_th p q r =
        imp_trans (axiom_addimp (Imp (q, r)) p)
                    (axiom_distribimp p q r)

    (* ------------------------------------------------------------------------- *)
    (*                 |- p ==> q                                                *)
    (*         ------------------------------- imp_add_concl r                   *)
    (*          |- (q ==> r) ==> (p ==> r)                                       *)
    (* ------------------------------------------------------------------------- *)

    let imp_add_concl r th =
        let p, q = dest_imp (concl th)
        modusponens (imp_swap (imp_trans_th p q r)) th

    (* ------------------------------------------------------------------------- *)
    (* |- (p ==> q ==> r) ==> (q ==> p ==> r)                                    *)
    (* ------------------------------------------------------------------------- *)

    let imp_swap_th p q r =
        imp_trans
            (axiom_distribimp p q r)
            (imp_add_concl (Imp (p, r)) (axiom_addimp q p))

    (* ------------------------------------------------------------------------- *)
    (*  |- (p ==> q ==> r) ==> (s ==> t ==> u)                                   *)
    (* -----------------------------------------                                 *)
    (*  |- (q ==> p ==> r) ==> (t ==> s ==> u)                                   *)
    (* ------------------------------------------------------------------------- *)

    let imp_swap2 th =
        match concl th with
        | Imp (Imp (p, Imp (q, r)), Imp (s, Imp (t, u))) ->
            imp_trans (imp_swap_th q p r) (imp_trans th (imp_swap_th s t u))
        | _ -> failwith "imp_swap2"

    (* ------------------------------------------------------------------------- *)
    (* If |- p ==> q ==> r and |- p ==> q then |- p ==> r.                       *)
    (* ------------------------------------------------------------------------- *)

    let right_mp ith th =
        imp_unduplicate (imp_trans th (imp_swap ith))

    (* ------------------------------------------------------------------------- *)
    (*                 |- p <=> q                                                *)
    (*                ------------ iff_imp1                                      *)
    (*                 |- p ==> q                                                *)
    (* ------------------------------------------------------------------------- *)

    let iff_imp1 th =
        let p, q = dest_iff (concl th)
        modusponens (axiom_iffimp1 p q) th

    (* ------------------------------------------------------------------------- *)
    (*                 |- p <=> q                                                *)
    (*                ------------ iff_imp2                                      *)
    (*                 |- q ==> p                                                *)
    (* ------------------------------------------------------------------------- *)

    let iff_imp2 th =
        let p, q = dest_iff (concl th)
        modusponens (axiom_iffimp2 p q) th

    (* ------------------------------------------------------------------------- *)
    (*         |- p ==> q      |- q ==> p                                        *)
    (*        ---------------------------- imp_antisym                           *)
    (*              |- p <=> q                                                   *)
    (* ------------------------------------------------------------------------- *)

    let imp_antisym th1 th2 =
        let p, q = dest_imp (concl th1)
        modusponens (modusponens (axiom_impiff p q) th1) th2

    (* ------------------------------------------------------------------------- *)
    (*         |- p ==> (q ==> false) ==> false                                  *)
    (*       ----------------------------------- right_doubleneg                 *)
    (*               |- p ==> q                                                  *)
    (* ------------------------------------------------------------------------- *)

    let right_doubleneg th =
        match concl th with
        | Imp (_, Imp (Imp (p, False), False)) ->
            imp_trans th (axiom_doubleneg p)
        | _ -> failwith "right_doubleneg"

    (* ------------------------------------------------------------------------- *)
    (*                                                                           *)
    (*         ------------------------------------------- ex_falso (p)          *)
    (*                 |- false ==> p                                            *)
    (* ------------------------------------------------------------------------- *)

    let ex_falso p =
        right_doubleneg (axiom_addimp False (Imp (p, False)))

    (* ------------------------------------------------------------------------- *)
    (*  |- p ==> q ==> r        |- r ==> s                                       *)
    (* ------------------------------------ imp_trans2                           *)
    (*      |- p ==> q ==> s                                                     *)
    (* ------------------------------------------------------------------------- *)

    let imp_trans2 th1 th2 =
        let p, q, r =
            match concl th1 with Imp (p, Imp (q, r)) -> p, q, r
        let r', s =
            match concl th2 with Imp (r', s) -> r', s
        let th = imp_add_assum p (modusponens (imp_trans_th q r s) th2)
        modusponens th th1

    (* ------------------------------------------------------------------------- *)
    (*         |- p ==> q1   ...   |- p ==> qn   |- q1 ==> ... ==> qn ==> r      *)
    (*        --------------------------------------------------------------     *)
    (*                             |- p ==> r                                    *)
    (* ------------------------------------------------------------------------- *)

    let imp_trans_chain ths th =
        itlist (fun a b -> imp_unduplicate (imp_trans a (imp_swap b)))
             (List.rev (List.tail ths)) (imp_trans (hd ths) th)

    (* ------------------------------------------------------------------------- *)
    (* |- (q ==> false) ==> p ==> (p ==> q) ==> false                            *)
    (* ------------------------------------------------------------------------- *)

    let imp_truefalse p q =
        imp_trans (imp_trans_th p q False) (imp_swap_th (Imp (p, q)) p False)

    (* ------------------------------------------------------------------------- *)
    (*  |- (p' ==> p) ==> (q ==> q') ==> (p ==> q) ==> (p' ==> q')               *)
    (* ------------------------------------------------------------------------- *)

    let imp_mono_th p p' q q' =
        let rec th1 = imp_trans_th (Imp (p, q)) (Imp (p', q)) (Imp (p', q'))
        and th2 = imp_trans_th p' q q'
        and th3 = imp_swap (imp_trans_th p' p q)
        imp_trans th3 (imp_swap (imp_trans th2 th1))

    (* ------------------------------------------------------------------------- *)
    (* |- true                                                                   *)
    (* ------------------------------------------------------------------------- *)

    let truth : formula<fol> =
        modusponens (iff_imp2 axiom_true) (imp_refl False)

    (* ------------------------------------------------------------------------- *)
    (*         |- p ==> q                                                        *)
    (*      ----------------- contrapos                                          *)
    (*         |- ~q ==> ~p                                                      *)
    (* ------------------------------------------------------------------------- *)

    let contrapos th =
        let p, q = dest_imp (concl th)
        imp_trans (imp_trans (iff_imp1 (axiom_not q)) (imp_add_concl False th))
            (iff_imp2 (axiom_not p))

    (* ------------------------------------------------------------------------- *)
    (* |- p /\ q ==> p                                                           *)
    (* ------------------------------------------------------------------------- *)

    let and_left p q =
        let th1 = imp_add_assum p (axiom_addimp False q)
        let th2 = right_doubleneg (imp_add_concl False th1)
        imp_trans (iff_imp1 (axiom_and p q)) th2

    (* ------------------------------------------------------------------------- *)
    (* |- p /\ q ==> q                                                           *)
    (* ------------------------------------------------------------------------- *)

    let and_right p q =
        let th1 = axiom_addimp (Imp (q, False)) p
        let th2 = right_doubleneg (imp_add_concl False th1)
        imp_trans (iff_imp1 (axiom_and p q)) th2

    (* ------------------------------------------------------------------------- *)
    (* |- p1 /\ ... /\ pn ==> pi for each 1 <= i <= n (input term right assoc)   *)
    (* ------------------------------------------------------------------------- *)

    let rec conjths fm =
        try
            let p, q = dest_and fm
            (and_left p q) :: List.map (imp_trans (and_right p q)) (conjths q)
        with Failure _ ->
            [imp_refl fm]

    (* ------------------------------------------------------------------------- *)
    (* |- p ==> q ==> p /\ q                                                     *)
    (* ------------------------------------------------------------------------- *)

    let and_pair p q =
        let rec th1 = iff_imp2 (axiom_and p q)
        and th2 = imp_swap_th (Imp (p, Imp (q, False))) q False
        let th3 = imp_add_assum p (imp_trans2 th2 th1)
        modusponens th3 (imp_swap (imp_refl (Imp (p, Imp (q, False)))))

    (* ------------------------------------------------------------------------- *)
    (* If |- p /\ q ==> r then |- p ==> q ==> r                                  *)
    (* ------------------------------------------------------------------------- *)

    let shunt th =
        let p, q = dest_and (antecedent (concl th))
        modusponens (itlist imp_add_assum [p; q] th) (and_pair p q)

    (* ------------------------------------------------------------------------- *)
    (* If |- p ==> q ==> r then |- p /\ q ==> r                                  *)
    (* ------------------------------------------------------------------------- *)

    let unshunt th =
        let p, qr = dest_imp (concl th)
        let q, r = dest_imp qr
        imp_trans_chain [and_left p q; and_right p q] th

    (* ------------------------------------------------------------------------- *)
    (* Produce |- (p <=> q) <=> (p ==> q) /\ (q ==> p)                           *)
    (* ------------------------------------------------------------------------- *)

    // TODO : Which one of these definitions of 'iff_def' is the correct one?

//    let iff_def p q =
//        let th1 = and_pair (Imp (p, q)) (Imp (q, p))
//        let th2 = imp_trans_chain [axiom_iffimp1 p q; axiom_iffimp2 p q] th1
//        imp_antisym th2 (unshunt (axiom_impiff p q))

    let iff_def p q =
        let rec th = and_pair (Imp (p, q)) (Imp (q, p))
        and thl = [axiom_iffimp1 p q; axiom_iffimp2 p q]
        imp_antisym (imp_trans_chain thl th) (unshunt (axiom_impiff p q))

    (* ------------------------------------------------------------------------- *)
    (* Produce "expansion" theorem for defined connectives.                      *)
    (* ------------------------------------------------------------------------- *)

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

    (* ------------------------------------------------------------------------- *)
    (*                                                                           *)
    (*   ------------------------------------------------- imp_false_conseqs     *)
    (*      [|- ((p ==> q) ==> false) ==> (q ==> false);                         *)
    (*       |- ((p ==> q) ==> false) ==> p]                                     *)
    (* ------------------------------------------------------------------------- *)

    let imp_false_conseqs p q = [
        right_doubleneg (imp_add_concl False (imp_add_assum p (ex_falso q)));
        imp_add_concl False (imp_insert p (imp_refl q)); ]

    (* ------------------------------------------------------------------------- *)
    (*         |- p ==> (q ==> false) ==> r                                      *)
    (*        ------------------------------------ imp_false_rule                *)
    (*             |- ((p ==> q) ==> false) ==> r                                *)
    (* ------------------------------------------------------------------------- *)

    let imp_false_rule th =
        let p, r = dest_imp (concl th)
        imp_trans_chain (imp_false_conseqs p (funpow 2 antecedent r)) th

    (* ------------------------------------------------------------------------- *)
    (*         |- (p ==> false) ==> r          |- q ==> r                        *)
    (*       ---------------------------------------------- imp_true_rule        *)
    (*                      |- (p ==> q) ==> r                                   *)
    (* ------------------------------------------------------------------------- *)

    let imp_true_rule th1 th2 =
        let rec p = funpow 2 antecedent (concl th1)
        and q = antecedent (concl th2)
        and th3 = right_doubleneg (imp_add_concl False th1)
        and th4 = imp_add_concl False th2
        let th5 = imp_swap (imp_truefalse p q)
        let rec th6 = imp_add_concl False (imp_trans_chain [th3; th4] th5)
        and th7 = imp_swap (imp_refl (Imp (Imp (p, q), False)))
        right_doubleneg (imp_trans th7 th6)

    (* ------------------------------------------------------------------------- *)
    (*                                 *                                         *)
    (*                 -------------------------------------- imp_contr          *)
    (*                        |- p ==> -p ==> q                                  *)
    (* ------------------------------------------------------------------------- *)

    let imp_contr p q =
        if negativef p then imp_add_assum (negatef p) (ex_falso q)
        else imp_swap (imp_add_assum p (ex_falso q))

    (* ------------------------------------------------------------------------- *)
    (*                                                                           *)
    (* --------------------------------------------- imp_front (this antecedent) *)
    (*  |- (p0 ==> p1 ==> ... ==> pn ==> q)                                      *)
    (*     ==> pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                              *)
    (* ------------------------------------------------------------------------- *)

    let rec imp_front_th n fm =
        if n = 0 then imp_refl fm
        else
            let p, qr = dest_imp fm
            let th1 = imp_add_assum p (imp_front_th (n - 1) qr)
            let q', r' = dest_imp (funpow 2 consequent (concl th1))
            imp_trans th1 (imp_swap_th p q' r')

    (* ------------------------------------------------------------------------- *)
    (*           |- p0 ==> p1 ==> ... ==> pn ==> q                               *)
    (*         ------------------------------------------ imp_front n            *)
    (*           |- pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                         *)
    (* ------------------------------------------------------------------------- *)

    let imp_front n th =
        modusponens (imp_front_th n (concl th)) th

    (* ------------------------------------------------------------------------- *)
    (* Propositional tableaux procedure.                                         *)
    (* ------------------------------------------------------------------------- *)

    let rec lcfptab fms lits =
        match fms with
        | False :: fl ->
            ex_falso (itlist mk_imp (fl @ lits) False)

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
                let th = imp_contr p (itlist mk_imp (List.tail l2) False)
                itlist imp_insert (fl @ l1) th
            else
                imp_front (List.length fl) (lcfptab fl (p :: lits))

        | fm :: fl ->
            let th = eliminate_connective fm
            imp_trans th (lcfptab (consequent (concl th) :: fl) lits)

        | _ ->
            failwith "lcfptab: no contradiction"

    (* ------------------------------------------------------------------------- *)
    (* In particular, this gives a tautology prover.                             *)
    (* ------------------------------------------------------------------------- *)

    let lcftaut p =
        modusponens (axiom_doubleneg p) (lcfptab [negatef p] [])

    (* ------------------------------------------------------------------------- *)
    (* The examples in the text.                                                 *)
    (* ------------------------------------------------------------------------- *)
    (*
    START_INTERACTIVE;;
    lcftaut <<(p ==> q) \/ (q ==> p)>>;;

    lcftaut <<p /\ q <=> ((p <=> q) <=> p \/ q)>>;;

    lcftaut <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;
    END_INTERACTIVE;;
    *)
