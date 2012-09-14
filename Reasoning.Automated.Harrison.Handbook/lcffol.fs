(* ========================================================================= *)
(* First order tableau procedure using LCF setup.                            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

namespace Reasoning.Automated.Harrison.Handbook

module lcffol =
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
    open folderived

    (* ------------------------------------------------------------------------- *)
    (* Unification of complementary literals.                                    *)
    (* ------------------------------------------------------------------------- *)

    let unify_complementsf env = function
        | Atom (R (p1, a1)), Imp (Atom (R (p2, a2)), False)
        | Imp (Atom (R (p1, a1)), False), Atom (R (p2, a2)) ->
            unify env [Fn (p1, a1), Fn (p2, a2)]
        | _ ->
            failwith "unify_complementsf"

    (* ------------------------------------------------------------------------- *)
    (*    |- (q ==> f) ==> ... ==> (q ==> p) ==> r                               *)
    (* --------------------------------------------- use_laterimp <<q ==> p>>    *)
    (*    |- (p ==> f) ==> ... ==> (q ==> p) ==> r                               *)
    (* ------------------------------------------------------------------------- *)

    let rec use_laterimp i fm =
        match fm with
        | Imp (Imp (q', s), Imp (Imp (q, p) as i', r))
            when i' = i ->
            let rec th1 = axiom_distribimp i (Imp (Imp (q, s), r)) (Imp (Imp (p, s), r))
            and th2 = imp_swap(imp_trans_th q p s)
            and th3 = imp_swap(imp_trans_th (Imp (p, s)) (Imp (q, s)) r)
            imp_swap2(modusponens th1 (imp_trans th2 th3))
        | Imp (qs, Imp (a, b)) ->
            imp_swap2 (imp_add_assum a (use_laterimp i (Imp (qs, b))))

    (* ------------------------------------------------------------------------- *)
    (* The "closure" inference rules.                                            *)
    (* ------------------------------------------------------------------------- *)

    let imp_false_rule' th es =
        imp_false_rule (th es)

    let imp_true_rule' th1 th2 es =
        imp_true_rule (th1 es) (th2 es)

    let imp_front' n thp es =
        imp_front n (thp es)

    let add_assum' fm thp (e, s as es) =
        add_assum (onformula e fm) (thp es)

    let eliminate_connective' fm thp (e, s as es) =
        imp_trans (eliminate_connective (onformula e fm)) (thp es)

    let spec' y fm n thp (e, s) =
        let th = imp_swap (imp_front n (thp (e, s)))
        imp_unduplicate (imp_trans (ispec (e y) (onformula e fm)) th)

    let ex_falso' fms (e, s) =
        ex_falso (itlist (mk_imp >>|> onformula e) fms s)

    let complits' (p :: fl, lits) i (e, s) =
        let l1, p' :: l2 = chop_list i lits
        itlist (imp_insert >>|> onformula e) (fl @ l1)
             (imp_contr (onformula e p)
                        (itlist (mk_imp >>|> onformula e) l2 s))

    let deskol' (skh : fol formula) thp (e, s) =
        let th = thp (e, s)
        modusponens (use_laterimp (onformula e skh) (concl th)) th

    (* ------------------------------------------------------------------------- *)
    (* Main refutation function.                                                 *)
    (* ------------------------------------------------------------------------- *)

    let rec lcftab skofun (fms, lits, n) cont (env, sks, k as esk) =
        if n < 0 then
            failwith "lcftab: no proof"
        else
            match fms with
            | [] ->
                failwith "lcftab: No contradiction"
            | False :: fl ->
                cont (ex_falso' (fl @ lits)) esk

            | (Imp (p, q) as fm) :: fl
                when p = q ->
                lcftab skofun (fl, lits, n) (cont >>|> add_assum' fm) esk

            | Imp (Imp (p, q), False) :: fl ->
                lcftab skofun (p :: Imp (q, False) :: fl, lits, n) (cont >>|> imp_false_rule') esk

            | Imp (p, q) :: fl when q <> False ->
                lcftab skofun (Imp (p, False) :: fl, lits, n) (fun th ->
                    lcftab skofun (q :: fl, lits, n) (cont >>|> imp_true_rule' th)) esk

            | ((Atom _ | Imp (Atom _, False)) as p) :: fl ->
                try tryfind (fun p' ->
                    let env' = unify_complementsf env (p, p')
                    cont (complits' (fms, lits) (index p' lits)) (env', sks, k)) lits
                with Failure _ ->
                    lcftab skofun (fl,p::lits,n) (cont >>|> imp_front' (List.length fl)) esk

            | (Forall (x, p) as fm) :: fl ->
                let y = Var ("X_" + string k)
                lcftab skofun ((subst (x |=> y) p) :: fl @ [fm], lits, n - 1)
                            (cont >>|> spec' y fm (List.length fms)) (env, sks, k + 1)

            | (Imp (Forall (y, p) as yp, False)) :: fl ->
                let fx = skofun yp
                let p' = subst (y |=> fx) p
                let skh = Imp (p', Forall (y, p))
                let sks' = (Forall (y, p), fx) :: sks
                lcftab skofun (Imp (p', False) :: fl, lits, n) (cont >>|> deskol' skh) (env, sks', k)

            | fm :: fl ->
                let fm' = consequent (concl (eliminate_connective fm))
                lcftab skofun (fm' :: fl, lits, n) (cont >>|> eliminate_connective' fm) esk
          

    (* ------------------------------------------------------------------------- *)
    (* Identify quantified subformulas; true = exists, false = forall. This is   *)
    (* taking into account the effective parity.                                 *)
    (* NB: maybe I can use this in sigma/delta/pi determination.                 *)
    (* ------------------------------------------------------------------------- *)

    let rec quantforms e fm =
        match fm with
        | Not p ->
            quantforms (not e) p
        | And (p, q)
        | Or (p, q) ->
            union (quantforms e p) (quantforms e q)
        | Imp (p, q) ->
            quantforms e (Or (Not p, q))
        | Iff (p, q) ->
            quantforms e (Or (And (p, q), And (Not p, Not q)))
        | Exists (x, p) ->
            if e then fm :: (quantforms e p) else quantforms e p
        | Forall (x, p) ->
            if e then quantforms e p else fm :: (quantforms e p)
        | _ -> []

    (* ------------------------------------------------------------------------- *)
    (* Now create some Skolem functions.                                         *)
    (* ------------------------------------------------------------------------- *)

    let skolemfuns fm =
        let rec fns = List.map fst (functions fm)
        and skts = List.map (function Exists (x, p) -> Forall (x,Not p) | p -> p) (quantforms true fm)
        let skofun i (Forall (y, p) as ap) =
            let vars = List.map (fun v -> Var v) (fv ap)
            ap, Fn (variant ("f_" + string i) fns, vars)
        List.map2 skofun (1 -- List.length skts) skts

    (* ------------------------------------------------------------------------- *)
    (* Matching.                                                                 *)
    (* ------------------------------------------------------------------------- *)

    let rec form_match (f1,f2 as fp) env =
        match fp with
        | False, False
        | True, True ->
            env
        | Atom (R (p, pa)), Atom (R (q, qa)) ->
            term_match env [Fn (p, pa), Fn (q, qa)]
        | Not p1, Not p2 ->
            form_match (p1, p2) env
        | And (p1, q1), And (p2, q2)
        | Or (p1, q1), Or (p2, q2)
        | Imp (p1, q1), Imp (p2, q2)
        | Iff (p1, q1), Iff (p2, q2) ->
            form_match (p1, p2) (form_match (q1, q2) env)
        | Forall (x1, p1), Forall (x2, p2)
        | Exists (x1, p1), Exists (x2, p2)
            when x1 = x2 ->
            let z = variant x1 (union (fv p1) (fv p2))
            let inst_fn = subst (x1 |=> Var z)
            undefine z (form_match (inst_fn p1,inst_fn p2) env)
        | _ -> failwith "form_match"

    (* ------------------------------------------------------------------------- *)
    (* With the current approach to picking Skolem functions.                    *)
    (* ------------------------------------------------------------------------- *)

    let lcfrefute fm n cont =
        let sl = skolemfuns fm
        let find_skolem fm =            
            tryfind (fun (f,t) -> tsubst(form_match (f,fm) undefined) t) sl
        lcftab find_skolem ([fm], [], n) cont (undefined, [], 0)

    (* ------------------------------------------------------------------------- *)
    (* A quick demo before doing deskolemization.                                *)
    (* ------------------------------------------------------------------------- *)

    let mk_skol (Forall(y, p), fx) q =
        Imp (Imp (subst (y |=> fx) p, Forall (y, p)), q)

    let simpcont thp (env, sks, k) =
      let ifn = tsubst (solve env)
      thp (ifn, onformula ifn (itlist mk_skol sks False))

    (*
    lcfrefute <<p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))>> 1 simpcont;;

    lcfrefute <<(exists x. ~p(x)) /\ (forall x. p(x))>> 1 simpcont;;
    *)

    (* ------------------------------------------------------------------------- *)
    (*         |- (p(v) ==> forall x. p(x)) ==> q                                *)
    (*       -------------------------------------- elim_skolemvar               *)
    (*                   |- q                                                    *)
    (* ------------------------------------------------------------------------- *)

    let elim_skolemvar th =
        match concl th with
        | Imp (Imp (pv, (Forall (x, px) as apx)), q) ->
            let [th1; th2] =
                List.map (imp_trans(imp_add_concl False th)) (imp_false_conseqs pv apx)
            let v = List.head (subtract (fv pv) (fv apx) @ [x])
            let th3 = gen_right v th1
            let th4 = imp_trans th3 (alpha x (consequent (concl th3)))
            modusponens (axiom_doubleneg q) (right_mp th2 th4)
        | _ ->
            failwith "elim_skolemvar"

    (* ------------------------------------------------------------------------- *)
    (* Top continuation with careful sorting and variable replacement.           *)
    (* Also need to delete post-instantiation duplicates! This shows up more     *)
    (* often now that we have adequate sharing.                                  *)
    (* ------------------------------------------------------------------------- *)

    let deskolcont thp (env, sks, k) =
        let ifn = tsubst (solve env)
        let isk = setify (List.map (fun (p, t) -> onformula ifn p, ifn t) sks)
        let ssk = sort (decreasing (termsize >>|> snd)) isk
        let vs = List.map (fun i -> Var ("Y_" + string i)) (1 -- List.length ssk)
        let vfn =
            replacet (itlist2 (fun (p, t) v -> t |-> v) ssk vs undefined)
        let th = thp (vfn >>|> ifn, onformula vfn (itlist mk_skol ssk False))
        repeat (elim_skolemvar >>|> imp_swap) th

    (* ------------------------------------------------------------------------- *)
    (* Overall first-order prover.                                               *)
    (* ------------------------------------------------------------------------- *)

    let lcffol fm =
        let fvs = fv fm
        let fm' = Imp(itlist mk_forall fvs fm,False)
        let th1 = deepen (fun n -> lcfrefute fm' n deskolcont) 0
        let th2 = modusponens (axiom_doubleneg (negatef fm')) th1
        itlist (fun v -> spec (Var v)) (List.rev fvs) th2

    (* ------------------------------------------------------------------------- *)
    (* Examples in the text.                                                     *)
    (* ------------------------------------------------------------------------- *)
    (*
    START_INTERACTIVE;;
    let p58 = lcffol
     <<forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

    let ewd1062_1 = lcffol
     <<(forall x. x <= x) /\
       (forall x y z. x <= y /\ y <= z ==> x <= z) /\
       (forall x y. f(x) <= y <=> x <= g(y))
       ==> (forall x y. x <= y ==> f(x) <= f(y))>>;;
    END_INTERACTIVE;;
    *)

    (* ------------------------------------------------------------------------- *)
    (* More exhaustive set of tests not in the main text.                        *)
    (* ------------------------------------------------------------------------- *)
    (*
    START_INTERACTIVE;;

    let start_time = Sys.time();;

    let p1 = time lcftaut
     <<p ==> q <=> ~q ==> ~p>>;;

    let p2 = time lcftaut
     <<~ ~p <=> p>>;;

    let p3 = time lcftaut
     <<~(p ==> q) ==> q ==> p>>;;

    let p4 = time lcftaut
     <<~p ==> q <=> ~q ==> p>>;;

    let p5 = time lcftaut
     <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

    let p6 = time lcftaut
     <<p \/ ~p>>;;

    let p7 = time lcftaut
     <<p \/ ~ ~ ~p>>;;

    let p8 = time lcftaut
     <<((p ==> q) ==> p) ==> p>>;;

    let p9 = time lcftaut
     <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

    let p10 = time lcftaut
     <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

    let p11 = time lcftaut
     <<p <=> p>>;;

    let p12 = time lcftaut
     <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

    let p13 = time lcftaut
     <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

    let p14 = time lcftaut
     <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

    let p15 = time lcftaut
     <<p ==> q <=> ~p \/ q>>;;

    let p16 = time lcftaut
     <<(p ==> q) \/ (q ==> p)>>;;

    let p17 = time lcftaut
     <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

    let p1 = time lcffol
     <<p ==> q <=> ~q ==> ~p>>;;

    let p2 = time lcffol
     <<~ ~p <=> p>>;;

    let p3 = time lcffol
     <<~(p ==> q) ==> q ==> p>>;;

    let p4 = time lcffol
     <<~p ==> q <=> ~q ==> p>>;;

    let p5 = time lcffol
     <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

    let p6 = time lcffol
     <<p \/ ~p>>;;

    let p7 = time lcffol
     <<p \/ ~ ~ ~p>>;;

    let p8 = time lcffol
     <<((p ==> q) ==> p) ==> p>>;;

    let p9 = time lcffol
     <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

    let p10 = time lcffol
     <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

    let p11 = time lcffol
     <<p <=> p>>;;

    let p12 = time lcffol
     <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

    let p13 = time lcffol
     <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

    let p14 = time lcffol
     <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

    let p15 = time lcffol
     <<p ==> q <=> ~p \/ q>>;;

    let p16 = time lcffol
     <<(p ==> q) \/ (q ==> p)>>;;

    let p17 = time lcffol
     <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

    let p18 = time lcffol
     <<exists y. forall x. P(y) ==> P(x)>>;;

    let p19 = time lcffol
     <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

    let p20 = time lcffol
     <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
       ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

    let p21 = time lcffol
     <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
       ==> (exists x. P <=> Q(x))>>;;

    let p22 = time lcffol
     <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

    let p23 = time lcffol
     <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

    let p24 = time lcffol
     <<~(exists x. U(x) /\ Q(x)) /\
       (forall x. P(x) ==> Q(x) \/ R(x)) /\
       ~(exists x. P(x) ==> (exists x. Q(x))) /\
       (forall x. Q(x) /\ R(x) ==> U(x)) ==>
       (exists x. P(x) /\ R(x))>>;;

    let p25 = time lcffol
     <<(exists x. P(x)) /\
       (forall x. U(x) ==> ~G(x) /\ R(x)) /\
       (forall x. P(x) ==> G(x) /\ U(x)) /\
       ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
       ==> (exists x. Q(x) /\ P(x))>>;;

    let p26 = time lcffol
     <<((exists x. P(x)) <=> (exists x. Q(x))) /\
       (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
       ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

    let p27 = time lcffol
     <<(exists x. P(x) /\ ~Q(x)) /\
       (forall x. P(x) ==> R(x)) /\
       (forall x. U(x) /\ V(x) ==> P(x)) /\
       (exists x. R(x) /\ ~Q(x))
       ==> (forall x. U(x) ==> ~R(x))
           ==> (forall x. U(x) ==> ~V(x))>>;;

    let p28 = time lcffol
     <<(forall x. P(x) ==> (forall x. Q(x))) /\
       ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
       ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
       (forall x. P(x) /\ L(x) ==> M(x))>>;;

    let p29 = time lcffol
     <<(exists x. P(x)) /\ (exists x. G(x)) ==>
       ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

    let p30 = time lcffol
     <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\
       (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
       ==> (forall x. U(x))>>;;

    let p31 = time lcffol
     <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\
       (exists x. Q(x) /\ P(x)) /\
       (forall x. ~H(x) ==> J(x))
       ==> (exists x. Q(x) /\ J(x))>>;;

    let p32 = time lcffol
     <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
       (forall x. Q(x) /\ H(x) ==> J(x)) /\
       (forall x. R(x) ==> H(x))
       ==> (forall x. P(x) /\ R(x) ==> J(x))>>;;

    let p33 = time lcffol
     <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
       (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

    *)

    (***** NEWLY HARD

    let p34 = time lcffol
     <<((exists x. forall y. P(x) <=> P(y)) <=>
        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
       ((exists x. forall y. Q(x) <=> Q(y)) <=>
        ((exists x. P(x)) <=> (forall y. P(y))))>>;;

     *****)

    (*
    let p35 = time lcffol
     <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

    let p36 = time lcffol
     <<(forall x. exists y. P(x,y)) /\
       (forall x. exists y. G(x,y)) /\
       (forall x y. P(x,y) \/ G(x,y)
       ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
           ==> (forall x. exists y. H(x,y))>>;;

    let p37 = time lcffol
     <<(forall z.
         exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
         (P(y,w) ==> (exists u. Q(u,w)))) /\
       (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
       ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
       (forall x. exists y. R(x,y))>>;;

    let p38 = time lcffol
     <<(forall x.
         P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
         (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
       (forall x.
         (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
         (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
         (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

    let p39 = time lcffol
     <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

    let p40 = time lcffol
     <<(exists y. forall x. P(x,y) <=> P(x,x))
      ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

    let p41 = time lcffol
     <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
      ==> ~(exists z. forall x. P(x,z))>>;;

    let p42 = time lcffol
     <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

    *)

    (***** SEEMS HARD
    let p43 = time lcffol
     <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
       ==> forall x y. Q(x,y) <=> Q(y,x)>>;;
     *****)

    (*
    let p44 = time lcffol
     <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
       (exists y. G(y) /\ ~H(x,y))) /\
       (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
       (exists x. J(x) /\ ~P(x))>>;;
    *)

    (**** SEEMS HARD

    let p45 = time lcffol
     <<(forall x.
         P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
           (forall y. G(y) /\ H(x,y) ==> R(y))) /\
       ~(exists y. L(y) /\ R(y)) /\
       (exists x. P(x) /\ (forall y. H(x,y) ==>
         L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
       (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;
     ******)

    (*
    let p55 = time lcffol
     <<lives(agatha) /\ lives(butler) /\ lives(charles) /\
       (killed(agatha,agatha) \/ killed(butler,agatha) \/
        killed(charles,agatha)) /\
       (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
       (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
       (hates(agatha,agatha) /\ hates(agatha,charles)) /\
       (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
       (forall x. hates(agatha,x) ==> hates(butler,x)) /\
       (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
       ==> killed(agatha,agatha) /\
           ~killed(butler,agatha) /\
           ~killed(charles,agatha)>>;;

    let p57 = time lcffol
     <<P(f(a,b),f(b,c)) /\
       P(f(b,c),f(a,c)) /\
       (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z))
       ==> P(f(a,b),f(a,c))>>;;

    let p58 = time lcffol
     <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

    let p59 = time lcffol
     <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

    let p60 = time lcffol
     <<forall x. P(x,f(x)) <=>
                exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

    let gilmore_3 = time lcffol
     <<exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> H(z)) /\
            F(x,y)
            ==> F(z,z)>>;;

    let gilmore_4 = time lcffol
     <<exists x y. forall z.
            (F(x,y) ==> F(y,z) /\ F(z,z)) /\
            (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

    let gilmore_5 = time lcffol
     <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
       (forall x y. F(y,x) ==> F(y,y))
       ==> exists z. F(z,z)>>;;

    let gilmore_6 = time lcffol
     <<forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

    let gilmore_7 = time lcffol
     <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
       (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
       ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

    let gilmore_8 = time lcffol
     <<exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)>>;;

    let gilmore_9 = time lcffol
     <<forall x. exists y. forall z.
            ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
              ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
              ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
            ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
             ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

    let davis_putnam_example = time lcffol
     <<exists x. exists y. forall z.
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

    let ewd1062_1 = time lcffol
     <<(forall x. x <= x) /\
       (forall x y z. x <= y /\ y <= z ==> x <= z) /\
       (forall x y. f(x) <= y <=> x <= g(y))
       ==> (forall x y. x <= y ==> f(x) <= f(y))>>;;

    let ewd1062_2 = time lcffol
     <<(forall x. x <= x) /\
       (forall x y z. x <= y /\ y <= z ==> x <= z) /\
       (forall x y. f(x) <= y <=> x <= g(y))
       ==> (forall x y. x <= y ==> g(x) <= g(y))>>;;

    let finish_time = Sys.time() in
    print_string
     ("Complete CPU time (user): "^
      (string_of_float(finish_time -. start_time)));;
      print_newline();;

    END_INTERACTIVE;;
    *)

