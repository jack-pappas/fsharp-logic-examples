// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Jack Pappas, Eric Taucher                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

//  ========================================================================= // 
//  First order tableau procedure using LCF setup.                            // 
//  ========================================================================= // 

module Reasoning.Automated.Harrison.Handbook.lcffol

open intro
open formulas
open prop
open defcnf
open dp
open stal
open bdd
open fol
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

// pg. 494
//  ------------------------------------------------------------------------- // 
//  Unification of complementary literals.                                    // 
//  ------------------------------------------------------------------------- // 

let unify_complementsf env = function
    | Atom (R (p1, a1)), Imp (Atom (R (p2, a2)), False)
    | Imp (Atom (R (p1, a1)), False), Atom (R (p2, a2)) ->
        unify env [Fn (p1, a1), Fn (p2, a2)]
    | _ ->
        failwith "unify_complementsf"
            
// pg. 497
//  ------------------------------------------------------------------------- // 
//     |- (q ==> f) ==> ... ==> (q ==> p) ==> r                               // 
//  --------------------------------------------- use_laterimp <<q ==> p>>    // 
//     |- (p ==> f) ==> ... ==> (q ==> p) ==> r                               // 
//  ------------------------------------------------------------------------- // 

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
            
// pg. 497
//  ------------------------------------------------------------------------- // 
//  The "closure" inference rules.                                            // 
//  ------------------------------------------------------------------------- // 

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
    ex_falso (List.foldBack (mk_imp << onformula e) fms s)

let complits' (p :: fl, lits) i (e, s) =
    let l1, p' :: l2 = chop_list i lits
    List.foldBack (imp_insert << onformula e) (fl @ l1)
            (imp_contr (onformula e p)
                    (List.foldBack (mk_imp << onformula e) l2 s))

let deskol' (skh : fol formula) thp (e, s) =
    let th = thp (e, s)
    modusponens (use_laterimp (onformula e skh) (concl th)) th
        
// pg. 499
//  ------------------------------------------------------------------------- // 
//  Main refutation function.                                                 // 
//  ------------------------------------------------------------------------- // 

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
            lcftab skofun (fl, lits, n) (cont << add_assum' fm) esk

        | Imp (Imp (p, q), False) :: fl ->
            lcftab skofun (p :: Imp (q, False) :: fl, lits, n) (cont << imp_false_rule') esk

        | Imp (p, q) :: fl when q <> False ->
            lcftab skofun (Imp (p, False) :: fl, lits, n) (fun th ->
                lcftab skofun (q :: fl, lits, n) (cont << imp_true_rule' th)) esk

        | ((Atom _ | Imp (Atom _, False)) as p) :: fl ->
            try tryfind (fun p' ->
                let env' = unify_complementsf env (p, p')
                cont (complits' (fms, lits) (index p' lits)) (env', sks, k)) lits
            with Failure _ ->
                lcftab skofun (fl,p::lits,n) (cont << imp_front' (List.length fl)) esk

        | (Forall (x, p) as fm) :: fl ->
            let y = Var ("X_" + string k)
            lcftab skofun ((subst (x |=> y) p) :: fl @ [fm], lits, n - 1)
                        (cont << spec' y fm (List.length fms)) (env, sks, k + 1)

        | (Imp (Forall (y, p) as yp, False)) :: fl ->
            let fx = skofun yp
            let p' = subst (y |=> fx) p
            let skh = Imp (p', Forall (y, p))
            let sks' = (Forall (y, p), fx) :: sks
            lcftab skofun (Imp (p', False) :: fl, lits, n) (cont << deskol' skh) (env, sks', k)

        | fm :: fl ->
            let fm' = consequent (concl (eliminate_connective fm))
            lcftab skofun (fm' :: fl, lits, n) (cont << eliminate_connective' fm) esk
          
// pg. 500
//  ------------------------------------------------------------------------- // 
//  Identify quantified subformulas; true = exists, false = forall. This is   // 
//  taking into account the effective parity.                                 // 
//  NB: maybe I can use this in sigma/delta/pi determination.                 // 
//  ------------------------------------------------------------------------- // 

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
        
// pg. 500
//  ------------------------------------------------------------------------- // 
//  Now create some Skolem functions.                                         // 
//  ------------------------------------------------------------------------- // 

let skolemfuns fm =
    let rec fns = List.map fst (functions fm)
    and skts = List.map (function Exists (x, p) -> Forall (x,Not p) | p -> p) (quantforms true fm)
    let skofun i (Forall (y, p) as ap) =
        let vars = List.map (fun v -> Var v) (fv ap)
        ap, Fn (variant ("f_" + string i) fns, vars)
    List.map2 skofun (1 -- List.length skts) skts
        
// pg. 501
//  ------------------------------------------------------------------------- // 
//  Matching.                                                                 // 
//  ------------------------------------------------------------------------- // 

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
        
// pg. 501
//  ------------------------------------------------------------------------- // 
//  With the current approach to picking Skolem functions.                    // 
//  ------------------------------------------------------------------------- // 

let lcfrefute fm n cont =
    let sl = skolemfuns fm
    let find_skolem fm =            
        tryfind (fun (f,t) -> tsubst(form_match (f,fm) undefined) t) sl
    lcftab find_skolem ([fm], [], n) cont (undefined, [], 0)
        
// pg. 501
//  ------------------------------------------------------------------------- // 
//  A quick demo before doing deskolemization.                                // 
//  ------------------------------------------------------------------------- // 

let mk_skol (Forall(y, p), fx) q =
    Imp (Imp (subst (y |=> fx) p, Forall (y, p)), q)

let simpcont thp (env, sks, k) =
    let ifn = tsubst (solve env)
    thp (ifn, onformula ifn (List.foldBack mk_skol sks False))
      
// pg. 502
//  ------------------------------------------------------------------------- // 
//          |- (p(v) ==> forall x. p(x)) ==> q                                // 
//        -------------------------------------- elim_skolemvar               // 
//                    |- q                                                    // 
//  ------------------------------------------------------------------------- // 

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
            
// pg. 503
//  ------------------------------------------------------------------------- // 
//  Top continuation with careful sorting and variable replacement.           // 
//  Also need to delete post-instantiation duplicates! This shows up more     // 
//  often now that we have adequate sharing.                                  // 
//  ------------------------------------------------------------------------- // 

let deskolcont thp (env, sks, k) =
    let ifn = tsubst (solve env)
    let isk = setify (List.map (fun (p, t) -> onformula ifn p, ifn t) sks)
    let ssk = sort (decreasing (termsize << snd)) isk
    let vs = List.map (fun i -> Var ("Y_" + string i)) (1 -- List.length ssk)
    let vfn =
        replacet (List.foldBack2 (fun (p, t) v -> t |-> v) ssk vs undefined)
    let th = thp (vfn << ifn, onformula vfn (List.foldBack mk_skol ssk False))
    repeat (elim_skolemvar << imp_swap) th
        
// pg. 504
//  ------------------------------------------------------------------------- // 
//  Overall first-order prover.                                               // 
//  ------------------------------------------------------------------------- // 

let lcffol fm =
    let fvs = fv fm
    let fm' = Imp(List.foldBack mk_forall fvs fm,False)
    let th1 = deepen (fun n -> lcfrefute fm' n deskolcont) 0
    let th2 = modusponens (axiom_doubleneg (negatef fm')) th1
    List.foldBack (fun v -> spec (Var v)) (List.rev fvs) th2