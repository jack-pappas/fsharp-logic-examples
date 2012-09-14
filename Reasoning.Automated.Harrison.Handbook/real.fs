(* ========================================================================= *)
(* Real quantifier elimination (using Cohen-Hormander algorithm).            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

namespace Reasoning.Automated.Harrison.Handbook

module real =
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

    (* ------------------------------------------------------------------------- *)
    (* Formal derivative of polynomial.                                          *)
    (* ------------------------------------------------------------------------- *)

    // TODO : Optimize using continuation-passing style.
    let rec poly_diffn x n p =
        match p with
        | Fn ("+", [c; Fn ("*", [y; q])])
            when y = x ->
            Fn ("+", [poly_cmul (Int n) c; Fn ("*", [x; poly_diffn x (n + 1) q])])
        | _ ->
            poly_cmul (Int n) p

    let poly_diff vars p =
        match p with
        | Fn ("+", [c; Fn ("*", [Var x; q])])
            when x = List.head vars ->
            poly_diffn (Var x) 1 q
        | _ -> zero

    (* ------------------------------------------------------------------------- *)
    (* Evaluate a quantifier-free formula given a sign matrix row for its polys. *)
    (* ------------------------------------------------------------------------- *)

    let rel_signs = [
        "=", [Zero];
        "<=", [Zero; Negative];
        ">=", [Zero; Positive];
        "<", [Negative];
        ">", [Positive]; ]

    let testform pmat fm =
        eval fm (fun (R (a, [p; z])) ->
            mem (assoc p pmat) (assoc a rel_signs))

    /// Infer sign of p(x) at points from corresponding qi(x) with pi(x) = 0.
    let inferpsign (pd, qd) =
        try let i = index Zero pd
            el i qd :: pd
        with Failure _ ->
            Nonzero :: pd

    /// Condense subdivision by removing points with no relevant zeros.
    let rec condense ps =
        match ps with
        | int :: pt :: other ->
            let rest = condense other
            if mem Zero pt then
                int :: pt :: rest
            else rest
        | _ -> ps

    /// Infer sign on intervals (use with infinities at end) and split if needed
    let rec inferisign ps =
        match ps with
        | ((l::ls) as x) :: (_ :: ints) :: ((r :: rs) :: xs as pts) ->
            match l, r with
            | Zero, Zero ->
                failwith "inferisign: inconsistent"
            | Nonzero, _
            | _, Nonzero ->
                failwith "inferisign: indeterminate"
            | Zero, _ ->
                x :: (r :: ints) :: inferisign pts
            | _, Zero ->
                x :: (l :: ints) :: inferisign pts
            | Negative, Negative
            | Positive, Positive ->
                x :: (l :: ints) :: inferisign pts
            | _ ->
                x :: (l :: ints) :: (Zero :: ints) :: (r :: ints) :: inferisign pts
        | _ -> ps

    /// Deduce matrix for p,p1,...,pn from matrix for p',p1,...,pn,q0,...,qn
    /// where qi = rem(p,pi) with p0 = p'.
    let dedmatrix cont mat =
        let l = List.length (List.head mat) / 2
        let mat1 = condense (List.map (inferpsign >>|> chop_list l) mat)
        let mat2 = [swap true (el 1 (List.head mat1))] :: mat1 @ [[el 1 (last mat1)]]
        let mat3 = butlast (List.tail (inferisign mat2))
        cont (condense (List.map (fun l -> List.head l :: List.tail (List.tail l)) mat3))

    /// Pseudo-division making sure the remainder has the same sign.
    let pdivide_pos vars sgns s p =
        let a = head vars p
        let (k, r) = pdivide vars s p
        let sgn = findsign sgns a
        if sgn = Zero then
            failwith "pdivide_pos: zero head coefficient"
        elif sgn = Positive || k % 2 = 0 then r
        elif sgn = Negative then poly_neg r
        else poly_mul vars a r

    /// Case splitting for positive/negative (assumed nonzero).
    let split_sign sgns pol cont =
        match findsign sgns pol with
        | Nonzero ->
            let fm = Atom (R (">", [pol; zero]))
            Or (And (fm, cont (assertsign sgns (pol, Positive))),
                And (Not fm,cont (assertsign sgns (pol, Negative))))
        | _ -> cont sgns

    let split_trichotomy sgns pol cont_z cont_pn =
        split_zero sgns pol cont_z (fun s' -> split_sign s' pol cont_pn)

    /// Main recursive evaluation of sign matrices.
    let rec casesplit vars dun pols cont sgns =
        match pols with
        | [] -> matrix vars dun cont sgns
        | p :: ops ->
            split_trichotomy sgns (head vars p)
                (if is_constant vars p then delconst vars dun p ops cont
                    else casesplit vars dun (behead vars p :: ops) cont)
                (if is_constant vars p then delconst vars dun p ops cont
                    else casesplit vars (dun @ [p]) ops cont)

    and delconst vars dun p ops cont sgns =
        let cont' m = cont (List.map (insertat (List.length dun) (findsign sgns p)) m)
        casesplit vars dun ops cont' sgns

    and matrix vars pols cont sgns =
        if pols = [] then
            try
                cont [[]]
            with Failure _ ->
                False
        else
            let p = List.head (sort (decreasing (degree vars)) pols)
            let rec p' = poly_diff vars p
            and i = index p pols
            let qs =
                let p1, p2 = chop_list i pols
                p' :: p1 @ List.tail p2
            let gs = List.map (pdivide_pos vars sgns p) qs
            let cont' m = cont (List.map (fun l -> insertat i (List.head l) (List.tail l)) m)
            casesplit vars [] (qs @ gs) (dedmatrix cont') sgns

    (* ------------------------------------------------------------------------- *)
    (* Now the actual quantifier elimination code.                               *)
    (* ------------------------------------------------------------------------- *)

    let basic_real_qelim vars (Exists (x, p)) =
        let pols = atom_union (function (R (a, [t; Fn ("0", [])])) -> [t] | _ -> []) p
        let cont mat =
            if List.exists (fun m -> testform (List.zip pols m) p) mat then
                True
            else False
        casesplit (x :: vars) [] pols cont init_sgns

    let real_qelim =
        simplify
        >>|> evalc
        >>|> lift_qelim polyatom (simplify >>|> evalc) basic_real_qelim

    (* ------------------------------------------------------------------------- *)
    (* First examples.                                                           *)
    (* ------------------------------------------------------------------------- *)

    (*
    START_INTERACTIVE;;
    real_qelim <<exists x. x^4 + x^2 + 1 = 0>>;;

    real_qelim <<exists x. x^3 - x^2 + x - 1 = 0>>;;

    real_qelim <<exists x y. x^3 - x^2 + x - 1 = 0 /\
                             y^3 - y^2 + y - 1 = 0 /\ ~(x = y)>>;;

    #trace testform;;
    real_qelim <<exists x. x^2 - 3 * x + 2 = 0 /\ 2 * x - 3 = 0>>;;
    #untrace testform;;

    real_qelim
     <<forall a f k. (forall e. k < e ==> f < a * e) ==> f <= a * k>>;;

    real_qelim <<exists x. a * x^2 + b * x + c = 0>>;;

    real_qelim <<forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                               b^2 >= 4 * a * c>>;;

    real_qelim <<forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                               a = 0 /\ (b = 0 ==> c = 0) \/
                               ~(a = 0) /\ b^2 >= 4 * a * c>>;;
    *)

    (* ------------------------------------------------------------------------- *)
    (* Termination ordering for group theory completion.                         *)
    (* ------------------------------------------------------------------------- *)

    (*
    real_qelim <<1 < 2 /\ (forall x. 1 < x ==> 1 < x^2) /\
                 (forall x y. 1 < x /\ 1 < y ==> 1 < x * (1 + 2 * y))>>;;
    END_INTERACTIVE;;
    *)

    let rec grpterm tm =
        match tm with
        | Var x -> tm
        | Fn ("*", [s; t]) ->
            let t2 = Fn ("*", [Fn ("2", []); grpterm t])
            Fn ("*", [grpterm s; Fn ("+", [Fn("1", []); t2])])
        | Fn ("i", [t]) ->
            Fn ("^", [grpterm t; Fn ("2", [])])
        | Fn ("1", []) ->
            Fn ("2", [])        

    let grpform (Atom (R ("=", [s; t]))) =
        let fm = generalize (Atom (R (">", [grpterm s; grpterm t])))
        relativize (fun x -> Atom (R (">", [Var x; Fn("1",[])]))) fm

    (*
    START_INTERACTIVE;;
    let eqs = complete_and_simplify ["1"; "*"; "i"]
      [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

    let fm = list_conj (map grpform eqs);;

    real_qelim fm;;
    END_INTERACTIVE;;
    *)

    (* ------------------------------------------------------------------------- *)
    (* A case where using DNF is an improvement.                                 *)
    (* ------------------------------------------------------------------------- *)

    let real_qelim' =
        simplify >>|> evalc >>|>
        lift_qelim polyatom (dnf >>|> cnnf (fun x -> x) >>|> evalc) basic_real_qelim

    (*
    real_qelim'
     <<forall d.
         (exists c. forall a b. (a = d /\ b = c) \/ (a = c /\ b = 1)
                                ==> a^2 = b)
         <=> d^4 = 1>>;;
    *)

    (* ------------------------------------------------------------------------- *)
    (* Didn't seem worth it in the book, but monicization can help a lot.        *)
    (* Now this is just set as an exercise.                                      *)
    (* ------------------------------------------------------------------------- *)

    #if INTERACTIVE
    (*
    let rec casesplit vars dun pols cont sgns =
      match pols with
        [] -> monicize vars dun cont sgns
      | p::ops -> split_trichotomy sgns (head vars p)
                    (if is_constant vars p then delconst vars dun p ops cont
                     else casesplit vars dun (behead vars p :: ops) cont)
                    (if is_constant vars p then delconst vars dun p ops cont
                     else casesplit vars (dun@[p]) ops cont)

    and delconst vars dun p ops cont sgns =
      let cont' m = cont(map (insertat (length dun) (findsign sgns p)) m) in
      casesplit vars dun ops cont' sgns

    and matrix vars pols cont sgns =
      if pols = [] then try cont [[]] with Failure _ -> False else
      let p = hd(sort(decreasing (degree vars)) pols) in
      let p' = poly_diff vars p and i = index p pols in
      let qs = let p1,p2 = chop_list i pols in p'::p1 @ tl p2 in
      let gs = map (pdivide_pos vars sgns p) qs in
      let cont' m = cont(map (fun l -> insertat i (hd l) (tl l)) m) in
      casesplit vars [] (qs@gs) (dedmatrix cont') sgns

    and monicize vars pols cont sgns =
      let mols,swaps = unzip(map monic pols) in
      let sols = setify mols in
      let indices = map (fun p -> index p sols) mols in
      let transform m =
        map2 (fun sw i -> swap sw (el i m)) swaps indices in
      let cont' mat = cont(map transform mat) in
      matrix vars sols cont' sgns;;

    let basic_real_qelim vars (Exists(x,p)) =
      let pols = atom_union
        (function (R(a,[t;Fn("0",[])])) -> [t] | _ -> []) p in
      let cont mat = if exists (fun m -> testform (zip pols m) p) mat
                     then True else False in
      casesplit (x::vars) [] pols cont init_sgns;;

    let real_qelim =
      simplify >>|> evalc >>|>
      lift_qelim polyatom (simplify >>|> evalc) basic_real_qelim;;

    let real_qelim' =
      simplify >>|> evalc >>|>
      lift_qelim polyatom (dnf >>|> cnnf (fun x -> x) >>|> evalc)
                          basic_real_qelim
    *)
    #endif
