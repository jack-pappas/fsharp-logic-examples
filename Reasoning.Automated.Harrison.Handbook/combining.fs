(* ========================================================================= *)
(* Nelson-Oppen combined decision procedure.                                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

namespace Reasoning.Automated.Harrison.Handbook

module combining =
    open FSharpx.Compatibility.OCaml

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

    (* ------------------------------------------------------------------------- *)
    (* Real language with decision procedure.                                    *)
    (* ------------------------------------------------------------------------- *)

    let real_lang =
        let rec fn = ["-", 1; "+", 2; "-", 2; "*", 2; "^", 2]
        and pr = ["<=", 2; "<", 2; ">=", 2; ">", 2]
        (fun (s,n) -> n = 0 && is_numeral (Fn (s, [])) || mem (s,n) fn),
        (fun sn -> mem sn pr),
        (fun fm -> real_qelim (generalize fm) = True)

    (* ------------------------------------------------------------------------- *)
    (* Integer language with decision procedure.                                 *)
    (* ------------------------------------------------------------------------- *)

    let int_lang =
        let rec fn = ["-", 1; "+", 2; "-", 2; "*", 2]
        and pr = ["<=", 2; "<", 2; ">=", 2; ">", 2]
        (fun (s,n) -> n = 0 && is_numeral (Fn (s, [])) || mem (s,n) fn),
        (fun sn -> mem sn pr),
        (fun fm -> integer_qelim (generalize fm) = True)

    (* ------------------------------------------------------------------------- *)
    (* Add any uninterpreted functions to a list of languages.                   *)
    (* ------------------------------------------------------------------------- *)

    let add_default langs =
        langs @ [(fun sn -> not (List.exists (fun (f, p, d) -> f sn) langs)),
                    (fun sn -> sn = ("=", 2)), ccvalid]

    (* ------------------------------------------------------------------------- *)
    (* Choose a language for homogenization of an atom.                          *)
    (* ------------------------------------------------------------------------- *)

    let chooselang langs fm =
        match fm with
        | Atom (R ("=", [Fn (f, args); _]))
        | Atom (R ("=", [_; Fn (f, args)])) ->
            List.find (fun (fn, pr, dp) -> fn (f, List.length args)) langs
        | Atom (R (p, args)) ->
            List.find (fun (fn, pr, dp) -> pr (p, List.length args)) langs

    (* ------------------------------------------------------------------------- *)
    (* General listification for CPS-style function.                             *)
    (* ------------------------------------------------------------------------- *)

    let rec listify f l cont =
        match l with
        | [] -> cont []
        | h :: t ->
            f h (fun h' -> listify f t (fun t' -> cont (h' :: t')))

    /// Homogenize a term.
    let rec homot (fn, pr, dp) tm cont (n : num) defs =
        match tm with
        | Var x ->
            cont tm n defs
        | Fn (f, args) ->
            if fn (f, List.length args) then
                listify (homot (fn, pr, dp)) args (fun a -> cont (Fn (f, a))) n defs
            else
                cont (Var ("v_" + n.ToString())) (n + Int 1)
                        (mk_eq (Var ("v_" + n.ToString())) tm :: defs)

    /// Homogenize a literal.
    let rec homol langs fm cont n defs =
        match fm with
        | Not f ->
            homol langs f (fun p -> cont (Not p)) n defs
        | Atom (R (p, args)) ->
            let lang = chooselang langs fm
            listify (homot lang) args (fun a -> cont (Atom (R (p, a)))) n defs
        | _ -> failwith "homol: not a literal"

    /// Fully homogenize a list of literals.
    let rec homo langs fms cont =
        listify (homol langs) fms
        <| fun dun n defs ->
            if defs = [] then cont dun n defs
            else homo langs defs (fun res -> cont (dun @ res)) n []

    /// Overall homogenization.
    let homogenize langs fms =
        let fvs = unions (List.map fv fms)
        let n = (Int 1) + itlist (max_varindex "v_") fvs (Int 0)
        homo langs fms (fun res n defs -> res) n []

    /// Whether a formula belongs to a language.
    let belongs (fn, pr, dp) fm =
        List.forall fn (functions fm) &&
        List.forall pr (subtract (predicates fm) ["=", 2])

    /// Partition formulas among a list of languages.
    let rec langpartition langs fms =
        match langs with
        | [] ->
            match fms with
            | [] -> []
            | _ ->
                failwith "langpartition"
        | l :: ls ->
            let fms1, fms2 = List.partition (belongs l) fms
            fms1 :: langpartition ls fms2

    (* ------------------------------------------------------------------------- *)
    (* Running example if we magically knew the interpolant.                     *)
    (* ------------------------------------------------------------------------- *)
    (*
    START_INTERACTIVE;;
    (integer_qelim ** generalize)
      <<(u + 1 = v /\ v_1 + 1 = u - 1 /\ v_2 - 1 = v + 1 /\ v_3 = v - 1)
        ==> u = v_3 /\ ~(v_1 = v_2)>>;;

    ccvalid
      <<(v_2 = f(v_3) /\ v_1 = f(u)) ==> ~(u = v_3 /\ ~(v_1 = v_2))>>;;
    END_INTERACTIVE;;
    *)

    (* ------------------------------------------------------------------------- *)
    (* Turn an arrangement (partition) of variables into corresponding formula.  *)
    (* ------------------------------------------------------------------------- *)

    let rec arreq l =
        match l with
        | v1 :: v2 :: rest ->
            mk_eq (Var v1) (Var v2) :: (arreq (v2 :: rest))
        | _ -> []

    let arrangement part =
        itlist (union >>|> arreq) part
             (List.map (fun (v, w) -> Not (mk_eq (Var v) (Var w)))
                  (distinctpairs (List.map hd part)))

    (* ------------------------------------------------------------------------- *)
    (* Attempt to substitute with trivial equations.                             *)
    (* ------------------------------------------------------------------------- *)

    let dest_def fm =
        match fm with
        | Atom (R ("=", [Var x; t]))
            when not (mem x (fvt t)) ->
            x, t
        | Atom (R ("=", [t; Var x]))
            when not (mem x (fvt t)) ->
            x, t
        | _ -> failwith "dest_def"

    let rec redeqs eqs =
        try
            let eq = List.find (can dest_def) eqs
            let x, t = dest_def eq
            redeqs (List.map (subst (x |=> t)) (subtract eqs [eq]))
        with Failure _ ->
            eqs

    (* ------------------------------------------------------------------------- *)
    (* Naive Nelson-Oppen variant trying all arrangements.                       *)
    (* ------------------------------------------------------------------------- *)

    let trydps ldseps fms =
        List.exists (fun ((_, _, dp), fms0) ->
            dp (Not (list_conj (redeqs (fms0 @ fms)))))
            ldseps

    let allpartitions =
        let allinsertions x l acc =
            itlist (fun p acc -> ((x :: p) :: (subtract l [p])) :: acc) l (([x] :: l) :: acc)
        fun l -> itlist (fun h y -> itlist (allinsertions h) y []) l [[]]

    // TEMP : These are commented out because of the duplicate function definitions
    // below (which are the "better" implementation).
//    let nelop_refute vars ldseps =
//        List.forall (trydps ldseps >>|> arrangement) (allpartitions vars)
//
//    let nelop1 langs fms0 =
//        let fms = homogenize langs fms0
//        let seps = langpartition langs fms
//        let fvlist = List.map (unions >>|> List.map fv) seps
//        let vars = List.filter (fun x -> List.length (List.filter (mem x) fvlist) >= 2) (unions fvlist)
//        nelop_refute vars (List.zip langs seps)
//
//    let nelop langs fm =
//        List.forall (nelop1 langs) (simpdnf (simplify (Not fm)))

    (* ------------------------------------------------------------------------- *)
    (* Check that our example works.                                             *)
    (* ------------------------------------------------------------------------- *)
    (*
    START_INTERACTIVE;;
    nelop (add_default [int_lang])
     <<f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false>>;;

    (* ------------------------------------------------------------------------- *)
    (* Bell numbers show the size of our case analysis.                          *)
    (* ------------------------------------------------------------------------- *)

    let bell n = List.length(allpartitions (1--n)) in List.map bell (1--10)

    END_INTERACTIVE;;
    *)

    (* ------------------------------------------------------------------------- *)
    (* Find the smallest subset satisfying a predicate.                          *)
    (* ------------------------------------------------------------------------- *)

    // TODO : Optimize by using the Maybe or Either monads instead of using
    // exceptions for control flow.
    let rec findasubset p m l =
        if m = 0 then p [] else
        match l with
        | [] -> failwith "findasubset"
        | h :: t ->
            try findasubset (fun s -> p (h :: s)) (m - 1) t
            with Failure _ -> findasubset p m t

    let findsubset p l =
        tryfind (fun n ->
            findasubset (fun x -> if p x then x else failwith "") n l)
            (0 -- List.length l)

    (* ------------------------------------------------------------------------- *)
    (* The "true" Nelson-Oppen method.                                           *)
    (* ------------------------------------------------------------------------- *)

    let rec nelop_refute eqs ldseps =
        try
            let dj = findsubset (trydps ldseps >>|> List.map negate) eqs
            List.forall (fun eq ->
                nelop_refute (subtract eqs [eq]) (List.map (fun (dps, es) ->
                    (dps, eq :: es)) ldseps)) dj
        with Failure _ ->
            false

    let nelop1 langs fms0 =
        let fms = homogenize langs fms0
        let seps = langpartition langs fms
        let fvlist = List.map (unions >>|> List.map fv) seps
        let vars = List.filter (fun x -> List.length (List.filter (mem x) fvlist) >= 2) (unions fvlist)
        let eqs = List.map (fun (a, b) -> mk_eq (Var a) (Var b)) (distinctpairs vars)
        nelop_refute eqs (List.zip langs seps)

    let nelop langs fm =
        List.forall (nelop1 langs) (simpdnf (simplify (Not fm)))

    (* ------------------------------------------------------------------------- *)
    (* Some additional examples (from ICS paper and Shostak's "A practical..."   *)
    (* ------------------------------------------------------------------------- *)
    (*
    START_INTERACTIVE;;
    nelop (add_default [int_lang])
     <<y <= x /\ y >= x + z /\ z >= 0 ==> f(f(x) - f(y)) = f(z)>>;;

    nelop (add_default [int_lang])
     <<x = y /\ y >= z /\ z >= x ==> f(z) = f(x)>>;;

    nelop (add_default [int_lang])
     <<a <= b /\ b <= f(a) /\ f(a) <= 1
      ==> a + b <= 1 \/ b + f(b) <= 1 \/ f(f(b)) <= f(a)>>;;
    *)
    (* ------------------------------------------------------------------------- *)
    (* Confirmation of non-convexity.                                            *)
    (* ------------------------------------------------------------------------- *)

//    map (real_qelim ** generalize)
//      [<<x * y = 0 /\ z = 0 ==> x = z \/ y = z>>;
//       <<x * y = 0 /\ z = 0 ==> x = z>>;
//       <<x * y = 0 /\ z = 0 ==> y = z>>];;
//
//    map (integer_qelim ** generalize)
//      [<<0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y \/ x = z>>;
//       <<0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y>>;
//       <<0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = z>>];;

    (* ------------------------------------------------------------------------- *)
    (* Failures of original Shostak procedure.                                   *)
    (* ------------------------------------------------------------------------- *)

//    nelop (add_default [int_lang])
//     <<f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false>>;;

    (*** And this one is where the original procedure loops ***)

//    nelop (add_default [int_lang])
//     <<f(v) = v /\ f(u) = u - 1 /\ u = v ==> false>>;;

    (* ------------------------------------------------------------------------- *)
    (* Additional examples not in the text.                                      *)
    (* ------------------------------------------------------------------------- *)

    (*** This is on p. 8 of Shostak's "Deciding combinations" paper ***)

//    time (nelop (add_default [int_lang]))
//     <<z = f(x - y) /\ x = z + y /\ ~(-(y) = -(x - f(f(z)))) ==> false>>;;

    (*** This (ICS theories-1) fails without array operations ***)

//    time (nelop (add_default [int_lang]))
//     <<a + 2 = b ==> f(read(update(A,a,3),b-2)) = f(b - a + 1)>>;;

    (*** can-001 from ICS examples site, with if-then-elses expanded manually ***)

//    time (nelop (add_default [int_lang]))
//     <<(x = y /\ z = 1 ==> f(f((x+z))) = f(f((1+y))))>>;;

    (*** RJB example; lists plus uninterpreted functions ***)

//    time (nelop (add_default [int_lang]))
//     <<hd(x) = hd(y) /\ tl(x) = tl(y) /\ ~(x = nil) /\ ~(y = nil)
//       ==> f(x) = f(y)>>;;

    (*** Another one from the ICS paper ***)

//    time (nelop (add_default [int_lang]))
//     <<~(f(f(x) - f(y)) = f(z)) /\ y <= x /\ y >= x + z /\ z >= 0 ==> false>>;;

    (*** Shostak's "A Practical Decision Procedure..." paper
     *** No longer works since I didn't do predicates in congruence closure
    time (nelop (add_default [int_lang]))
     <<x < f(y) + 1 /\ f(y) <= x ==> (P(x,y) <=> P(f(y),y))>>;;
     ***)

    (*** Shostak's "Practical..." paper again, using extra clauses for MAX ***)

//    time (nelop (add_default [int_lang]))
//     <<(x >= y ==> MAX(x,y) = x) /\ (y >= x ==> MAX(x,y) = y)
//       ==> x = y + 2 ==> MAX(x,y) = x>>;;

    (*** Shostak's "Practical..." paper again ***)

//    time (nelop (add_default [int_lang]))
//     <<x <= g(x) /\ x >= g(x) ==> x = g(g(g(g(x))))>>;;

    (*** Easy example I invented ***)

//    time (nelop (add_default [real_lang]))
//     <<x^2 =  1 ==> (f(x) = f(-(x)))  ==> (f(x) = f(1))>>;;

    (*** Taken from Clark Barrett's CVC page ***)

//    time (nelop (add_default [int_lang]))
//     <<2 * f(x + y) = 3 * y /\ 2 * x = y ==> f(f(x + y)) = 3 * x>>;;

    (*** My former running example in the text; seems too slow.
     *** Anyway this also needs extra predicates in CC

    time (nelop (add_default [real_lang]))
     <<x^2 = y^2 /\ x < y /\ z^2 = z /\ x < x * z /\ P(f(1 + z))
      ==> P(f(x + y) - f(0))>>;;
     ***)

    (*** An example where the "naive" procedure is slow but feasible ***)

//    nelop (add_default [int_lang])
//     <<4 * x = 2 * x + 2 * y /\ x = f(2 * x - y) /\
//      f(2 * y - x) = 3 /\ f(x) = 4 ==> false>>;;

    //END_INTERACTIVE;;
