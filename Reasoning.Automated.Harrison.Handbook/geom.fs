(* ========================================================================= *)
(* Geometry theorem proving.                                                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

namespace Reasoning.Automated.Harrison.Handbook

module geom =
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

    (* ------------------------------------------------------------------------- *)
    (* List of geometric properties with their coordinate translations.          *)
    (* ------------------------------------------------------------------------- *)
    (*
    let coordinations =
      ["collinear", (** Points 1, 2 and 3 lie on a common line **)
       <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x)>>;
       "parallel", (** Lines (1,2) and (3,4) are parallel **)
        <<(1_x - 2_x) * (3_y - 4_y) = (1_y - 2_y) * (3_x - 4_x)>>;
       "perpendicular", (** Lines (1,2) and (3,4) are perpendicular **)
       <<(1_x - 2_x) * (3_x - 4_x) + (1_y - 2_y) * (3_y - 4_y) = 0>>;
       "lengths_eq", (** Lines (1,2) and (3,4) have the same length **)
       <<(1_x - 2_x)^2 + (1_y - 2_y)^2 = (3_x - 4_x)^2 + (3_y - 4_y)^2>>;
       "is_midpoint", (** Point 1 is the midpoint of line (2,3) **)
       <<2 * 1_x = 2_x + 3_x /\ 2 * 1_y = 2_y + 3_y>>;
       "is_intersection", (** Lines (2,3) and (4,5) meet at point 1 **)
       <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x) /\
         (1_x - 4_x) * (4_y - 5_y) = (1_y - 4_y) * (4_x - 5_x)>>;
       "=", (** Points 1 and 2 are the same **)
       <<(1_x = 2_x) /\ (1_y = 2_y)>>]
       *)
    // TEMP : Just to get things working in F#
    let coordinations = []

    (* ------------------------------------------------------------------------- *)
    (* Convert formula into coordinate form.                                     *)
    (* ------------------------------------------------------------------------- *)

    let coordinate = onatoms <| fun (R (a, args)) ->
        let xtms,ytms = List.unzip (List.map (fun (Var v) -> Var (v + "_x"), Var (v + "_y")) args)
        let rec xs = List.map (fun n -> string n + "_x") (1 -- List.length args)
        and ys = List.map (fun n -> string n + "_y") (1 -- List.length args)
        subst (fpf (xs @ ys) (xtms @ ytms)) (assoc a coordinations)

    (* ------------------------------------------------------------------------- *)
    (* Trivial example.                                                          *)
    (* ------------------------------------------------------------------------- *)

    #if INTERACTIVE
    coordinate <<collinear(a,b,c) ==> collinear(b,a,c)>>
    #endif

    (* ------------------------------------------------------------------------- *)
    (* Verify equivalence under rotation.                                        *)
    (* ------------------------------------------------------------------------- *)

    let invariant (x', y') (s : string, z) =
        let m n f =
            let rec x = string n + "_x"
            and y = string n + "_y"
            let i = fpf ["x";"y"] [Var x;Var y]
            (x |-> tsubst i x') ((y |-> tsubst i y') f)
        Iff (z,subst (itlist m (1 -- 5) undefined) z)
    (*
    let invariant_under_translation = invariant (<<|x + X|>>,<<|y + Y|>>)
    *)
    #if INTERACTIVE
    forall (grobner_decide >>|> invariant_under_translation) coordinations
    #endif
    (*
    let invariant_under_rotation fm =
      Imp(<<s^2 + c^2 = 1>>,
          invariant (<<|c * x - s * y|>>,<<|s * x + c * y|>>) fm);;
    *)
    #if INTERACTIVE
    forall (grobner_decide >>|> invariant_under_rotation) coordinations;;
    #endif

    (* ------------------------------------------------------------------------- *)
    (* And show we can always invent such a transformation to zero a y:          *)
    (* ------------------------------------------------------------------------- *)

    #if INTERACTIVE
    real_qelim
     <<forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0>>;;
    #endif

    (* ------------------------------------------------------------------------- *)
    (* Choose one point to be the origin and rotate to zero another y coordinate *)
    (* ------------------------------------------------------------------------- *)

    let originate fm =
        let a :: b :: ovs = fv fm
        subst (fpf [a + "_x"; a + "_y"; b + "_y"] [zero; zero; zero]) (coordinate fm)

    (* ------------------------------------------------------------------------- *)
    (* Other interesting invariances.                                            *)
    (* ------------------------------------------------------------------------- *)
    (*
    let invariant_under_scaling fm =
      Imp(<<~(A = 0)>>,invariant(<<|A * x|>>,<<|A * y|>>) fm);;

    let invariant_under_shearing = invariant(<<|x + b * y|>>,<<|y|>>);;
    *)
    #if INTERACTIVE
    forall (grobner_decide >>|> invariant_under_scaling) coordinations;;

    partition (grobner_decide >>|> invariant_under_shearing) coordinations;;
    #endif

    (* ------------------------------------------------------------------------- *)
    (* One from "Algorithms for Computer Algebra"                                *)
    (* ------------------------------------------------------------------------- *)

    #if INTERACTIVE
    (grobner_decide >>|> originate)
     <<is_midpoint(m,a,c) /\ perpendicular(a,c,m,b)
       ==> lengths_eq(a,b,b,c)>>;;

    (* ------------------------------------------------------------------------- *)
    (* Parallelogram theorem (Chou's expository example at the start).           *)
    (* ------------------------------------------------------------------------- *)

    (grobner_decide >>|> originate)
     <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
       is_intersection(e,a,c,b,d)
       ==> lengths_eq(a,e,e,c)>>;;

    (grobner_decide >>|> originate)
     <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
       is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
       ==> lengths_eq(a,e,e,c)>>;;
    #endif

    (* ------------------------------------------------------------------------- *)
    (* Reduce p using triangular set, collecting degenerate conditions.          *)
    (* ------------------------------------------------------------------------- *)

    let rec pprove vars triang p degens =
      if p = zero then degens
      else
          match triang with
          | [] -> (mk_eq p zero) :: degens
          | (Fn ("+", [c; Fn ("*", [Var x; _])]) as q) :: qs ->
                if x <> hd vars then
                    if mem (hd vars) (fvt p) then
                        itlist (pprove vars triang) (coefficients vars p) degens
                    else
                        pprove (List.tail vars) triang p degens
                else
                    let k, p' = pdivide vars p q
                    if k = 0 then pprove vars qs p' degens
                    else
                        let degens' = Not (mk_eq (head vars q) zero) :: degens
                        itlist (pprove vars qs) (coefficients vars p') degens'

    (* ------------------------------------------------------------------------- *)
    (* Triangulate a set of polynomials.                                         *)
    (* ------------------------------------------------------------------------- *)

    let rec triangulate vars consts pols =
        if vars = [] then pols else
        let cns, tpols = List.partition (is_constant vars) pols
        if cns <> [] then triangulate vars (cns @ consts) tpols else
        if List.length pols <= 1 then pols @ triangulate (List.tail vars) [] consts else
        let n = end_itlist min (List.map (degree vars) pols)
        let p = List.find (fun p -> degree vars p = n) pols
        let ps = subtract pols [p]
        triangulate vars consts (p :: List.map (fun q -> snd (pdivide vars q p)) ps)

    (* ------------------------------------------------------------------------- *)
    (* Trivial version of Wu's method based on repeated pseudo-division.         *)
    (* ------------------------------------------------------------------------- *)

    let wu fm vars zeros =
        let gfm0 = coordinate fm
        let gfm = subst(itlist (fun v -> v |-> zero) zeros undefined) gfm0
        if not (set_eq vars (fv gfm)) then
            failwith "wu: bad parameters" else
        let ant, con = dest_imp gfm
        let rec pols = List.map (lhs >>|> polyatom vars) (conjuncts ant)
        and ps = List.map (lhs >>|> polyatom vars) (conjuncts con)
        let tri = triangulate vars [] pols
        itlist (fun p -> union (pprove vars tri p [])) ps []

    (* ------------------------------------------------------------------------- *)
    (* Simson's theorem.                                                         *)
    (* ------------------------------------------------------------------------- *)

    #if INTERACTIVE
    let simson =
     <<lengths_eq(o,a,o,b) /\
       lengths_eq(o,a,o,c) /\
       lengths_eq(o,a,o,d) /\
       collinear(e,b,c) /\
       collinear(f,a,c) /\
       collinear(g,a,b) /\
       perpendicular(b,c,d,e) /\
       perpendicular(a,c,d,f) /\
       perpendicular(a,b,d,g)
       ==> collinear(e,f,g)>>;;

    let vars =
     ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";
      "b_y"; "b_x"; "o_x"]
    and zeros = ["a_x"; "a_y"; "o_y"];;

    wu simson vars zeros;;

    (* ------------------------------------------------------------------------- *)
    (* Try without special coordinates.                                          *)
    (* ------------------------------------------------------------------------- *)

    wu simson (vars @ zeros) [];;

    (* ------------------------------------------------------------------------- *)
    (* Pappus (Chou's figure 6).                                                 *)
    (* ------------------------------------------------------------------------- *)

    let pappus =
     <<collinear(a1,b2,d) /\
       collinear(a2,b1,d) /\
       collinear(a2,b3,e) /\
       collinear(a3,b2,e) /\
       collinear(a1,b3,f) /\
       collinear(a3,b1,f)
       ==> collinear(d,e,f)>>;;

    let vars = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x";
                "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"]
    and zeros = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"];;

    wu pappus vars zeros;;

    (* ------------------------------------------------------------------------- *)
    (* The Butterfly (figure 9).                                                 *)
    (* ------------------------------------------------------------------------- *)

    (****
    let butterfly =
     <<lengths_eq(b,o,a,o) /\ lengths_eq(c,o,a,o) /\ lengths_eq(d,o,a,o) /\
       collinear(a,e,c) /\ collinear(d,e,b) /\
       perpendicular(e,f,o,e) /\
       collinear(a,f,d) /\ collinear(f,e,g) /\ collinear(b,c,g)
       ==> is_midpoint(e,f,g)>>;;

    let vars = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "c_y";
                "b_y"; "d_x"; "c_x"; "b_x"; "a_x"]
    and zeros = ["a_y"; "o_x"; "o_y"];;

     **** This one is costly (too big for laptop, but doable in about 300M)
     **** However, it gives exactly the same degenerate conditions as Chou

    wu butterfly vars zeros;;

     ****
     ****)
    #endif

    (*** Other examples removed from text

    (* ------------------------------------------------------------------------- *)
    (* Centroid (Chou, example 142).                                             *)
    (* ------------------------------------------------------------------------- *)

    (grobner_decide ** originate)
     <<is_midpoint(d,b,c) /\ is_midpoint(e,a,c) /\
       is_midpoint(f,a,b) /\ is_intersection(m,b,e,a,d)
       ==> collinear(c,f,m)>>;;

    ****)
