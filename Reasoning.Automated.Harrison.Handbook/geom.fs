// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

//  ========================================================================= // 
//  Geometry theorem proving.                                                 // 
//  ========================================================================= // 

module Reasoning.Automated.Harrison.Handbook.geom

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

// pg. 415
//  ------------------------------------------------------------------------- // 
//  List of geometric properties with their coordinate translations.          // 
//  ------------------------------------------------------------------------- // 

let coordinations =
    ["collinear", // * Points 1, 2 and 3 lie on a common line *// 
        (parse "(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x)");
        "parallel", // * Lines (1,2) and (3,4) are parallel *// 
        (parse "(1_x - 2_x) * (3_y - 4_y) = (1_y - 2_y) * (3_x - 4_x)");
        "perpendicular", // * Lines (1,2) and (3,4) are perpendicular *// 
        (parse "(1_x - 2_x) * (3_x - 4_x) + (1_y - 2_y) * (3_y - 4_y) = 0");
        "lengths_eq", // * Lines (1,2) and (3,4) have the same length *// 
        (parse "(1_x - 2_x)^2 + (1_y - 2_y)^2 = (3_x - 4_x)^2 + (3_y - 4_y)^2");
        "is_midpoint", // * Point 1 is the midpoint of line (2,3) *// 
        (parse "2 * 1_x = 2_x + 3_x /\ 2 * 1_y = 2_y + 3_y");
        "is_intersection", // * Lines (2,3) and (4,5) meet at point 1 *// 
        (parse "(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x) /\ (1_x - 4_x) * (4_y - 5_y) = (1_y - 4_y) * (4_x - 5_x)");
        "=", // * Points 1 and 2 are the same *// 
        (parse "(1_x = 2_x) /\ (1_y = 2_y)")]
    
// pg. 415
//  ------------------------------------------------------------------------- // 
//  Convert formula into coordinate form.                                     // 
//  ------------------------------------------------------------------------- // 

// OCaml: val coordinate : fol formula -> fol formula = <fun>
// F#:    val coordinate : (formula<fol> -> formula<fol>)
let coordinate = onatoms <| fun (R (a, args)) ->
    let xtms,ytms = List.unzip (List.map (fun (Var v) -> Var (v + "_x"), Var (v + "_y")) args)
    let rec xs = List.map (fun n -> string n + "_x") (1 -- List.length args)
    and ys = List.map (fun n -> string n + "_y") (1 -- List.length args)
    subst (fpf (xs @ ys) (xtms @ ytms)) (assoc a coordinations)
    
// pg. 415
//  ------------------------------------------------------------------------- // 
//  Verify equivalence under rotation.                                        // 
//  ------------------------------------------------------------------------- // 

// OCaml: val invariant : term * term -> string * fol formula -> fol formula = <fun>
// F#:    val invariant : term * term -> string * formula<fol> -> formula<fol>
let invariant (x', y') (s : string, z) =
    let m n f =
        let rec x = string n + "_x"
        and y = string n + "_y"
        let i = fpf ["x";"y"] [Var x;Var y]
        (x |-> tsubst i x') ((y |-> tsubst i y') f)
    Iff (z,subst (List.foldBack m (1 -- 5) undefined) z)

// OCaml: val invariant_under_translation : string * fol formula -> fol formula = <fun>
// F#:    val invariant_under_translation : (string * formula<fol> -> formula<fol>)
let invariant_under_translation = invariant ((parset "x + X"),(parset "y + Y"))

// OCaml: val invariant_under_rotation : string * fol formula -> fol formula = <fun>
// F#:    val invariant_under_rotation : string * formula<fol> -> formula<fol>
let invariant_under_rotation fm =
    Imp((parse "s^2 + c^2 = 1"),
        invariant ((parset "c * x - s * y"),(parset "s * x + c * y")) fm)
    
// pg. 416
//  ------------------------------------------------------------------------- // 
//  Choose one point to be the origin and rotate to zero another y coordinate // 
//  ------------------------------------------------------------------------- // 

// OCaml: val originate : fol formula -> fol formula = <fun>
// F#:    val originate : formula<fol> -> formula<fol>
let originate fm =
    let a :: b :: ovs = fv fm
    subst (fpf [a + "_x"; a + "_y"; b + "_y"] [zero; zero; zero]) (coordinate fm)
        
// pg. 417
//  ------------------------------------------------------------------------- // 
//  Other interesting invariances.                                            // 
//  ------------------------------------------------------------------------- // 

let invariant_under_scaling fm =
    Imp((parse "~(A = 0)"),invariant((parset "A * x"),(parset "A * y")) fm)

// OCaml: val invariant_under_shearing : string * fol formula -> fol formula = <fun>
// F#:    val invariant_under_shearing : (string * formula<fol> -> formula<fol>)
let invariant_under_shearing = invariant((parset "x + b * y"),(parset "y"))
    
// pg. 421
//  ------------------------------------------------------------------------- // 
//  Reduce p using triangular set, collecting degenerate conditions.          // 
//  ------------------------------------------------------------------------- // 

// OCaml : val pprove : string list -> term list -> term -> fol formula list  -> fol formula list = <fun>
// F#:     val pprove : string list -> term list -> term -> formula<fol> list -> formula<fol> list
let rec pprove vars triang p degens =
    if p = zero then degens
    else
        match triang with
        | [] -> (mk_eq p zero) :: degens
        | (Fn ("+", [c; Fn ("*", [Var x; _])]) as q) :: qs ->
            if x <> List.head vars then
                if mem (List.head vars) (fvt p) then
                    List.foldBack (pprove vars triang) (coefficients vars p) degens
                else
                    pprove (List.tail vars) triang p degens
            else
                let k, p' = pdivide vars p q
                if k = 0 then pprove vars qs p' degens
                else
                    let degens' = Not (mk_eq (head vars q) zero) :: degens
                    List.foldBack (pprove vars qs) (coefficients vars p') degens'
                        
// pg. 421
//  ------------------------------------------------------------------------- // 
//  Triangulate a set of polynomials.                                         // 
//  ------------------------------------------------------------------------- // 

// OCaml: val triangulate : string list -> term list -> term list -> term list =  <fun>
// F#:    val triangulate : string list -> term list -> term list -> term list
let rec triangulate vars consts pols =
    if vars = [] then pols else
    let cns, tpols = List.partition (is_constant vars) pols
    if cns <> [] then triangulate vars (cns @ consts) tpols else
    if List.length pols <= 1 then pols @ triangulate (List.tail vars) [] consts else
    let n = end_itlist min (List.map (degree vars) pols)
    let p = List.find (fun p -> degree vars p = n) pols
    let ps = subtract pols [p]
    triangulate vars consts (p :: List.map (fun q -> snd (pdivide vars q p)) ps)
        
// pg. 421
//  ------------------------------------------------------------------------- // 
//  Trivial version of Wu's method based on repeated pseudo-division.         // 
//  ------------------------------------------------------------------------- // 

// OCaml: val wu : fol formula -> string list -> string list -> fol formula list = <fun>
// F#:    val wu : formula<fol> -> string list -> string list -> formula<fol> list
let wu fm vars zeros =
    let gfm0 = coordinate fm
    let gfm = subst(List.foldBack (fun v -> v |-> zero) zeros undefined) gfm0
    if not (set_eq vars (fv gfm)) then failwith "wu: bad parameters" else
    let ant, con = dest_imp gfm
    let pols = List.map (lhs << polyatom vars) (conjuncts ant)
    let ps = List.map (lhs << polyatom vars) (conjuncts con)
    let tri = triangulate vars [] pols
    List.foldBack (fun p -> union (pprove vars tri p [])) ps []