// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Jack Pappas, Eric Taucher                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// Nelson-Oppen combined decision procedure.                                 //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.combining

open FSharpx.Compatibility.OCaml.Num

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

// pg. 436
// ------------------------------------------------------------------------- //
// Real language with decision procedure.                                    //
// ------------------------------------------------------------------------- //

let real_lang =
    let rec fn = ["-", 1; "+", 2; "-", 2; "*", 2; "^", 2]
    and pr = ["<=", 2; "<", 2; ">=", 2; ">", 2]
    (fun (s,n) -> n = 0 && is_numeral (Fn (s, [])) || mem (s,n) fn),
    (fun sn -> mem sn pr),
    (fun fm -> real_qelim (generalize fm) = True)
        
// pg. 436
// ------------------------------------------------------------------------- //
// Integer language with decision procedure.                                 //
// ------------------------------------------------------------------------- //

let int_lang =
    let rec fn = ["-", 1; "+", 2; "-", 2; "*", 2]
    and pr = ["<=", 2; "<", 2; ">=", 2; ">", 2]
    (fun (s,n) -> n = 0 && is_numeral (Fn (s, [])) || mem (s,n) fn),
    (fun sn -> mem sn pr),
    (fun fm -> integer_qelim (generalize fm) = True)
        
// pg. 436
// ------------------------------------------------------------------------- //
// Add any uninterpreted functions to a list of languages.                   //
// ------------------------------------------------------------------------- //

let add_default langs =
    langs @ [(fun sn -> not (List.exists (fun (f, p, d) -> f sn) langs)),
                (fun sn -> sn = ("=", 2)), ccvalid]
                    
// pg. 437
// ------------------------------------------------------------------------- //
// Choose a language for homogenization of an atom.                          //
// ------------------------------------------------------------------------- //

let chooselang langs fm =
    match fm with
    | Atom (R ("=", [Fn (f, args); _]))
    | Atom (R ("=", [_; Fn (f, args)])) ->
        List.find (fun (fn, pr, dp) -> fn (f, List.length args)) langs
    | Atom (R (p, args)) ->
        List.find (fun (fn, pr, dp) -> pr (p, List.length args)) langs
            
// pg. 437
// ------------------------------------------------------------------------- //
// General listification for CPS-style function.                             //
// ------------------------------------------------------------------------- //

let rec listify f l cont =
    match l with
    | [] -> cont []
    | h :: t ->
        f h (fun h' -> listify f t (fun t' -> cont (h' :: t')))
            
// pg. 438
// ------------------------------------------------------------------------- //
// Homogenize a term.                                                        //
// ------------------------------------------------------------------------- //

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
                        
// pg. 438
// ------------------------------------------------------------------------- //
// Homogenize a literal.                                                     //
// ------------------------------------------------------------------------- //

let rec homol langs fm cont n defs =
    match fm with
    | Not f ->
        homol langs f (fun p -> cont (Not p)) n defs
    | Atom (R (p, args)) ->
        let lang = chooselang langs fm
        listify (homot lang) args (fun a -> cont (Atom (R (p, a)))) n defs
    | _ -> failwith "homol: not a literal"

        
// pg. 438
// ------------------------------------------------------------------------- //
// Fully homogenize a list of literals.                                      //
// ------------------------------------------------------------------------- //

let rec homo langs fms cont =
    listify (homol langs) fms
    <| fun dun n defs ->
        if defs = [] then cont dun n defs
        else homo langs defs (fun res -> cont (dun @ res)) n []

// pg. 438
// ------------------------------------------------------------------------- //
// Overall homogenization.                                                   //
// ------------------------------------------------------------------------- //

let homogenize langs fms =
    let fvs = unions (List.map fv fms)
    let n = (Int 1) + List.foldBack (max_varindex "v_") fvs (Int 0)
    homo langs fms (fun res n defs -> res) n []

// pg. 439
// ------------------------------------------------------------------------- //
// Whether a formula belongs to a language.                                  //
// ------------------------------------------------------------------------- //

let belongs (fn, pr, dp) fm =
    List.forall fn (functions fm) &&
    List.forall pr (subtract (predicates fm) ["=", 2])
        
// pg. 439
// ------------------------------------------------------------------------- //
// Partition formulas among a list of languages.                             //
// ------------------------------------------------------------------------- //

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
//
    
// pg. 442
// ------------------------------------------------------------------------- //
// Turn an arrangement (partition) of variables into corresponding formula.  //
// ------------------------------------------------------------------------- //

let rec arreq l =
    match l with
    | v1 :: v2 :: rest ->
        mk_eq (Var v1) (Var v2) :: (arreq (v2 :: rest))
    | _ -> []

let arrangement part =
    List.foldBack (union >>|> arreq) part
            (List.map (fun (v, w) -> Not (mk_eq (Var v) (Var w)))
                (distinctpairs (List.map List.head part)))
                  
// pg. 443
// ------------------------------------------------------------------------- //
// Attempt to substitute with trivial equations.                             //
// ------------------------------------------------------------------------- //

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
    match List.tryFind (can dest_def) eqs with
    | None -> eqs
    | Some eq ->
        let x, t = dest_def eq
        redeqs (List.map (subst (x |=> t)) (subtract eqs [eq]))
            
// pg. 443
// ------------------------------------------------------------------------- //
// Naive Nelson-Oppen variant trying all arrangements.                       //
// ------------------------------------------------------------------------- //

let trydps ldseps fms =
    List.exists (fun ((_, _, dp), fms0) ->
        dp (Not (list_conj (redeqs (fms0 @ fms)))))
        ldseps

let allpartitions =
    let allinsertions x l acc =
        List.foldBack (fun p acc -> ((x :: p) :: (subtract l [p])) :: acc) l (([x] :: l) :: acc)
    fun l -> List.foldBack (fun h y -> List.foldBack (allinsertions h) y []) l [[]]

let nelop_refute001 vars ldseps =
    List.forall (trydps ldseps >>|> arrangement) (allpartitions vars)

let nelop1001 langs fms0 =
    let fms = homogenize langs fms0
    let seps = langpartition langs fms
    let fvlist = List.map (unions >>|> List.map fv) seps
    let vars = List.filter (fun x -> List.length (List.filter (mem x) fvlist) >= 2) (unions fvlist)
    nelop_refute001 vars (List.zip langs seps)

let nelop001 langs fm =
    List.forall (nelop1001 langs) (simpdnf (simplify004 (Not fm)))
    
// pg. 445
// ------------------------------------------------------------------------- //
// Find the smallest subset satisfying a predicate.                          //
// ------------------------------------------------------------------------- //

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
            
// pg. 446
// ------------------------------------------------------------------------- //
// The "true" Nelson-Oppen method.                                           //
// ------------------------------------------------------------------------- //

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
    List.forall (nelop1 langs) (simpdnf (simplify004 (Not fm)))
