// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.cooper

open LanguagePrimitives
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

// pg. 337
// ========================================================================= //
// Cooper's algorithm for Presburger arithmetic.                             //
// ========================================================================= //

let zero = Fn ("0",[])

// pg.338
// ------------------------------------------------------------------------- //
// Lift operations up to numerals.                                           //
// ------------------------------------------------------------------------- //

let mk_numeral (n : num) =
    Fn (n.ToString(), [])

let dest_numeral = function
    | Fn (ns, []) ->
        num_of_string ns
    | _ ->
        failwith "dest_numeral"

let inline is_numeral tm =
    can dest_numeral tm

let numeral1 fn n =
    fn (dest_numeral n)
    |> mk_numeral

let numeral2 fn m n =
    fn (dest_numeral m) (dest_numeral n)
    |> mk_numeral

// pg.338
// ------------------------------------------------------------------------- //
// Operations on canonical linear terms c1 * x1 + ... + cn * xn + k          //
//                                                                           //
// Note that we're quite strict: the ci must be present even if 1            //
// (but if 0 we expect that variable to be omitted) and k must be there      //
// even if it's zero. Thus, it's a constant iff not an addition term.        //
// ------------------------------------------------------------------------- //

// OPTIMIZE : Optimize functions with CPS.
let rec linear_cmul (n : num) tm =
    if n = GenericZero then zero
    else
        match tm with
        | Fn ("+", [Fn ("*", [c; x]); r]) ->
            Fn ("+", [Fn("*", [numeral1 ((*) n) c; x]); linear_cmul n r])
        | k -> numeral1 ((*) n) k

let rec linear_add vars tm1 tm2 =
    match tm1, tm2 with
    | Fn ("+", [Fn ("*", [c1; Var x1]); r1]), Fn ("+", [Fn ("*", [c2; Var x2]); r2]) ->
        if x1 = x2 then
            let c = numeral2 (+) c1 c2
            if c = zero then
                linear_add vars r1 r2
            else
                Fn ("+", [Fn ("*", [c; Var x1]); linear_add vars r1 r2])
        elif earlier vars x1 x2 then
            Fn ("+", [Fn ("*", [c1; Var x1]); linear_add vars r1 tm2])
        else
            Fn ("+", [Fn ("*", [c2; Var x2]); linear_add vars tm1 r2])

    | Fn ("+", [Fn ("*", [c1; Var x1]); r1]), k2 ->
        Fn ("+", [Fn ("*", [c1; Var x1]); linear_add vars r1 k2])
    | k1, Fn ("+", [Fn ("*", [c2; Var x2]); r2]) ->
        Fn ("+", [Fn ("*", [c2; Var x2]); linear_add vars k1 r2])
    | _ ->
        numeral2 (+) tm1 tm2

let inline linear_neg tm =
    linear_cmul -GenericOne tm

let inline linear_sub vars tm1 tm2 =
    linear_neg tm2
    |> linear_add vars tm1

let linear_mul tm1 tm2 =
    if is_numeral tm1 then
        linear_cmul (dest_numeral tm1) tm2
    elif is_numeral tm2 then
        linear_cmul (dest_numeral tm2) tm1
    else
        failwith "linear_mul: nonlinearity"
  
// pg.340
// ------------------------------------------------------------------------- //
// Linearize a term.                                                         //
// ------------------------------------------------------------------------- //

let rec private lintImpl vars tm cont =
    match tm with
    | Var _ ->
        Fn ("+", [Fn ("*", [Fn ("1", []); tm]); zero])
        |> cont
    | Fn ("~", [t]) ->
        lintImpl vars t <| fun lint_t ->
            cont (linear_neg lint_t)
    | Fn ("+", [s; t]) ->
        lintImpl vars s <| fun lint_s ->
        lintImpl vars t <| fun lint_t ->
            cont (linear_add vars lint_s lint_t)
    | Fn ("-", [s; t]) ->
        lintImpl vars s <| fun lint_s ->
        lintImpl vars t <| fun lint_t ->
            cont (linear_sub vars lint_s lint_t)
    | Fn ("*", [s; t]) ->
        lintImpl vars s <| fun lint_s ->
        lintImpl vars t <| fun lint_t ->
            cont (linear_mul lint_s lint_t)
    | tm ->
        if is_numeral tm then
            cont tm 
        else
            failwith "lintImpl: unknown term"

let lint vars tm =
    lintImpl vars tm id
  
// pg.340
// ------------------------------------------------------------------------- //
// Linearize the atoms in a formula, and eliminate non-strict inequalities.  //
// ------------------------------------------------------------------------- //

let mkatom vars p t =
    Atom (R (p, [zero; lint vars t]))

let linform vars fm =
    match fm with
    | Atom (R ("divides", [c; t])) ->
        Atom (R ("divides", [numeral1 abs c; lint vars t]))
    | Atom (R ("=", [s; t])) ->
        mkatom vars "=" (Fn ("-", [t; s]))
    | Atom (R ("<", [s; t])) ->
        mkatom vars "<" (Fn ("-", [t; s]))
    | Atom (R (">", [s; t])) ->
        mkatom vars "<" (Fn ("-", [s; t]))
    | Atom (R ("<=", [s; t])) ->
        mkatom vars "<" (Fn ("-", [Fn ("+", [t; Fn ("1", [])]); s]))
    | Atom (R (">=", [s; t])) ->
        mkatom vars "<" (Fn ("-", [Fn ("+", [s; Fn ("1", [])]); t]))
    | _ -> fm
  
// pg.341
// ------------------------------------------------------------------------- //
// Post-NNF transformation eliminating negated inequalities.                 //
// ------------------------------------------------------------------------- //
    
let posineq = function
    | Not (Atom (R ("<", [Fn ("0", []); t]))) ->
        Atom (R ("<", [zero; linear_sub [] (Fn ("1", [])) t]))
    | fm ->
        fm
  
// pg.342
// ------------------------------------------------------------------------- //
// Find the LCM of the coefficients of x.                                    //
// ------------------------------------------------------------------------- //

let rec private formlcmImpl x fm cont =
    match fm with
    | Atom (R (p, [_; Fn ("+", [Fn ("*", [c; y]); z])]))
        when y = x ->
        cont (abs (dest_numeral c))
    | Not p ->
        formlcmImpl x p cont
    | And (p, q)
    | Or (p, q) ->
        formlcmImpl x p <| fun lcm_p ->
        formlcmImpl x q <| fun lcm_q ->
            cont (lcm_num lcm_p lcm_q)
    | _ ->
        cont GenericOne

let formlcm x fm : num =
    formlcmImpl x fm id
  
// pg.342
// ------------------------------------------------------------------------- //
// Adjust all coefficients of x in formula; fold in reduction to +/- 1.      //
// ------------------------------------------------------------------------- //

let rec private adjustcoeffImpl x l fm cont =
    match fm with
    | Atom (R (p, [d; Fn ("+", [Fn ("*", [c; y]); z])]))
        when y = x ->
        let m = l / dest_numeral c
        let n = if p = "<" then abs m else m
        let xtm = Fn ("*", [mk_numeral (m / n); x])
        Atom (R (p, [linear_cmul (abs m) d; Fn ("+", [xtm; linear_cmul n z])]))
        |> cont
    | Not p ->
        adjustcoeffImpl x l p <| fun adjusted_p ->
            cont (Not adjusted_p)
    | And (p, q) ->
        adjustcoeffImpl x l p <| fun adjusted_p ->
        adjustcoeffImpl x l q <| fun adjusted_q ->
            And (adjusted_p, adjusted_q)
            |> cont
    | Or (p, q) ->
        adjustcoeffImpl x l p <| fun adjusted_p ->
        adjustcoeffImpl x l q <| fun adjusted_q ->
            Or (adjusted_p, adjusted_q)
            |> cont
    | _ ->
        cont fm

let adjustcoeff x l fm =
    adjustcoeffImpl x l fm id
  
// pg.343
// ------------------------------------------------------------------------- //
// Hence make coefficient of x one in existential formula.                   //
// ------------------------------------------------------------------------- //

let unitycoeff x fm =
    let l = formlcm x fm
    let fm' = adjustcoeff x l fm
    if l = GenericOne then fm'
    else
        let xp = Fn ("+", [Fn ("*", [Fn ("1", []); x]); zero])
        And (Atom (R ("divides", [mk_numeral l; xp])), adjustcoeff x l fm)
  
// pg.344
// ------------------------------------------------------------------------- //
// The "minus infinity" version.                                             //
// ------------------------------------------------------------------------- //

let rec private minusinfImpl x fm cont =
    match fm with
    | Atom (R ("=", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])]))
        when y = x ->
        cont False
    | Atom (R ("<", [Fn ("0", []); Fn ("+", [Fn ("*", [pm1; y]); a])]))
        when y = x ->
        if pm1 = Fn ("1", []) then False else True
        |> cont
    | Not p ->
        minusinfImpl x p <| fun minusinf_p ->
            cont (Not minusinf_p)
    | And (p, q) ->
        minusinfImpl x p <| fun minusinf_p ->
        minusinfImpl x q <| fun minusinf_q ->
            And (minusinf_p, minusinf_q)
            |> cont
    | Or (p, q) ->
        minusinfImpl x p <| fun minusinf_p ->
        minusinfImpl x q <| fun minusinf_q ->
            Or (minusinf_p, minusinf_q)
            |> cont
    | _ ->
        cont fm

let minusinf x fm =
    minusinfImpl x fm id
  
// pg.344
// ------------------------------------------------------------------------- //
// The LCM of all the divisors that involve x.                               //
// ------------------------------------------------------------------------- //

let rec private divlcmImpl x fm cont =
    match fm with
    | Atom (R ("divides", [d; Fn ("+", [Fn ("*", [c; y]); a])]))
        when y = x ->
        cont (dest_numeral d)
    | Not p ->
        divlcmImpl x p cont
    | And (p, q)
    | Or (p, q) ->
        divlcmImpl x p <| fun divlcm_p ->
        divlcmImpl x q <| fun divlcm_q ->
            cont (lcm_num divlcm_p divlcm_q)
    | _ ->
        cont GenericOne

let divlcm x fm =
    divlcmImpl x fm id
  
// pg.346
// ------------------------------------------------------------------------- //
// Construct the B-set.                                                      //
// ------------------------------------------------------------------------- //

let rec private bsetImpl x fm cont =
    // TODO : Merge the first and third cases?
    match fm with
    | Not (Atom (R ("=", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])])))
        when y = x ->
        cont [linear_neg a]
    | Atom (R ("=", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])]))
        when y = x ->
        cont [linear_neg (linear_add [] a (Fn ("1", [])))]
    | Atom (R ("<", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])]))
        when y = x ->
        cont [linear_neg a]
    | Not p ->
        bsetImpl x p cont
    | And (p, q)
    | Or (p, q) ->
        bsetImpl x p <| fun bset_p ->
        bsetImpl x q <| fun bset_q ->
            union bset_p bset_q
            |> cont
    | _ ->
        cont []

let bset x fm =
    bsetImpl x fm id
  
// pg.347
// ------------------------------------------------------------------------- //
// Replace top variable with another linear form, retaining canonicality.    //
// ------------------------------------------------------------------------- //

let rec private linrepImpl vars x t fm cont =
    match fm with
    | Atom (R (p, [d; Fn ("+", [Fn ("*", [c; y]); a])]))
        when y = x ->
        let ct = linear_cmul (dest_numeral c) t
        Atom (R (p, [d; linear_add vars ct a]))
        |> cont
    | Not p ->
        linrepImpl vars x t p <| fun linrep_p ->
            cont (Not linrep_p)
    | And (p, q) ->
        linrepImpl vars x t p <| fun linrep_p ->
        linrepImpl vars x t q <| fun linrep_q ->
            And (linrep_p, linrep_q)
            |> cont
    | Or (p, q) ->
        linrepImpl vars x t p <| fun linrep_p ->
        linrepImpl vars x t q <| fun linrep_q ->
            Or (linrep_p, linrep_q)
            |> cont
    | fm ->
        cont fm

let linrep vars x t fm =
    linrepImpl vars x t fm id
  
// pg.348
// ------------------------------------------------------------------------- //
// Hence the core quantifier elimination procedure.                          //
// ------------------------------------------------------------------------- //

let cooper vars fm =
    match fm with
    | Exists (x0, p0) ->
        let x = Var x0
        let p = unitycoeff x p0
            
        let p_element j b = linrep vars x (linear_add vars b (mk_numeral j)) p

        let bs = bset x p
        let stage j =
            let p_inf = simplify004 (minusinf x p)
            list_disj (linrep vars x (mk_numeral j) p_inf :: List.map (p_element j) bs)

        // OPTIMIZE : Implement a special version of List.init which uses
        // 'num' instead of 'int'. Then, use it to replace this call to List.map.
        [GenericOne .. divlcm x p]
        |> List.map stage
        |> list_disj

    | _ ->
        failwith "cooper: not an existential formula"
  
// pg.347
// ------------------------------------------------------------------------- //
// Evaluation of constant expressions.                                       //
// ------------------------------------------------------------------------- //

let operations = ["=", (=);
                    "<", (<); 
                    ">", (>);
                    "<=", (<=);
                    ">=", (>=);
                    "divides", (fun x y -> y % x = GenericZero); ]

let evalc = 
    let v1 = (fun (R(p,[s;t]) as at) ->
        try 
            if assoc p operations (dest_numeral s) (dest_numeral t)
            then True 
            else False
        with Failure _ ->
            Atom at)
    onatoms v1
         
// pg.349
// ------------------------------------------------------------------------- //
// Overall function.                                                         //
// ------------------------------------------------------------------------- //

let integer_qelim = 
    simplify004
    << evalc
    << lift_qelim linform (cnnf posineq << evalc) cooper

// pg.350
// ------------------------------------------------------------------------- //
// Natural number version.                                                   //
// ------------------------------------------------------------------------- //

let rec private relativizeImpl r fm cont =
    match fm with
    | Not p ->
        relativizeImpl r p <| fun rel_p ->
            cont (Not rel_p)
    | And (p, q) ->
        relativizeImpl r p <| fun rel_p ->
        relativizeImpl r q <| fun rel_q ->
            And (rel_p, rel_q)
            |> cont
    | Or (p, q) ->
        relativizeImpl r p <| fun rel_p ->
        relativizeImpl r q <| fun rel_q ->
            Or (rel_p, rel_q)
            |> cont
    | Imp (p, q) ->
        relativizeImpl r p <| fun rel_p ->
        relativizeImpl r q <| fun rel_q ->
            Imp (rel_p, rel_q)
            |> cont
    | Iff (p, q) ->
        relativizeImpl r p <| fun rel_p ->
        relativizeImpl r q <| fun rel_q ->
            Iff (rel_p, rel_q)
            |> cont
    | Forall (x, p) ->
        relativizeImpl r p <| fun rel_p ->
            Forall (x, Imp (r x, rel_p))
            |> cont
    | Exists (x, p) ->
        relativizeImpl r p <| fun rel_p ->
            Exists (x, And (r x, rel_p))
            |> cont
    | fm ->
        cont fm

let relativize r fm =
    relativizeImpl r fm id

let natural_qelim =
    integer_qelim
    << relativize (fun x ->
        Atom (R ("<=", [zero; Var x])))