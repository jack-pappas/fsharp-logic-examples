// IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
// By downloading, copying, installing or using the software you agree
// to this license.  If you do not agree to this license, do not
// download, install, copy or use the software.
// 
// Copyright (c) 2003-2007, John Harrison
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of John Harrison may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
// USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.
//
// ===================================================================
//
// Converted to F# 2.0
//
// Copyright (c) 2012, Eric Taucher
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the previous disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the previous disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of Eric Taucher may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
//
// ===================================================================

namespace Reasoning.Automated.Harrison.Handbook

open LanguagePrimitives

module cooper =
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
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

    // OCaml: val zero : term = <<|0|>>
    let zero = Fn ("0",[])

// pg.338
// ------------------------------------------------------------------------- //
// Lift operations up to numerals.                                           //
// ------------------------------------------------------------------------- //

    // TODO: is (string n) faster or more accurate then (n.ToString()) ?
  
    // OCaml: val mk_numeral : num -> term = <fun>
    // F#:    val mk_numeral : num -> term
    let mk_numeral (n : num) =
        Fn (n.ToString(), [])

    // Convert a term to a F# BigIntenger, i.e. OCaml Num
    // OCaml: val dest_numeral : term -> num        = <fun>
    // F#:    val dest_numeral : term -> num
    let dest_numeral t : num =
        match t with
        | Fn (ns, []) ->
            num_of_string ns
        | _ ->
            failwith "dest_numeral"

    // OCaml: val is_numeral :  term -> bool = <fun>
    // F#:    val is_numeral : (term -> bool)
    let is_numeral = can dest_numeral

    // OCaml: val numeral1 : (num -> num) -> term -> term = <fun>
    // F#:    val numeral1 : (num -> num) -> term -> term
    let numeral1 fn n =
        mk_numeral (fn (dest_numeral n))

    // OCaml: val numeral2 : (num -> num -> num) -> term -> term -> term = <fun>
    // F#:    val numeral2 : (num -> num -> num) -> term -> term -> term
    let numeral2 fn m n =
        mk_numeral (fn (dest_numeral m) (dest_numeral n))

// pg.338
// ------------------------------------------------------------------------- //
// Operations on canonical linear terms c1 * x1 + ... + cn * xn + k          //
//                                                                           //
// Note that we're quite strict: the ci must be present even if 1            //
// (but if 0 we expect that variable to be omitted) and k must be there      //
// even if it's zero. Thus, it's a constant iff not an addition term.        //
// ------------------------------------------------------------------------- //

    // OCaml: val linear_cmul : num        -> term -> term = <fun>
    // F#:    val linear_cmul : num        -> term -> term
    let rec linear_cmul (n : num) tm =
        if n = GenericZero then zero
        else
            match tm with
            | Fn ("+", [Fn ("*", [c; x]); r]) ->
                Fn ("+", [Fn("*", [numeral1 ((*) n) c; x]); linear_cmul n r])
            | k -> numeral1 ((*) n) k

    // OCaml: val linear_add : string list -> term -> term -> term = <fun>
    // F#:    val linear_add : string list -> term -> term -> term
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

    // OCaml: val linear_neg : term -> term = <fun>
    // F#:    val linear_neg : term -> term 
    let linear_neg tm = linear_cmul -GenericOne tm

    // OCaml: val linear_sub : string list -> term -> term -> term = <fun>
    // F#:    val linear_sub : string list -> term -> term -> term
    let linear_sub vars tm1 tm2 = linear_add vars tm1 (linear_neg tm2)

    // OCaml: val linear_mul : term -> term -> term = <fun>
    // F#:    val linear_mul : term -> term -> term
    let linear_mul tm1 tm2 =
        if is_numeral tm1 then linear_cmul (dest_numeral tm1) tm2
        elif is_numeral tm2 then linear_cmul (dest_numeral tm2) tm1
        else failwith "linear_mul: nonlinearity"
  
// pg.340
// ------------------------------------------------------------------------- //
// Linearize a term.                                                         //
// ------------------------------------------------------------------------- //

    // OCaml: val lint : string list -> term -> term = <fun>
    // F#:    val lint : string list -> term -> term
    let rec lint vars tm =
        match tm with
        | Var _ ->
            Fn ("+", [Fn ("*", [Fn ("1", []); tm]); zero])
        | Fn ("~", [t]) ->
            linear_neg (lint vars t)
        | Fn ("+", [s; t]) ->
            linear_add vars (lint vars s) (lint vars t)
        | Fn ("-", [s; t]) ->
            linear_sub vars (lint vars s) (lint vars t)
        | Fn ("*", [s; t]) ->
            linear_mul (lint vars s) (lint vars t)
        | _ ->
            if is_numeral tm then tm 
            else failwith "lint: unknown term"
  
// pg.340
// ------------------------------------------------------------------------- //
// Linearize the atoms in a formula, and eliminate non-strict inequalities.  //
// ------------------------------------------------------------------------- //

    // OCaml: val mkatom : string list -> string -> term -> fol formula
    // F#:    val mkatom : string list -> string -> term -> fol formula
    let mkatom vars p t =
        Atom (R (p, [zero; lint vars t]))

    // OCaml: val linform : string list -> fol formula -> fol formula = <fun>
    // F#:    val linform : string list -> fol formula -> fol formula
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
    
    // OCaml: val posineq : fol formula -> fol formula = <fun>
    // F#:    val posineq : fol formula -> fol formula
    let rec posineq fm =
        match fm with
        | Not (Atom (R ("<", [Fn ("0", []); t]))) ->
            Atom (R ("<", [zero; linear_sub [] (Fn ("1", [])) t]))
        | _ -> fm
  
// pg.342
// ------------------------------------------------------------------------- //
// Find the LCM of the coefficients of x.                                    //
// ------------------------------------------------------------------------- //

    // OCaml: val formlcm : term -> fol formula -> num        = <fun>
    // F#:    val formlcm : term -> fol formula -> num
    let rec formlcm x fm : num =
        match fm with
        | Atom (R (p, [_; Fn ("+", [Fn ("*", [c; y]); z])]))
            when y = x ->
            abs (dest_numeral c)
        | Not p ->
            formlcm x p
        | And (p, q)
        | Or (p, q) ->
            lcm_num (formlcm x p) (formlcm x q)
        | _ ->
            GenericOne
  
// pg.342
// ------------------------------------------------------------------------- //
// Adjust all coefficients of x in formula; fold in reduction to +/- 1.      //
// ------------------------------------------------------------------------- //

    // OCaml: val adjustcoeff : term -> num        -> fol formula -> fol formula = <fun>
    // F#:    val adjustcoeff : term -> num        -> fol formula -> fol formula
    let rec adjustcoeff x l fm =
        match fm with
        | Atom (R (p, [d; Fn ("+", [Fn ("*", [c; y]); z])]))
            when y = x ->
            let m = l / dest_numeral c
            let n = if p = "<" then abs m else m
            let xtm = Fn ("*", [mk_numeral (m / n); x])
            Atom (R (p, [linear_cmul (abs m) d; Fn ("+", [xtm; linear_cmul n z])]))
        | Not p ->
            Not (adjustcoeff x l p)
        | And (p, q) ->
            And (adjustcoeff x l p, adjustcoeff x l q)
        | Or (p, q) ->
            Or (adjustcoeff x l p, adjustcoeff x l q)
        | _ -> fm
  
// pg.343
// ------------------------------------------------------------------------- //
// Hence make coefficient of x one in existential formula.                   //
// ------------------------------------------------------------------------- //

    // OCaml: val unitycoeff : term -> fol formula -> fol formula = <fun>
    // F#:    val unitycoeff : term -> fol formula -> fol formula
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

    // OCaml: val minusinf : term -> fol formula -> fol formula = <fun>
    // F#:    val minusinf : term -> fol formula -> fol formula
    let rec minusinf x fm =
        match fm with
        | Atom (R ("=", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])]))
            when y = x ->
            False
        | Atom (R ("<", [Fn ("0", []); Fn ("+", [Fn ("*", [pm1; y]); a])]))
            when y = x ->
            if pm1 = Fn ("1", []) then False else True
        | Not p ->
            Not (minusinf x p)
        | And (p, q) ->
            And (minusinf x p, minusinf x q)
        | Or (p, q) ->
            Or (minusinf x p, minusinf x q)
        | _ -> fm
  
// pg.344
// ------------------------------------------------------------------------- //
// The LCM of all the divisors that involve x.                               //
// ------------------------------------------------------------------------- //

    // OCaml: val divlcm : term -> fol formula -> num        = <fun>
    // F#:    val divlcm : term -> fol formula -> num
    let rec divlcm x fm : num =
        match fm with
        | Atom (R ("divides", [d; Fn ("+", [Fn ("*", [c; y]); a])]))
            when y = x ->
            dest_numeral d
        | Not p ->
            divlcm x p
        | And (p, q)
        | Or (p, q) ->
            lcm_num (divlcm x p) (divlcm x q)
        | _ ->
            GenericOne
  
// pg.346
// ------------------------------------------------------------------------- //
// Construct the B-set.                                                      //
// ------------------------------------------------------------------------- //

    // OCaml: val bset : term -> fol formula -> term list = <fun>
    // F#:    val bset : term -> fol formula -> term list
    let rec bset x fm =
        match fm with
        | Not (Atom (R ("=", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])])))
            when y = x ->
            [linear_neg a]
        | Atom (R ("=", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])]))
            when y = x ->
            [linear_neg (linear_add [] a (Fn ("1", [])))]
        | Atom (R ("<", [Fn ("0", []); Fn ("+", [Fn ("*", [Fn ("1", []); y]); a])]))
            when y = x ->
            [linear_neg a]
        | Not p ->
            bset x p
        | And (p, q) ->
            union (bset x p) (bset x q)
        | Or (p, q) ->
            union (bset x p) (bset x q)
        | _ -> []
  
// pg.347
// ------------------------------------------------------------------------- //
// Replace top variable with another linear form, retaining canonicality.    //
// ------------------------------------------------------------------------- //

    // OCaml: val linrep : string list -> term -> term -> fol formula -> fol formula = <fun>
    // F#:    val linrep : string list -> term -> term -> fol formula -> fol formula
    let rec linrep vars x t fm =
        match fm with
        | Atom (R (p, [d; Fn ("+", [Fn ("*", [c; y]); a])]))
            when y = x ->
            let ct = linear_cmul (dest_numeral c) t
            Atom (R (p, [d; linear_add vars ct a]))
        | Not p ->
            Not (linrep vars x t p)
        | And (p, q) ->
            And (linrep vars x t p, linrep vars x t q)
        | Or (p, q) ->
            Or (linrep vars x t p, linrep vars x t q)
        | _ -> fm
  
// pg.348
// ------------------------------------------------------------------------- //
// Hence the core quantifier elimination procedure.                          //
// ------------------------------------------------------------------------- //

    // OCaml: val cooper : string list -> fol formula -> fol formula = <fun>
    // F#:    val cooper : string list -> fol formula -> fol formula
    let cooper vars fm =
        match fm with
        | Exists (x0, p0) ->
            let x = Var x0
            let p = unitycoeff x p0
            let p_inf = simplify (minusinf x p) 
            let bs = bset x p
            let js = GenericOne --- divlcm x p
            let p_element j b = linrep vars x (linear_add vars b (mk_numeral j)) p
            let stage j = list_disj (linrep vars x (mk_numeral j) p_inf :: List.map (p_element j) bs)
            let fol_list = List.map stage js
            list_disj fol_list
        | _ -> failwith "cooper: not an existential formula"
  
// pg.347
// ------------------------------------------------------------------------- //
// Evaluation of constant expressions.                                       //
// ------------------------------------------------------------------------- //

    // OCaml: val operations : (string * (num        -> num        -> bool)) list = [("=", <fun>);                ("<", <fun>);                  (">", <fun>);                  ("<=", <fun>);                  (">=", <fun>);                  ("divides", <fun>)]
    // F#:    val operations : (string * (num        -> num        -> bool)) list = [("=", <fun:operations@401>); ("<", <fun:operations@402-1>); (">", <fun:operations@403-2>); ("<=", <fun:operations@404-3>); (">=", <fun:operations@405-4>); ("divides", <fun:operations@406-5>)]
    let operations = ["=", (=);
                      "<", (<); 
                      ">", (>);
                      "<=", (<=);
                      ">=", (>=);
                      "divides", divides'; ]

//    // OCaml: val evalc : fol formula -> fol formula = <fun>
//    // F#:    val evalc : (fol formula -> fol formula)
//    let evalc = 
//        onatoms (fun (R(p,[s;t]) as at) ->
//            try 
//              if assoc p operations (dest_numeral s) (dest_numeral t)
//              then True 
//              else False
//            with 
//            | Failure _ -> Atom at)

    // OCaml: val evalc : fol formula -> fol formula = <fun>
    // F#:    val evalc : (fol formula -> fol formula)
    let evalc = 
        let v1 = (fun (R(p,[s;t]) as at) ->
            try 
              if assoc p operations (dest_numeral s) (dest_numeral t)
              then True 
              else False
            with 
            | Failure _ -> Atom at)
        onatoms v1
         
// pg.349
// ------------------------------------------------------------------------- //
// Overall function.                                                         //
// ------------------------------------------------------------------------- //

    // OCaml: val integer_qelim : fol formula -> fol formula = <fun>
    // F#:    val integer_qelim : (fol formula -> fol formula)
    let integer_qelim = 
        simplify >>|> evalc >>|>
        lift_qelim linform (cnnf posineq >>|> evalc) cooper

// pg.350
// ------------------------------------------------------------------------- //
// Natural number version.                                                   //
// ------------------------------------------------------------------------- //

    // F#: val relativize : (string -> 'a formula) -> 'a formula -> 'a formula
    let rec relativize r fm =
        match fm with
        | Not p ->
            Not (relativize r p)
        | And (p, q) ->
            And (relativize r p, relativize r q)
        | Or (p, q) ->
            Or(relativize r p, relativize r q)
        | Imp (p, q) ->
            Imp (relativize r p, relativize r q)
        | Iff (p, q) ->
            Iff (relativize r p, relativize r q)
        | Forall (x, p) ->
            Forall (x, Imp (r x, relativize r p))
        | Exists (x, p) ->
            Exists (x, And (r x, relativize r p))
        | _ -> fm

    // F#: val natural_qelim : (fol formula -> fol formula)
    let natural_qelim =
        integer_qelim >>|> relativize (fun x -> Atom (R ("<=", [zero; Var x])))