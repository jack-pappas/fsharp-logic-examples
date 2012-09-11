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

module formulas =

    open EGT.OCaml.Format

    open lib
//    open intro

// pg. 26
// ========================================================================= //
// Polymorphic type of formulas with parser and printer.                     //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

    type ('a)formula = 
        | False
        | True
        | Atom   of 'a
        | Not    of ('a)formula
        | And    of ('a)formula * ('a)formula
        | Or     of ('a)formula * ('a)formula
        | Imp    of ('a)formula * ('a)formula
        | Iff    of ('a)formula * ('a)formula
        | Forall of string * ('a)formula
        | Exists of string * ('a)formula

// pg. 623
// ------------------------------------------------------------------------- //
// General parsing of iterated infixes.                                      //
// ------------------------------------------------------------------------- //

    // OCaml: val parse_ginfix : 'a -> (('b -> 'c) -> 'b -> 'b -> 'c) -> ('b -> 'c) -> ('a list -> 'b * 'a list) -> 'a list -> 'c * 'a list = <fun>
    // F#:    val parse_ginfix : 'a -> (('b -> 'c) -> 'b -> 'b -> 'c) -> ('b -> 'c) -> ('a list -> 'b * 'a list) -> 'a list -> 'c * 'a list when 'a : equality
    let rec parse_ginfix opsym opupdate sof subparser inp =
        let e1,inp1 = subparser inp
        if (inp1 <> []) && (List.head inp1 = opsym) then parse_ginfix opsym opupdate (opupdate sof e1) subparser (List.tail inp1)
        else sof e1,inp1

    // OCaml: val parse_left_infix : 'a -> ('b * 'b -> 'b) ->  ('a list -> 'b * 'a list) -> 'a list -> 'b * 'a list = <fun>
    // F#:    val parse_left_infix : 'a -> ('b * 'b -> 'b) -> (('a list -> 'b * 'a list) -> 'a list -> 'b * 'a list) when 'a : equality
    let parse_left_infix opsym opcon =
        parse_ginfix opsym (fun f e1 e2 -> opcon(f e1,e2)) (fun x -> x)

    // OCaml: val parse_right_infix : 'a -> ('b * 'b -> 'b) ->  ('a list -> 'b * 'a list) -> 'a list -> 'b * 'a list = <fun>
    // F#:    val parse_right_infix : 'a -> ('b * 'b -> 'b) -> (('a list -> 'b * 'a list) -> 'a list -> 'b * 'a list) when 'a : equality
    let parse_right_infix opsym opcon =
        parse_ginfix opsym (fun f e1 e2 -> f(opcon(e1,e2))) (fun x -> x)

    // OCaml: val parse_list : 'a ->  ('a list -> 'b * 'a list) -> 'a list -> 'b list * 'a list = <fun>
    // F#:    val parse_list : 'a -> (('a list -> 'b * 'a list) -> 'a list -> 'b list * 'a list)  when 'a : equality
    let parse_list opsym =
        parse_ginfix opsym (fun f e1 e2 -> (f e1)@[e2]) (fun x -> [x])

// pg. 624
// ------------------------------------------------------------------------- //
// Other general parsing combinators.                                        //
// ------------------------------------------------------------------------- //

    // OCaml: val papply : ('a -> 'b) -> 'a * 'c -> 'b * 'c = <fun>
    // F#:    val papply : ('a -> 'b) -> 'a * 'c -> 'b * 'c
    let papply f (ast,rest) = 
        (f ast,rest)

    // OCaml: val nextin : 'a list -> 'a -> bool = <fun>
    // F#:    val nextin : 'a list -> 'a -> bool when 'a : equality
    let nextin inp tok = 
        (inp <> []) && (List.head inp = tok)

    // OCaml: val parse_bracketed : ('a -> 'b * 'c list) -> 'c -> 'a -> 'b * 'c list = <fun>
    // F#:    val parse_bracketed : ('a -> 'b * 'c list) -> 'c -> 'a -> 'b * 'c list when 'c : equality
    let parse_bracketed subparser cbra inp =
        let ast,rest = subparser inp
        if nextin rest cbra then ast,List.tail rest
        else failwith "Closing bracket expected"

// pg. 625
// ------------------------------------------------------------------------- //
// Parsing of formulas, parametrized by atom parser "pfn".                   //
// ------------------------------------------------------------------------- //

    // OCaml: val parse_atomic_formula : (string list -> string list -> 'a formula * string list) * (string list -> string list -> 'a formula * string list) -> string list -> string list -> 'a formula * string list = <fun>
    // F#:    val parse_atomic_formula : (string list -> string list -> 'a formula * string list) * (string list -> string list -> 'a formula * string list) -> string list -> string list -> 'a formula * string list
    let rec parse_atomic_formula (ifn,afn) vs inp =
        match inp with
        | []                                    -> failwith "formula expected"
        | "false"::rest                         -> False,rest
        | "true"::rest                          -> True,rest
        | "("::rest -> 
            (try ifn vs inp with Failure _      -> parse_bracketed (parse_formula (ifn,afn) vs) ")" rest)
        | "~"::rest                             -> papply (fun p -> Not p) (parse_atomic_formula (ifn,afn) vs rest)
        | "forall"::x::rest                     -> parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Forall(x,p)) x rest
        | "exists"::x::rest                     -> parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Exists(x,p)) x rest
        | _                                     -> afn vs inp

    // OCaml: val parse_quant : (string list -> string list -> 'a formula * string list) * (string list -> string list -> 'a formula * string list) -> string list -> (string * 'a formula -> 'a formula) -> string -> string list -> 'a formula * string list = <fun>
    // F#:    val parse_quant : (string list -> string list -> 'a formula * string list) * (string list -> string list -> 'a formula * string list) -> string list -> (string * 'a formula -> 'a formula) -> string -> string list -> 'a formula * string list
    and parse_quant (ifn,afn) vs qcon x inp =
        match inp with
        | []      -> failwith "Body of quantified term expected"
        | y::rest -> papply (fun fm -> qcon(x,fm)) (if y = "." then parse_formula (ifn,afn) vs rest else parse_quant (ifn,afn) (y::vs) qcon y rest)

    // OCaml: val parse_formula : (string list -> string list -> 'a formula * string list) * (string list -> string list -> 'a formula * string list) -> string list -> string list -> 'a formula * string list = <fun>
    // F#:    val parse_formula : (string list -> string list -> 'a formula * string list) * (string list -> string list -> 'a formula * string list) -> string list -> string list -> 'a formula * string list
    and parse_formula (ifn,afn) vs inp =
        parse_right_infix "<=>" (fun (p,q) -> Iff(p,q))
            (parse_right_infix "==>" (fun (p,q) -> Imp(p,q))
                (parse_right_infix "\\/" (fun (p,q) -> Or(p,q))
                    (parse_right_infix "/\\" (fun (p,q) -> And(p,q))
                        (parse_atomic_formula (ifn,afn) vs)))) inp

// pg. 626
// ------------------------------------------------------------------------- //
// Printing of formulas, parametrized by atom printer.                       //
// ------------------------------------------------------------------------- //

    // OCaml: val bracket : bool -> int -> ('a -> 'b -> 'c) -> 'a -> 'b -> unit = <fun>
    // F#:    val bracket : bool -> 'a -> ('b -> 'c -> unit) -> 'b -> 'c -> unit
    // Note: No use of OCaml format module. i.e. print_box removed during conversion
//    let bracket p n f x y =
//        (if p then printf "(" else ())
//        f x y
//        (if p then printf ")" else ())

    let bracket p n f x y =
      (if p then print_string "(" else ());
      open_box n; f x y; close_box();
      (if p then print_string ")" else ())

    // OCaml: val strip_quant : 'a formula -> string list * 'a formula = <fun>
    // F#:    val strip_quant : 'a formula -> string list * 'a formula
    let rec strip_quant fm =
        match fm with
        | Forall(x,(Forall(y,p) as yp)) | Exists(x,(Exists(y,p) as yp)) -> let xs,q = strip_quant yp in x::xs,q
        | Forall(x,p) | Exists(x,p)                                     -> [x],p
        | _                                                             -> [],fm
        
    // OCaml: val print_formula : (int -> 'a -> unit) -> 'a formula -> unit = <fun>
    // F#:    val print_formula : (int -> 'a -> unit) -> ('a formula -> unit)
    // Note: No use of OCaml format module. i.e. print_box removed during conversion
//    let print_formula pfn =
//        let rec print_formula pr fm =
//            match fm with
//            | False -> printf "%s" "false"
//            | True -> printf "%s" "true"
//            | Atom(pargs) -> pfn pr pargs
//            | Not(p) -> bracket (pr > 10) 1 (print_prefix 10) "~" p
//            | And(p,q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
//            | Or(p,q) ->  bracket (pr > 6) 0 (print_infix  6 "\\/") p q
//            | Imp(p,q) ->  bracket (pr > 4) 0 (print_infix 4 "==>") p q
//            | Iff(p,q) ->  bracket (pr > 2) 0 (print_infix 2 "<=>") p q
//            | Forall(x,p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
//            | Exists(x,p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
//        and print_qnt qname (bvs,bod) =
//            printf "%s" qname
//            do_list (fun v -> printf " "; printf "%s" v) bvs
//            printf "%s" ". "
////            print_space()
////            open_box 0
//            print_formula 0 bod
////            close_box()
//        and print_prefix newpr sym p =
//            printf "%s" sym
//            print_formula (newpr+1) p
//        and print_infix newpr sym p q =
//            print_formula (newpr+1) p
//            printf "%s" (" " + sym + " ")
////            print_space()
//            print_formula newpr q
//        print_formula 0

    let print_formula pfn =
      let rec print_formula pr fm =
        match fm with
        | False       -> print_string "false"
        | True        -> print_string "true"
        | Atom(pargs) -> pfn pr pargs
        | Not(p)      -> bracket (pr > 10) 1 (print_prefix 10) "~" p
        | And(p,q)    -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
        | Or(p,q)     ->  bracket (pr > 6) 0 (print_infix  6 "\\/") p q
        | Imp(p,q)    ->  bracket (pr > 4) 0 (print_infix 4 "==>") p q
        | Iff(p,q)    ->  bracket (pr > 2) 0 (print_infix 2 "<=>") p q
        | Forall(x,p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
        | Exists(x,p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
      and print_qnt qname (bvs,bod) =
        print_string qname;
        do_list (fun v -> print_string " "; print_string v) bvs;
        print_string "."; print_space(); open_box 0;
        print_formula 0 bod;
        close_box()
      and print_prefix newpr sym p =
       print_string sym; print_formula (newpr+1) p
      and print_infix newpr sym p q =
        print_formula (newpr+1) p;
        print_string(" " + sym); print_space();
        print_formula newpr q in
      print_formula 0

    // OCaml: val print_qformula : (int -> 'a -> unit) -> 'a formula -> unit = <fun>
    // F#:    val print_qformula : (int -> 'a -> unit) -> 'a formula -> unit
    // Note: No use of OCaml format module. i.e. print_box removed during conversion
    // pg. 28
//    let print_qformula pfn fm =
//        printf "<<"
//        print_formula pfn fm
//        printfn ">>"

    let print_qformula pfn fm =
      open_box 0; print_string "<<";
      open_box 0; print_formula pfn fm; close_box();
      print_string ">>"; close_box()

// pg.30
// ------------------------------------------------------------------------- //
// OCaml won't let us use the constructors.                                  //
// ------------------------------------------------------------------------- //

    // OCaml: val mk_and : 'a formula -> 'a formula -> 'a formula = <fun>
    // F#:    val mk_and : 'a formula -> 'a formula -> 'a formula
    let mk_and p q    = And(p,q) 

    // OCaml: val mk_or : 'a formula -> 'a formula -> 'a formula = <fun>
    // F#:    val mk_or : 'a formula -> 'a formula -> 'a formula
    let mk_or p q     = Or(p,q)

    // OCaml: val mk_imp : 'a formula -> 'a formula -> 'a formula = <fun>
    // F#:    val mk_imp : 'a formula -> 'a formula -> 'a formula
    let mk_imp p q    = Imp(p,q) 

    // OCaml: val mk_iff : 'a formula -> 'a formula -> 'a formula = <fun>
    // F#:    val mk_iff : 'a formula -> 'a formula -> 'a formula
    let mk_iff p q    = Iff(p,q)

    // OCaml: val mk_forall : string -> 'a formula -> 'a formula = <fun>
    // F#:    val mk_forall : string -> 'a formula -> 'a formula
    let mk_forall x p = Forall(x,p) 

    // OCaml: val mk_exists : string -> 'a formula -> 'a formula = <fun>
    // F#:    val mk_exists : string -> 'a formula -> 'a formula
    let mk_exists x p = Exists(x,p)

// pg. 30
// ------------------------------------------------------------------------- //
// Destructors.                                                              //
// ------------------------------------------------------------------------- //

    // OCaml: val dest_iff : 'a formula -> 'a formula * 'a formula = <fun>
    // F#:    val dest_iff : 'a formula -> 'a formula * 'a formula
    let dest_iff fm =
        match fm with 
        | Iff(p,q) -> (p,q) 
        | _        -> failwith "dest_iff"

    // OCaml: val dest_and : 'a formula -> 'a formula * 'a formula = <fun>
    // F#:    val dest_and : 'a formula -> 'a formula * 'a formula
    let dest_and fm =
        match fm with 
        | And(p,q) -> (p,q) 
        | _        -> failwith "dest_and"

    // OCaml: val conjuncts : 'a formula -> 'a formula list = <fun>
    // F#:    val conjuncts : 'a formula -> 'a formula list
    let rec conjuncts fm =
        match fm with 
        | And(p,q) -> conjuncts p @ conjuncts q 
        | _        -> [fm]

    // OCaml: val dest_or : 'a formula -> 'a formula * 'a formula = <fun>
    // F#:    val dest_or : 'a formula -> 'a formula * 'a formula
    let dest_or fm =
        match fm with 
        | Or(p,q) -> (p,q) 
        | _       -> failwith "dest_or"

    // OCaml: val disjuncts : 'a formula -> 'a formula list = <fun>
    // F#:    val disjuncts : 'a formula -> 'a formula list
    let rec disjuncts fm =
        match fm with 
        | Or(p,q) -> disjuncts p @ disjuncts q 
        | _       -> [fm]

    // OCaml: val dest_imp : 'a formula -> 'a formula * 'a formula = <fun>
    // F#:    val dest_imp : 'a formula -> 'a formula * 'a formula
    let dest_imp fm =
        match fm with 
        | Imp(p,q) -> (p,q) 
        | _        -> failwith "dest_imp"

    // OCaml: val antecedent : 'a formula -> 'a formula = <fun>
    // F#:    val antecedent : 'a formula -> 'a formula
    let antecedent fm = fst(dest_imp fm)

    // OCaml: val consequent : 'a formula -> 'a formula = <fun>
    // F#:    val consequent : 'a formula -> 'a formula
    let consequent fm = snd(dest_imp fm)

// pg. 31
// ------------------------------------------------------------------------- //
// Apply a function to the atoms, otherwise keeping structure.               //
// ------------------------------------------------------------------------- //

    // OCaml: val onatoms : ('a -> 'a formula) -> 'a formula -> 'a formula = <fun>
    // F#:    val onatoms : ('a -> 'a formula) -> 'a formula -> 'a formula
    let rec onatoms f fm =
        match fm with
        | Atom a      -> f a
        | Not(p)      -> Not(onatoms f p)
        | And(p,q)    -> And(onatoms f p,onatoms f q)
        | Or(p,q)     -> Or(onatoms f p,onatoms f q)
        | Imp(p,q)    -> Imp(onatoms f p,onatoms f q)
        | Iff(p,q)    -> Iff(onatoms f p,onatoms f q)
        | Forall(x,p) -> Forall(x,onatoms f p)
        | Exists(x,p) -> Exists(x,onatoms f p)
        | _           -> fm

// pg. 31
// ------------------------------------------------------------------------- //
// Formula analog of list iterator "itlist".                                 //
// ------------------------------------------------------------------------- //

    // OCaml: val overatoms : ('a -> 'b -> 'b) -> 'a formula -> 'b -> 'b = <fun>
    // F#:    val overatoms : ('a -> 'b -> 'b) -> 'a formula -> 'b -> 'b
    let rec overatoms f fm b =
        match fm with
        | Atom(a)                                  -> f a b
        | Not(p)                                   -> overatoms f p b
        | And(p,q) | Or(p,q) | Imp(p,q) | Iff(p,q) -> overatoms f p (overatoms f q b)
        | Forall(x,p) | Exists(x,p)                -> overatoms f p b
        | _                                        -> b

// pg. 32
// ------------------------------------------------------------------------- //
// Special case of a union of the results of a function over the atoms.      //
// ------------------------------------------------------------------------- //

    // OCaml: val atom_union : ('a -> 'b list) -> 'a formula -> 'b list = <fun>
    // F#:    val atom_union : ('a -> 'b list) -> 'a formula -> 'b list when 'b : comparison
    let atom_union f fm = setify (overatoms (fun h t -> f(h)@t) fm [])


    

