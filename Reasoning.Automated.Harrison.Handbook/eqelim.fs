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

module eqelim =
    open formulas
    open prop
    open folMod
    open skolem
    open tableaux
    open meson
    open equal

// ========================================================================= //
// Equality elimination including Brand transformation and relatives.        //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

// pg.291
// ------------------------------------------------------------------------- //
// Brand's S and T modifications on clauses.                                 //
// ------------------------------------------------------------------------- //

    // val modify_S : fol formula list -> fol formula list list
    let rec modify_S cl =
          // val dest_eq : fol formula -> (term * term) option
          let dest_eq fm =
            match fm with
            | Atom(R("=",[s;t])) -> Some(s,t)
            | _                  -> None
          // val tryfind : ('a -> ('b * 'c) option) -> 'a list -> ('b * 'c) option
          let rec tryfind dest_eq l =
              match l with
              | []            -> None
              | (h::t) -> 
                  match dest_eq h with
                  | Some(s,t) -> Some(s,t)
                  | None      -> tryfind dest_eq t
          match tryfind dest_eq cl with
          | Some(s,t) -> 
              let eq1 = mk_eq s t 
              let eq2 = mk_eq t s
              let sub = modify_S (subtract cl [eq1])
              List.map (insert eq1) sub @ List.map (insert eq2) sub
          | None -> [cl]

    let rec modify_T cl =
      match cl with
      | (Atom(R("=",[s;t])) as eq)::ps ->
            let ps' = modify_T ps
            let w = Var(variant "w" (itlist (union ** fv) ps' (fv eq)))
            Not(mk_eq t w)::(mk_eq s w)::ps'
      | p::ps -> p::(modify_T ps)
      | [] -> []


// pg. 294
// ------------------------------------------------------------------------- //
// Finding nested non-variable subterms.                                     //
// ------------------------------------------------------------------------- //

    // val is_nonvar : term -> bool
    let is_nonvar = 
        function 
        | (Var x) -> false 
        | _       -> true

    // val find_nvsubterm : fol formula -> term option
    let rec find_nvsubterm fm =
      let rec find p l =
        match l with
        | [] -> None
        | (h::t) -> 
            if p(h) then Some(h) 
            else find p t
      match fm with
      | Atom(R("=",[s;t])) -> 
          let find_nestnonvar tm =
            match tm with
            | Var x      -> None
            | Fn(f,args) -> 
              match find is_nonvar args with
              | Some(x) -> Some(x)
              | None    -> None
          let rec tryfind f l =
            match l with
            | []     -> None
            | (h::t) -> 
                match f h with 
                | Some(x) -> Some(x)
                | None -> tryfind f t
          tryfind find_nestnonvar [s;t]
      | Atom(R(p,args)) -> 
          match find is_nonvar args with
          | Some(x) -> Some(x)
          | None    -> None
      | Not p       -> find_nvsubterm p
//      | False       -> failwith "How did we get here"
//      | True        -> failwith "How did we get here"
//      | And(_,_)    -> failwith "How did we get here"
//      | Or(_,_)     -> failwith "How did we get here"
//      | Imp(_,_)    -> failwith "How did we get here"
//      | Iff(_,_)    -> failwith "How did we get here"
//      | Forall(_,_) -> failwith "How did we get here"
//      | Exists(_,_) -> failwith "How did we get here"
      | _ -> failwith "How did we get here"

// pg. 295
// ------------------------------------------------------------------------- //
// Replacement (substitution for non-variable) in term and literal.          //
// ------------------------------------------------------------------------- //

    // OCaml: val replacet : (term, term) func      -> term -> term = <fun>
    // F# 1:  val replacet : func<term,term>        -> term -> term
    // F# 2:  val replacet : func<term,term option> -> term -> term
    let rec replacet rfn tm =
      match apply_none rfn tm with
      | Some(x) -> x 
      | None ->
          match tm with
          | Fn(f,args) -> Fn(f,List.map (replacet rfn) args)
          | _          -> tm

    let replace rfn = onformula (replacet rfn)

// pg. 295
// ------------------------------------------------------------------------- //
// E-modification of a clause.                                               //
// ------------------------------------------------------------------------- //

    let rec emodify fvs cls =
      let t_option =
        let rec tryfind f l =
            match l with
            | []     -> None
            | (h::t) -> 
              match f h with 
              | Some(x) -> Some(x)
              | None -> 
                  tryfind f t
        tryfind find_nvsubterm cls
      match t_option with
      | Some(t) -> 
          let w = variant "w" fvs
          let cls' = List.map (replace (t |=> Some(Var w))) cls
          emodify (w::fvs) (Not(mk_eq t (Var w))::cls')
      | None -> cls

    let modify_E cls = emodify (itlist (union ** fv) cls []) cls

// pg. 296
// ------------------------------------------------------------------------- //
// Overall Brand transformation.                                             //
// ------------------------------------------------------------------------- //

    let brand cls =
      let cls1 = List.map modify_E cls
      let cls2 = itlist (union ** modify_S) cls1 []
      [mk_eq (Var "x") (Var "x")]::(List.map modify_T cls2)

// pg. 296
// ------------------------------------------------------------------------- //
// Incorporation into MESON.                                                 //
// ------------------------------------------------------------------------- //

    let bpuremeson fm =
      let cls = brand(simpcnf(specialize(pnf fm)))
      let rules = itlist ((@) ** contrapositives) cls []
      deepen (fun n ->
         mexpand002 rules [] False (fun x -> x) (undefined,n,0) |> ignore;  n) 0

    let bmeson fm =
      let fm1 = askolemize(Not(generalize fm))
      List.map (bpuremeson ** list_conj) (simpdnf fm1)

    // Moved from section - Older stuff not now in the text
    // to here because it is still in the text.  EGT
    let emeson fm = meson002 (equalitize fm)



