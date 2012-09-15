
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

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
//open Reasoning.Automated.Harrison.Handbook.formulas
//open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
open Reasoning.Automated.Harrison.Handbook.rewrite
open Reasoning.Automated.Harrison.Handbook.order
open Reasoning.Automated.Harrison.Handbook.completion
  
// pg. 277
// ------------------------------------------------------------------------- //
// Simple example.                                                           //
// ------------------------------------------------------------------------- //

// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",[Fn ("f",[Fn ("g",[Var "x0"])]); Fn ("g",[Fn ("f",[Var "x0"])])]));
//    Atom (R ("=",[Fn ("g",[Var "x1"]); Fn ("g",[Var "x1"])]))]
let eq = (parse "f(f(x)) = g(x)") in critical_pairs eq eq;;
  
// pg. 280
// ------------------------------------------------------------------------- //
// A simple "manual" example, before considering packaging and refinements.  //
// ------------------------------------------------------------------------- //

//val eqs : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//  [Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//   Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
//   Atom
//     (R ("=",
//         [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//          Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
let eqs = [(parse "1 * x = x"); (parse "i(x) * x = 1"); (parse "(x * y) * z = x * y * z")];;

// <<1 *x =x>>
// <<i(x) *x =1>>
// <<(x *y) *z =x *y *z>>
// val it : unit = ()
print_fol_formula_list eqs;;

// val ord : (term -> term -> bool)
let ord = lpo_ge (weight ["1"; "*"; "i"]);;

// 4 equations and 8 pending critical pairs + 0 deferred
// 5 equations and 12 pending critical pairs + 0 deferred
// 6 equations and 16 pending critical pairs + 0 deferred
// 7 equations and 27 pending critical pairs + 0 deferred
// 8 equations and 51 pending critical pairs + 0 deferred
// 9 equations and 70 pending critical pairs + 0 deferred
// 10 equations and 81 pending critical pairs + 0 deferred
// 11 equations and 78 pending critical pairs + 0 deferred
// 12 equations and 85 pending critical pairs + 0 deferred
// 13 equations and 114 pending critical pairs + 0 deferred
// 14 equations and 151 pending critical pairs + 0 deferred
// 15 equations and 180 pending critical pairs + 0 deferred
// 16 equations and 247 pending critical pairs + 0 deferred
// 17 equations and 298 pending critical pairs + 0 deferred
// 18 equations and 356 pending critical pairs + 0 deferred
// 19 equations and 404 pending critical pairs + 0 deferred
// 20 equations and 485 pending critical pairs + 0 deferred
// 21 equations and 530 pending critical pairs + 0 deferred
// 22 equations and 583 pending critical pairs + 0 deferred
// 23 equations and 642 pending critical pairs + 0 deferred
// 24 equations and 730 pending critical pairs + 0 deferred
// 25 equations and 779 pending critical pairs + 0 deferred
// 26 equations and 794 pending critical pairs + 0 deferred
// 27 equations and 819 pending critical pairs + 1 deferred
// 28 equations and 918 pending critical pairs + 1 deferred
// 29 equations and 901 pending critical pairs + 1 deferred
// 30 equations and 1005 pending critical pairs + 1 deferred
// 31 equations and 1086 pending critical pairs + 1 deferred
// 32 equations and 1155 pending critical pairs + 1 deferred
// 32 equations and 1000 pending critical pairs + 1 deferred
// 32 equations and 0 pending critical pairs + 1 deferred
// 32 equations and 0 pending critical pairs + 0 deferred
//
// val eqs' : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
//           Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Var "x1"; Fn ("i",[Fn ("*",[Var "x5"; Var "x1"])])]);
//           Fn ("i",[Var "x5"])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn ("i",[Var "x4"]);
//               Fn ("*",[Var "x1"; Fn ("i",[Fn ("*",[Var "x3"; Var "x1"])])])]);
//           Fn ("*",[Fn ("i",[Var "x4"]); Fn ("i",[Var "x3"])])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Var "x1";
//               Fn
//                 ("i",
//                  [Fn
//                     ("*",
//                      [Fn ("i",[Var "x4"]);
//                       Fn ("*",[Fn ("i",[Var "x3"]); Var "x1"])])])]);
//           Fn ("*",[Var "x3"; Var "x4"])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Fn ("*",[Var "x3"; Var "x5"])]); Var "x0"]);
//           Fn
//             ("*",
//              [Fn ("i",[Var "x5"]); Fn ("*",[Fn ("i",[Var "x3"]); Var "x0"])])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn
//                 ("i",
//                  [Fn
//                     ("*",
//                      [Var "x4";
//                       Fn ("*",[Var "x5"; Fn ("*",[Var "x6"; Var "x3"])])])]);
//               Var "x0"]);
//           Fn
//             ("*",
//              [Fn ("i",[Var "x3"]);
//               Fn
//                 ("*",
//                  [Fn
//                     ("i",[Fn ("*",[Var "x4"; Fn ("*",[Var "x5"; Var "x6"])])]);
//                   Var "x0"])])]));
//    Atom
//      (R ("=",
//          [Fn ("i",[Fn ("*",[Var "x0"; Fn ("i",[Var "x1"])])]);
//           Fn ("*",[Var "x1"; Fn ("i",[Var "x0"])])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("i",
//              [Fn ("*",[Fn ("i",[Fn ("*",[Var "x2"; Var "x1"])]); Var "x2"])]);
//           Var "x1"]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn ("i",[Fn ("*",[Fn ("i",[Var "x4"]); Var "x2"])]); Var "x0"]);
//           Fn ("*",[Fn ("i",[Var "x2"]); Fn ("*",[Var "x4"; Var "x0"])])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Var "x1";
//               Fn ("*",[Fn ("i",[Fn ("*",[Var "x2"; Var "x1"])]); Var "x2"])]);
//           Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Var "x1";
//               Fn
//                 ("*",
//                  [Fn
//                     ("i",
//                      [Fn
//                         ("*",
//                          [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]); Var "x1"])]);
//                   Var "x3"])]);
//           Fn ("*",[Var "x4"; Fn ("*",[Var "x5"; Var "x3"])])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("i",
//              [Fn ("*",[Var "x3"; Fn ("i",[Fn ("*",[Var "x1"; Var "x2"])])])]);
//           Fn ("*",[Var "x1"; Fn ("*",[Var "x2"; Fn ("i",[Var "x3"])])])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn
//                 ("i",
//                  [Fn
//                     ("*",
//                      [Fn
//                         ("i",
//                          [Fn
//                             ("*",
//                              [Var "x3";
//                               Fn ("i",[Fn ("*",[Var "x1"; Var "x2"])])])]);
//                       Fn ("i",[Fn ("*",[Var "x5"; Var "x6"])])])]);
//               Fn ("*",[Var "x1"; Fn ("*",[Var "x2"; Var "x0"])])]);
//           Fn
//             ("*",
//              [Var "x5"; Fn ("*",[Var "x6"; Fn ("*",[Var "x3"; Var "x0"])])])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Var "x1";
//               Fn ("*",[Var "x2"; Fn ("i",[Fn ("*",[Var "x1"; Var "x2"])])])]);
//           Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Var "x2";
//               Fn
//                 ("*",
//                  [Var "x3";
//                   Fn
//                     ("*",[Fn ("i",[Fn ("*",[Var "x2"; Var "x3"])]); Var "x1"])])]);
//           Var "x1"]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn ("i",[Fn ("*",[Var "x3"; Var "x4"])]);
//               Fn ("*",[Var "x3"; Var "x1"])]);
//           Fn ("*",[Fn ("i",[Var "x4"]); Var "x1"])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn ("i",[Fn ("*",[Var "x1"; Fn ("*",[Var "x3"; Var "x4"])])]);
//               Fn
//                 ("*",
//                  [Var "x1"; Fn ("*",[Var "x3"; Fn ("*",[Var "x4"; Var "x0"])])])]);
//           Var "x0"]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn ("i",[Fn ("*",[Var "x1"; Fn ("i",[Var "x3"])])]);
//               Fn ("*",[Var "x1"; Var "x4"])]); Fn ("*",[Var "x3"; Var "x4"])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn
//                 ("i",
//                  [Fn
//                     ("*",[Fn ("i",[Fn ("*",[Var "x5"; Var "x2"])]); Var "x5"])]);
//               Var "x0"]); Fn ("*",[Var "x2"; Var "x0"])]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn
//                 ("i",
//                  [Fn
//                     ("*",[Var "x4"; Fn ("i",[Fn ("*",[Var "x1"; Var "x2"])])])]);
//               Fn ("*",[Var "x4"; Var "x0"])]);
//           Fn ("*",[Var "x1"; Fn ("*",[Var "x2"; Var "x0"])])]));
//    Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
//    Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
//    Atom (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
//           Var "x3"]));
//    Atom
//      (R ("=",
//          [Fn
//             ("*",
//              [Fn ("i",[Fn ("*",[Var "x2"; Var "x3"])]);
//               Fn ("*",[Var "x2"; Fn ("*",[Var "x3"; Var "x1"])])]); Var "x1"]));
//    Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Fn ("1",[])]); Var "x1"]); Var "x1"]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Fn ("i",[Var "x0"])]); Var "x1"]);
//           Fn ("*",[Var "x0"; Var "x1"])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
//           Var "x2"]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//          Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
let eqs' = complete ord (eqs,[],unions(allpairs critical_pairs eqs eqs));;

// <<i(x4 *x5) =i(x5) *i(x4)>>
// <<x1 *i(x5 *x1) =i(x5)>>
// <<i(x4) *x1 *i(x3 *x1) =i(x4) *i(x3)>>
// <<x1 *i(i(x4) *i(x3) *x1) =x3 *x4>>
// <<i(x3 *x5) *x0 =i(x5) *i(x3) *x0>>
// <<i(x4 *x5 *x6 *x3) *x0 =i(x3) *i(x4 *x5 *x6) *x0>>
// <<i(x0 *i(x1)) =x1 *i(x0)>>
// <<i(i(x2 *x1) *x2) =x1>>
// <<i(i(x4) *x2) *x0 =i(x2) *x4 *x0>>
// <<x1 *i(x2 *x1) *x2 =1>>
// <<x1 *i(i(x4 *x5) *x1) *x3 =x4 *x5 *x3>>
// <<i(x3 *i(x1 *x2)) =x1 *x2 *i(x3)>>
// <<i(i(x3 *i(x1 *x2)) *i(x5 *x6)) *x1 *x2 *x0 =x5 *x6 *x3 *x0>>
// <<x1 *x2 *i(x1 *x2) =1>>
// <<x2 *x3 *i(x2 *x3) *x1 =x1>>
// <<i(x3 *x4) *x3 *x1 =i(x4) *x1>>
// <<i(x1 *x3 *x4) *x1 *x3 *x4 *x0 =x0>>
// <<i(x1 *i(x3)) *x1 *x4 =x3 *x4>>
// <<i(i(x5 *x2) *x5) *x0 =x2 *x0>>
// <<i(x4 *i(x1 *x2)) *x4 *x0 =x1 *x2 *x0>>
// <<i(i(x1)) =x1>>
// <<i(1) =1>>
// <<x0 *i(x0) =1>>
// <<x0 *i(x0) *x3 =x3>>
// <<i(x2 *x3) *x2 *x3 *x1 =x1>>
// <<x1 *1 =x1>>
// <<i(1) *x1 =x1>>
// <<i(i(x0)) *x1 =x0 *x1>>
// <<i(x1) *x1 *x2 =x2>>
// <<1 *x =x>>
// <<i(x) *x =1>>
// <<(x *y) *z =x *y *z>>
// val it : unit = ()
print_fol_formula_list eqs';;

// val it : term = Var "z"
rewrite eqs' (parset "i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))");;

// pg. 283
// ------------------------------------------------------------------------- //
// This does indeed help a lot.                                              //
// ------------------------------------------------------------------------- //

// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
//           Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
//    Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
//    Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
//    Atom (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
//           Var "x3"]));
//    Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
//           Var "x2"]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//           Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
interreduce [] eqs';;

// <<i(x4 *x5) =i(x5) *i(x4)>>
// <<i(i(x1)) =x1>>
// <<i(1) =1>>
// <<x0 *i(x0) =1>>
// <<x0 *i(x0) *x3 =x3>>
// <<x1 *1 =x1>>
// <<i(x1) *x1 *x2 =x2>>
// <<1 *x =x>>
// <<i(x) *x =1>>
// <<(x *y) *z =x *y *z>>
// val it : unit = ()
print_fol_formula_list (interreduce [] eqs');;

// K&B - Knuth, D. E. and Bendix, P. (1970) Simple word problems in universal algebras. In Leech. J. (ed.). Computational Problems in Abstract Algebra. Pergamon Press. pg. 263-2987
  
// pg. 284
// ------------------------------------------------------------------------- //
// Inverse property (K&B example 4).                                         //
// ------------------------------------------------------------------------- //

// 2 equations and 4 pending critical pairs + 0 deferred
// 3 equations and 9 pending critical pairs + 0 deferred
// 3 equations and 0 pending critical pairs + 0 deferred
// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
//           Var "x3"]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Fn ("i",[Var "x0"])]); Var "x1"]);
//           Fn ("*",[Var "x0"; Var "x1"])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Var "a"]); Fn ("*",[Var "a"; Var "b"])]); Var "b"]))]
complete_and_simplify ["1"; "*"; "i"] [(parse "i(a) * (a * b) = b")];;
  
// pg. 284
// ------------------------------------------------------------------------- //
// Auxiliary result used to justify extension of language for cancellation.  //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// val it : int list = [5; 4]
(meson002 ** equalitize) (parse "(forall x y z. x * y = x * z ==> y = z) <=> (forall x z. exists w. forall y. z = x * y ==> w = y)");;

// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula =
//   Or
//     (Not (Atom (R ("=",[Var "z"; Fn ("*",[Var "x"; Var "y"])]))),
//      Atom (R ("=",[Fn ("f_w",[Var "x"; Var "z"]); Var "y"])))
skolemize (parse "forall x z. exists w. forall y. z = x * y ==> w = y");;

// <<~z =x *y \/ f_w(x,z) =y>>
// val it : unit = ()
print_fol_formula (skolemize (parse "forall x z. exists w. forall y. z = x * y ==> w = y"));;

// pg.286
// ------------------------------------------------------------------------- //
// Central groupoids (K&B example 6).                                        //
// ------------------------------------------------------------------------- //

let eqs001 =  [(parse "(a * b) * (b * c) = b")];;
complete_and_simplify ["*"] eqs001;;

// 2 equations and 8 pending critical pairs + 0 deferred
// 3 equations and 18 pending critical pairs + 0 deferred
// 3 equations and 0 pending critical pairs + 0 deferred
// <<(x3 *x0 *x1) *x1 =x0 *x1>>
// <<x1 *(x1 *x2) *x5 =x1 *x2>>
// <<(a *b) *b *c =b>>
// val it : unit = ()
print_fol_formula_list (complete_and_simplify ["*"] eqs001);;

// ------------------------------------------------------------------------- //
// (l,r)-systems (K&B example 12).                                           //
// ------------------------------------------------------------------------- //

(******* This works, but takes a long time
// 4 equations and 24 pending critical pairs + 0 deferred
// 5 equations and 30 pending critical pairs + 0 deferred
// 6 equations and 28 pending critical pairs + 0 deferred
// 7 equations and 44 pending critical pairs + 0 deferred
// 8 equations and 71 pending critical pairs + 0 deferred
// 9 equations and 104 pending critical pairs + 0 deferred
// 10 equations and 117 pending critical pairs + 0 deferred
// 11 equations and 141 pending critical pairs + 0 deferred
// 12 equations and 164 pending critical pairs + 0 deferred
// 13 equations and 163 pending critical pairs + 0 deferred
// 14 equations and 186 pending critical pairs + 0 deferred
// 15 equations and 233 pending critical pairs + 0 deferred
// 16 equations and 251 pending critical pairs + 0 deferred
// 17 equations and 314 pending critical pairs + 0 deferred
// 18 equations and 361 pending critical pairs + 0 deferred
// 19 equations and 437 pending critical pairs + 0 deferred
// 20 equations and 538 pending critical pairs + 0 deferred
// 21 equations and 581 pending critical pairs + 0 deferred
// 22 equations and 688 pending critical pairs + 0 deferred
// 23 equations and 797 pending critical pairs + 0 deferred
// 24 equations and 881 pending critical pairs + 0 deferred
// 25 equations and 983 pending critical pairs + 0 deferred
// 26 equations and 1029 pending critical pairs + 0 deferred
// 27 equations and 1116 pending critical pairs + 0 deferred
// 28 equations and 1162 pending critical pairs + 0 deferred
// 29 equations and 1192 pending critical pairs + 0 deferred
// 30 equations and 1294 pending critical pairs + 0 deferred
// 31 equations and 1388 pending critical pairs + 0 deferred
// 32 equations and 1484 pending critical pairs + 0 deferred
// 33 equations and 1528 pending critical pairs + 0 deferred
// 34 equations and 1585 pending critical pairs + 0 deferred
// 35 equations and 1662 pending critical pairs + 0 deferred
// 36 equations and 1738 pending critical pairs + 0 deferred
// 37 equations and 1860 pending critical pairs + 0 deferred
// 38 equations and 1915 pending critical pairs + 0 deferred
// 39 equations and 1949 pending critical pairs + 0 deferred
// 40 equations and 2042 pending critical pairs + 0 deferred
// 41 equations and 2116 pending critical pairs + 0 deferred
// 42 equations and 2256 pending critical pairs + 0 deferred
// 43 equations and 2419 pending critical pairs + 0 deferred
// 44 equations and 2523 pending critical pairs + 0 deferred
// 45 equations and 2656 pending critical pairs + 0 deferred
// 46 equations and 2831 pending critical pairs + 0 deferred
// 47 equations and 3028 pending critical pairs + 0 deferred
// 48 equations and 3191 pending critical pairs + 0 deferred
// 49 equations and 3432 pending critical pairs + 0 deferred
// 50 equations and 3607 pending critical pairs + 0 deferred
// 51 equations and 3783 pending critical pairs + 0 deferred
// 52 equations and 4027 pending critical pairs + 0 deferred
// 53 equations and 4260 pending critical pairs + 0 deferred
// 54 equations and 4474 pending critical pairs + 0 deferred
// 55 equations and 4656 pending critical pairs + 0 deferred
// 56 equations and 4787 pending critical pairs + 0 deferred
// 57 equations and 4889 pending critical pairs + 0 deferred
// 58 equations and 5103 pending critical pairs + 0 deferred
// 59 equations and 5418 pending critical pairs + 0 deferred
// 60 equations and 5658 pending critical pairs + 0 deferred
// 61 equations and 5831 pending critical pairs + 0 deferred
// 62 equations and 6090 pending critical pairs + 0 deferred
// 63 equations and 6450 pending critical pairs + 0 deferred
// 64 equations and 6778 pending critical pairs + 0 deferred
// 65 equations and 7090 pending critical pairs + 0 deferred
// 66 equations and 7385 pending critical pairs + 0 deferred
// 67 equations and 7772 pending critical pairs + 0 deferred
// 68 equations and 7972 pending critical pairs + 0 deferred
// 69 equations and 8417 pending critical pairs + 0 deferred
// 70 equations and 8757 pending critical pairs + 0 deferred
// 71 equations and 9117 pending critical pairs + 0 deferred
// 72 equations and 9651 pending critical pairs + 0 deferred
// 73 equations and 10056 pending critical pairs + 0 deferred
// 74 equations and 10408 pending critical pairs + 0 deferred
// 75 equations and 10648 pending critical pairs + 0 deferred
// 76 equations and 10997 pending critical pairs + 0 deferred
// 77 equations and 11519 pending critical pairs + 0 deferred
// 78 equations and 12079 pending critical pairs + 0 deferred
// 79 equations and 12417 pending critical pairs + 0 deferred
// 80 equations and 12614 pending critical pairs + 0 deferred
// 81 equations and 12841 pending critical pairs + 0 deferred
// 82 equations and 13036 pending critical pairs + 0 deferred
// 82 equations and 13000 pending critical pairs + 0 deferred
// 83 equations and 13478 pending critical pairs + 0 deferred
// 84 equations and 14104 pending critical pairs + 0 deferred
// 85 equations and 14692 pending critical pairs + 0 deferred
// 86 equations and 15094 pending critical pairs + 0 deferred
// 87 equations and 15536 pending critical pairs + 0 deferred
// 88 equations and 16009 pending critical pairs + 1 deferred
// 89 equations and 16517 pending critical pairs + 1 deferred
// 90 equations and 17176 pending critical pairs + 1 deferred
// 91 equations and 17913 pending critical pairs + 1 deferred
// 92 equations and 18601 pending critical pairs + 1 deferred
// 93 equations and 18785 pending critical pairs + 1 deferred
// 94 equations and 19259 pending critical pairs + 1 deferred
// 95 equations and 19588 pending critical pairs + 1 deferred
// 96 equations and 19865 pending critical pairs + 1 deferred
// 97 equations and 20169 pending critical pairs + 1 deferred
// 98 equations and 20548 pending critical pairs + 1 deferred
// 99 equations and 20861 pending critical pairs + 1 deferred
// 100 equations and 21417 pending critical pairs + 1 deferred
// 101 equations and 22096 pending critical pairs + 1 deferred
// 102 equations and 22529 pending critical pairs + 1 deferred
// 103 equations and 23100 pending critical pairs + 1 deferred
// 104 equations and 23617 pending critical pairs + 1 deferred
// 105 equations and 23983 pending critical pairs + 1 deferred
// 106 equations and 24369 pending critical pairs + 1 deferred
// 107 equations and 24669 pending critical pairs + 1 deferred
// 108 equations and 25130 pending critical pairs + 2 deferred
// 109 equations and 25655 pending critical pairs + 2 deferred
// 110 equations and 26392 pending critical pairs + 2 deferred
// 111 equations and 27065 pending critical pairs + 2 deferred
// 112 equations and 27665 pending critical pairs + 2 deferred
// 113 equations and 27918 pending critical pairs + 2 deferred
// 114 equations and 28088 pending critical pairs + 2 deferred
// 115 equations and 28314 pending critical pairs + 2 deferred
// 116 equations and 28724 pending critical pairs + 2 deferred
// 117 equations and 29215 pending critical pairs + 2 deferred
// 118 equations and 29645 pending critical pairs + 2 deferred
// 119 equations and 29758 pending critical pairs + 2 deferred
// 120 equations and 29981 pending critical pairs + 2 deferred
// 121 equations and 30065 pending critical pairs + 2 deferred
// 122 equations and 30675 pending critical pairs + 2 deferred
// 123 equations and 31081 pending critical pairs + 2 deferred
// 124 equations and 31387 pending critical pairs + 2 deferred
// 125 equations and 32102 pending critical pairs + 2 deferred
// 126 equations and 32936 pending critical pairs + 2 deferred
// 127 equations and 33333 pending critical pairs + 2 deferred
// 128 equations and 33979 pending critical pairs + 2 deferred
// 129 equations and 34752 pending critical pairs + 2 deferred
// 130 equations and 35169 pending critical pairs + 2 deferred
// 131 equations and 35805 pending critical pairs + 2 deferred
// 132 equations and 36058 pending critical pairs + 2 deferred
// 133 equations and 36310 pending critical pairs + 2 deferred
// 134 equations and 36679 pending critical pairs + 2 deferred
// 135 equations and 37009 pending critical pairs + 2 deferred
// 136 equations and 37404 pending critical pairs + 2 deferred
// 136 equations and 37000 pending critical pairs + 2 deferred
// 136 equations and 36000 pending critical pairs + 2 deferred
// 136 equations and 35000 pending critical pairs + 2 deferred
// 136 equations and 34000 pending critical pairs + 2 deferred
// 136 equations and 33000 pending critical pairs + 2 deferred
// 136 equations and 32000 pending critical pairs + 2 deferred
// 136 equations and 31000 pending critical pairs + 2 deferred
// 136 equations and 30000 pending critical pairs + 2 deferred
// 136 equations and 29000 pending critical pairs + 2 deferred
// 136 equations and 28000 pending critical pairs + 2 deferred
// 136 equations and 27000 pending critical pairs + 2 deferred
// 136 equations and 26000 pending critical pairs + 2 deferred
// 136 equations and 25000 pending critical pairs + 2 deferred
// 136 equations and 24000 pending critical pairs + 2 deferred
// 136 equations and 23000 pending critical pairs + 2 deferred
// 136 equations and 22000 pending critical pairs + 2 deferred
// 136 equations and 21000 pending critical pairs + 2 deferred
// 136 equations and 20000 pending critical pairs + 2 deferred
// 136 equations and 19000 pending critical pairs + 2 deferred
// 136 equations and 18000 pending critical pairs + 2 deferred
// 136 equations and 17000 pending critical pairs + 2 deferred
// 136 equations and 16000 pending critical pairs + 2 deferred
// 136 equations and 15000 pending critical pairs + 2 deferred
// 136 equations and 14000 pending critical pairs + 2 deferred
// 136 equations and 13000 pending critical pairs + 2 deferred
// 136 equations and 12000 pending critical pairs + 2 deferred
// 136 equations and 11000 pending critical pairs + 2 deferred
// 136 equations and 10000 pending critical pairs + 2 deferred
// 136 equations and 9000 pending critical pairs + 2 deferred
// 136 equations and 8000 pending critical pairs + 2 deferred
// 136 equations and 7000 pending critical pairs + 2 deferred
// 136 equations and 6000 pending critical pairs + 2 deferred
// 136 equations and 5000 pending critical pairs + 2 deferred
// 136 equations and 4000 pending critical pairs + 2 deferred
// 136 equations and 3000 pending critical pairs + 2 deferred
// 136 equations and 2000 pending critical pairs + 2 deferred
// 136 equations and 1000 pending critical pairs + 2 deferred
// 136 equations and 0 pending critical pairs + 2 deferred
// 136 equations and 0 pending critical pairs + 1 deferred
// 136 equations and 0 pending critical pairs + 0 deferred
// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("i",[Fn ("*",[Var "x1"; Var "x2"])]);
//           Fn ("*",[Fn ("i",[Var "x2"]); Fn ("i",[Var "x1"])])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Var "x0"]); Fn ("1",[])]); Fn ("i",[Var "x0"])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x3"])]);
//           Var "x3"]));
//    Atom
//      (R ("=",
//          [Fn ("i",[Fn ("i",[Var "x0"])]); Fn ("*",[Var "x0"; Fn ("1",[])])]));
//    Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x2"])]);
//           Var "x2"]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//           Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Var "x"; Fn ("i",[Var "x"])]); Fn ("1",[])]))]
let eqs002 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x"); (parse "x * i(x) = 1")];;
complete_and_simplify ["1"; "*"; "i"] eqs002;;
***********)

// ------------------------------------------------------------------------- //
// Auxiliary result used to justify extension for example 9.                 //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// val it : int list = [5; 4]
(meson002 ** equalitize) (parse "(forall x y z. x * y = x * z ==> y = z) <=> (forall x z. exists w. forall y. z = x * y ==> w = y)");;

// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula =
//   Or
//     (Not (Atom (R ("=",[Var "z"; Fn ("*",[Var "x"; Var "y"])]))),
//      Atom (R ("=",[Fn ("f_w",[Var "x"; Var "z"]); Var "y"])))
skolemize (parse "forall x z. exists w. forall y. z = x * y ==> w = y");;

// val eqs003 : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom (R ("=",[Fn ("f",[Var "a"; Fn ("*",[Var "a"; Var "b"])]); Var "b"]));
//    Atom (R ("=",[Fn ("g",[Fn ("*",[Var "a"; Var "b"]); Var "b"]); Var "a"]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "a"]); Var "a"]));
//    Atom (R ("=",[Fn ("*",[Var "a"; Fn ("1",[])]); Var "a"]))]
let eqs003 = [(parse "f(a,a*b) = b"); (parse "g(a*b,b) = a"); (parse "1 * a = a"); (parse "a * 1 = a")];;

// 5 equations and 8 pending critical pairs + 0 deferred
// 6 equations and 10 pending critical pairs + 0 deferred
// 7 equations and 11 pending critical pairs + 0 deferred
// 8 equations and 12 pending critical pairs + 0 deferred
// 8 equations and 0 pending critical pairs + 0 deferred
// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom (R ("=",[Fn ("g",[Var "x1"; Var "x1"]); Fn ("1",[])]));
//    Atom (R ("=",[Fn ("g",[Var "x0"; Fn ("1",[])]); Var "x0"]));
//    Atom (R ("=",[Fn ("f",[Fn ("1",[]); Var "x1"]); Var "x1"]));
//    Atom (R ("=",[Fn ("f",[Var "x0"; Var "x0"]); Fn ("1",[])]));
//    Atom (R ("=",[Fn ("f",[Var "a"; Fn ("*",[Var "a"; Var "b"])]); Var "b"]));
//    Atom (R ("=",[Fn ("g",[Fn ("*",[Var "a"; Var "b"]); Var "b"]); Var "a"]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "a"]); Var "a"]));
//    Atom (R ("=",[Fn ("*",[Var "a"; Fn ("1",[])]); Var "a"]))]
complete_and_simplify ["1"; "*"; "f"; "g"] eqs003;;

// ------------------------------------------------------------------------- //
// K&B example 7, where we need to divide through.                           //
// ------------------------------------------------------------------------- //

(********** Can't orient
// val eqs004 : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("f",[Var "a"; Fn ("f",[Var "b"; Var "c"; Var "a"]); Var "d"]);
//           Var "c"]))]
let eqs004 =  [(parse "f(a,f(b,c,a),d) = c")];;

// 1 equations and 0 pending critical pairs + 1 deferred
// System.Collections.Generic.KeyNotFoundException: Exception of type 'System.Collections.Generic.KeyNotFoundException' was thrown.
complete_and_simplify ["f"] eqs004;;
************)

// val eqs005 : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("f",[Var "a"; Fn ("f",[Var "b"; Var "c"; Var "a"]); Var "d"]);
//           Var "c"]));
//    Atom
//      (R ("=",
//          [Fn ("f",[Var "a"; Var "b"; Var "c"]); Fn ("g",[Var "a"; Var "b"])]));
//    Atom (R ("=",[Fn ("g",[Var "a"; Var "b"]); Fn ("h",[Var "b"])]))]
let eqs005 =  [(parse "f(a,f(b,c,a),d) = c"); (parse "f(a,b,c) = g(a,b)"); (parse "g(a,b) = h(b)")];;

// 4 equations and 11 pending critical pairs + 0 deferred
// 4 equations and 0 pending critical pairs + 0 deferred
// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom (R ("=",[Fn ("h",[Fn ("h",[Var "x2"])]); Var "x2"]));
//    Atom (R ("=",[Fn ("f",[Var "a"; Var "b"; Var "c"]); Fn ("h",[Var "b"])]));
//    Atom (R ("=",[Fn ("g",[Var "a"; Var "b"]); Fn ("h",[Var "b"])]))]
complete_and_simplify ["h"; "g"; "f"] eqs005;;

// ------------------------------------------------------------------------- //
// Other examples not in the book, mostly from K&B                           //
// ------------------------------------------------------------------------- //

// ------------------------------------------------------------------------- //
// Group theory I (K & B example 1).                                         //
// ------------------------------------------------------------------------- //

// val eqs006 : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//           Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
let eqs006 = [(parse "1 * x = x"); (parse "i(x) * x = 1"); (parse "(x * y) * z = x * y * z")];;

// 4 equations and 8 pending critical pairs + 0 deferred
// 5 equations and 12 pending critical pairs + 0 deferred
// 6 equations and 16 pending critical pairs + 0 deferred
// 7 equations and 27 pending critical pairs + 0 deferred
// 8 equations and 51 pending critical pairs + 0 deferred
// 9 equations and 70 pending critical pairs + 0 deferred
// 10 equations and 81 pending critical pairs + 0 deferred
// 11 equations and 78 pending critical pairs + 0 deferred
// 12 equations and 85 pending critical pairs + 0 deferred
// 13 equations and 114 pending critical pairs + 0 deferred
// 14 equations and 151 pending critical pairs + 0 deferred
// 15 equations and 180 pending critical pairs + 0 deferred
// 16 equations and 247 pending critical pairs + 0 deferred
// 17 equations and 298 pending critical pairs + 0 deferred
// 18 equations and 356 pending critical pairs + 0 deferred
// 19 equations and 404 pending critical pairs + 0 deferred
// 20 equations and 485 pending critical pairs + 0 deferred
// 21 equations and 530 pending critical pairs + 0 deferred
// 22 equations and 583 pending critical pairs + 0 deferred
// 23 equations and 642 pending critical pairs + 0 deferred
// 24 equations and 730 pending critical pairs + 0 deferred
// 25 equations and 779 pending critical pairs + 0 deferred
// 26 equations and 794 pending critical pairs + 0 deferred
// 27 equations and 819 pending critical pairs + 1 deferred
// 28 equations and 918 pending critical pairs + 1 deferred
// 29 equations and 901 pending critical pairs + 1 deferred
// 30 equations and 1005 pending critical pairs + 1 deferred
// 31 equations and 1086 pending critical pairs + 1 deferred
// 32 equations and 1155 pending critical pairs + 1 deferred
// 32 equations and 1000 pending critical pairs + 1 deferred
// 32 equations and 0 pending critical pairs + 1 deferred
// 32 equations and 0 pending critical pairs + 0 deferred
// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
//           Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
//    Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
//    Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
//    Atom (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
//           Var "x3"]));
//    Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
//           Var "x2"]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//           Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
complete_and_simplify ["1"; "*"; "i"] eqs006;;

// ------------------------------------------------------------------------- //
// However, with the rules in a different order, things take longer.         //
// At least we don't need to defer any critical pairs...                     //
// ------------------------------------------------------------------------- //

// val eqs007 : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//           Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]))]
let eqs007 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x"); (parse "i(x) * x = 1")];;

// 4 equations and 8 pending critical pairs + 0 deferred
// 5 equations and 12 pending critical pairs + 0 deferred
// 6 equations and 30 pending critical pairs + 0 deferred
// 7 equations and 38 pending critical pairs + 0 deferred
// 8 equations and 51 pending critical pairs + 0 deferred
// 9 equations and 70 pending critical pairs + 0 deferred
// 10 equations and 80 pending critical pairs + 0 deferred
// 11 equations and 116 pending critical pairs + 0 deferred
// 12 equations and 153 pending critical pairs + 0 deferred
// 13 equations and 194 pending critical pairs + 0 deferred
// 14 equations and 233 pending critical pairs + 0 deferred
// 15 equations and 313 pending critical pairs + 0 deferred
// 16 equations and 303 pending critical pairs + 0 deferred
// 17 equations and 311 pending critical pairs + 0 deferred
// 18 equations and 358 pending critical pairs + 0 deferred
// 19 equations and 427 pending critical pairs + 0 deferred
// 20 equations and 477 pending critical pairs + 0 deferred
// 21 equations and 578 pending critical pairs + 0 deferred
// 22 equations and 625 pending critical pairs + 0 deferred
// 23 equations and 683 pending critical pairs + 0 deferred
// 24 equations and 745 pending critical pairs + 0 deferred
// 25 equations and 839 pending critical pairs + 0 deferred
// 26 equations and 897 pending critical pairs + 0 deferred
// 27 equations and 862 pending critical pairs + 0 deferred
// 28 equations and 865 pending critical pairs + 1 deferred
// 29 equations and 970 pending critical pairs + 1 deferred
// 30 equations and 946 pending critical pairs + 1 deferred
// 31 equations and 1053 pending critical pairs + 1 deferred
// 32 equations and 1136 pending critical pairs + 1 deferred
// 33 equations and 1208 pending critical pairs + 1 deferred
// 33 equations and 1000 pending critical pairs + 1 deferred
// 33 equations and 0 pending critical pairs + 1 deferred
// 33 equations and 0 pending critical pairs + 0 deferred
// val it : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom
//      (R ("=",
//          [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
//           Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
//    Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
//    Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
//    Atom (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
//           Var "x3"]));
//    Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
//           Var "x2"]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//           Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
//    Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]))]
complete_and_simplify ["1"; "*"; "i"] eqs007;;

// ------------------------------------------------------------------------- //
// Example 2: if we orient i(x) * i(y) -> i(x * y), things diverge.          //
// ------------------------------------------------------------------------- //

(*************
// val eqs008 : fol Reasoning.Automated.Harrison.Handbook.formulas.formula list =
//   [Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
//    Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
//    Atom
//      (R ("=",
//          [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
//           Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
let eqs008 = [(parse "1 * x = x"); (parse "i(x) * x = 1"); (parse "(x * y) * z = x * y * z")];;

// 4 equations and 8 pending critical pairs + 0 deferred
// 5 equations and 12 pending critical pairs + 0 deferred
// 6 equations and 16 pending critical pairs + 0 deferred
// 7 equations and 27 pending critical pairs + 0 deferred
// 8 equations and 51 pending critical pairs + 0 deferred
// 9 equations and 70 pending critical pairs + 0 deferred
// 10 equations and 81 pending critical pairs + 0 deferred
// 11 equations and 78 pending critical pairs + 0 deferred
// 12 equations and 85 pending critical pairs + 0 deferred
// 13 equations and 114 pending critical pairs + 0 deferred
// 14 equations and 151 pending critical pairs + 0 deferred
// 15 equations and 180 pending critical pairs + 0 deferred
// 16 equations and 247 pending critical pairs + 0 deferred
// 17 equations and 298 pending critical pairs + 0 deferred
// 18 equations and 356 pending critical pairs + 0 deferred
// 19 equations and 404 pending critical pairs + 0 deferred
// 20 equations and 485 pending critical pairs + 0 deferred
// 21 equations and 563 pending critical pairs + 1 deferred
// 22 equations and 624 pending critical pairs + 1 deferred
// 23 equations and 686 pending critical pairs + 1 deferred
// 24 equations and 775 pending critical pairs + 1 deferred
// 25 equations and 824 pending critical pairs + 1 deferred
// 26 equations and 881 pending critical pairs + 2 deferred
// 27 equations and 915 pending critical pairs + 3 deferred
// 28 equations and 1018 pending critical pairs + 3 deferred
// 28 equations and 1000 pending critical pairs + 3 deferred
// 29 equations and 964 pending critical pairs + 4 deferred
// 30 equations and 1074 pending critical pairs + 4 deferred
// 31 equations and 1160 pending critical pairs + 4 deferred
// 32 equations and 1303 pending critical pairs + 5 deferred
// 33 equations and 1468 pending critical pairs + 6 deferred
// 34 equations and 1554 pending critical pairs + 6 deferred
// 35 equations and 1541 pending critical pairs + 8 deferred
// 36 equations and 1786 pending critical pairs + 8 deferred
// 37 equations and 1871 pending critical pairs + 8 deferred
// 38 equations and 1864 pending critical pairs + 20 deferred
// 39 equations and 2037 pending critical pairs + 23 deferred
// 40 equations and 2334 pending critical pairs + 23 deferred
// 41 equations and 2271 pending critical pairs + 28 deferred
// 42 equations and 2532 pending critical pairs + 29 deferred
// 43 equations and 2661 pending critical pairs + 30 deferred
// 44 equations and 2817 pending critical pairs + 31 deferred
// 45 equations and 3008 pending critical pairs + 32 deferred
// 45 equations and 3000 pending critical pairs + 33 deferred
// 46 equations and 3165 pending critical pairs + 33 deferred
// 47 equations and 3317 pending critical pairs + 33 deferred
// 48 equations and 3533 pending critical pairs + 34 deferred
// 49 equations and 3875 pending critical pairs + 35 deferred
// 50 equations and 4067 pending critical pairs + 36 deferred
// 51 equations and 4291 pending critical pairs + 37 deferred
// 52 equations and 4536 pending critical pairs + 40 deferred
// 53 equations and 4740 pending critical pairs + 49 deferred
// 54 equations and 4920 pending critical pairs + 55 deferred
// 55 equations and 5108 pending critical pairs + 56 deferred
// 56 equations and 5447 pending critical pairs + 57 deferred
// 57 equations and 5611 pending critical pairs + 58 deferred
// 58 equations and 5810 pending critical pairs + 59 deferred
// 59 equations and 6045 pending critical pairs + 61 deferred
// 60 equations and 6244 pending critical pairs + 67 deferred
// 61 equations and 6434 pending critical pairs + 71 deferred
// 62 equations and 6714 pending critical pairs + 71 deferred
// 63 equations and 7137 pending critical pairs + 71 deferred
// 64 equations and 7628 pending critical pairs + 71 deferred
// 65 equations and 8128 pending critical pairs + 71 deferred
// 66 equations and 8383 pending critical pairs + 71 deferred
// 67 equations and 8685 pending critical pairs + 71 deferred
// 68 equations and 9005 pending critical pairs + 71 deferred
// 69 equations and 9428 pending critical pairs + 71 deferred
// 70 equations and 9860 pending critical pairs + 71 deferred
// 71 equations and 10282 pending critical pairs + 71 deferred
// 72 equations and 10546 pending critical pairs + 74 deferred
// 73 equations and 11067 pending critical pairs + 74 deferred
// 74 equations and 11682 pending critical pairs + 74 deferred
// 75 equations and 12309 pending critical pairs + 74 deferred
// 76 equations and 12947 pending critical pairs + 74 deferred
// 77 equations and 13282 pending critical pairs + 74 deferred
// 78 equations and 13649 pending critical pairs + 74 deferred
// 79 equations and 14056 pending critical pairs + 74 deferred
// 80 equations and 14468 pending critical pairs + 74 deferred
// 81 equations and 15040 pending critical pairs + 74 deferred
// 82 equations and 15622 pending critical pairs + 74 deferred
// 83 equations and 16214 pending critical pairs + 74 deferred
// 84 equations and 16799 pending critical pairs + 74 deferred
// 85 equations and 17278 pending critical pairs + 74 deferred
// 86 equations and 17500 pending critical pairs + 77 deferred
// 87 equations and 17926 pending critical pairs + 77 deferred
// 88 equations and 18357 pending critical pairs + 77 deferred
// 89 equations and 18786 pending critical pairs + 77 deferred
// 90 equations and 19293 pending critical pairs + 77 deferred
// 91 equations and 19846 pending critical pairs + 77 deferred
// 92 equations and 20405 pending critical pairs + 77 deferred
// 93 equations and 21047 pending critical pairs + 77 deferred
// 94 equations and 21777 pending critical pairs + 77 deferred
// 95 equations and 22378 pending critical pairs + 77 deferred
// 96 equations and 22827 pending critical pairs + 77 deferred
// 97 equations and 23199 pending critical pairs + 77 deferred
// 98 equations and 23718 pending critical pairs + 77 deferred
// 99 equations and 24169 pending critical pairs + 77 deferred
// 100 equations and 24625 pending critical pairs + 77 deferred
// 101 equations and 25155 pending critical pairs + 77 deferred
// 102 equations and 25500 pending critical pairs + 77 deferred
// 103 equations and 26019 pending critical pairs + 77 deferred
// 104 equations and 26592 pending critical pairs + 77 deferred
// 105 equations and 27124 pending critical pairs + 77 deferred
// 106 equations and 27660 pending critical pairs + 77 deferred
// 107 equations and 28163 pending critical pairs + 77 deferred
// 108 equations and 28821 pending critical pairs + 77 deferred
// 109 equations and 29400 pending critical pairs + 77 deferred
// 110 equations and 30054 pending critical pairs + 77 deferred
// 111 equations and 30520 pending critical pairs + 77 deferred
// 112 equations and 30983 pending critical pairs + 77 deferred
// 113 equations and 31418 pending critical pairs + 77 deferred
// 114 equations and 31865 pending critical pairs + 77 deferred
// 115 equations and 32197 pending critical pairs + 79 deferred
// 116 equations and 32632 pending critical pairs + 79 deferred
// 117 equations and 33090 pending critical pairs + 79 deferred
// 118 equations and 33585 pending critical pairs + 79 deferred
// 119 equations and 33965 pending critical pairs + 79 deferred
// 120 equations and 34326 pending critical pairs + 80 deferred
// 121 equations and 34602 pending critical pairs + 80 deferred
// 122 equations and 35154 pending critical pairs + 80 deferred
// 123 equations and 35716 pending critical pairs + 80 deferred
// 124 equations and 36522 pending critical pairs + 80 deferred
// 125 equations and 37341 pending critical pairs + 80 deferred
// 126 equations and 38017 pending critical pairs + 80 deferred
// 127 equations and 38409 pending critical pairs + 80 deferred
// 128 equations and 38993 pending critical pairs + 80 deferred
// 129 equations and 39572 pending critical pairs + 80 deferred
// 130 equations and 40283 pending critical pairs + 80 deferred
// 131 equations and 41016 pending critical pairs + 80 deferred
// 132 equations and 41541 pending critical pairs + 80 deferred
// 133 equations and 41902 pending critical pairs + 83 deferred
// 134 equations and 42609 pending critical pairs + 83 deferred
// 135 equations and 43328 pending critical pairs + 83 deferred
// 136 equations and 44002 pending critical pairs + 83 deferred
// 136 equations and 44000 pending critical pairs + 83 deferred
// 137 equations and 44693 pending critical pairs + 83 deferred
// 138 equations and 45675 pending critical pairs + 83 deferred
// 139 equations and 46668 pending critical pairs + 83 deferred
// 140 equations and 47521 pending critical pairs + 83 deferred
// 141 equations and 48391 pending critical pairs + 83 deferred
// 142 equations and 49065 pending critical pairs + 83 deferred
// 143 equations and 49598 pending critical pairs + 83 deferred
// 144 equations and 50352 pending critical pairs + 83 deferred
// 145 equations and 50936 pending critical pairs + 83 deferred
// 146 equations and 51697 pending critical pairs + 83 deferred
// 147 equations and 52388 pending critical pairs + 83 deferred
// 148 equations and 53122 pending critical pairs + 83 deferred
// 149 equations and 53816 pending critical pairs + 83 deferred
// 150 equations and 54731 pending critical pairs + 83 deferred
// 151 equations and 55652 pending critical pairs + 83 deferred
// 152 equations and 56312 pending critical pairs + 83 deferred
// 153 equations and 56867 pending critical pairs + 83 deferred
// 154 equations and 57692 pending critical pairs + 86 deferred
// 155 equations and 58455 pending critical pairs + 86 deferred
// 156 equations and 58904 pending critical pairs + 86 deferred
// 157 equations and 59443 pending critical pairs + 86 deferred
complete_and_simplify ["1"; "i"; "*"] eqs008;;
 *************)

// ------------------------------------------------------------------------- //
// Group theory III, with right inverse and identity (K&B example 3).        //
// ------------------------------------------------------------------------- //

let eqs009 = [(parse "(x * y) * z = x * y * z"); (parse "x * 1 = x"); (parse "x * i(x) = 1")];;
complete_and_simplify ["1"; "*"; "i"] eqs009;;

// ------------------------------------------------------------------------- //
// Inverse property (K&B example 4).                                         //
// ------------------------------------------------------------------------- //

let eqs010 =  [(parse "i(a) * (a * b) = b")];;
complete_and_simplify ["1"; "*"; "i"] eqs010;;

let eqs011 =  [(parse "a * (i(a) * b) = b")];;
complete_and_simplify ["1"; "*"; "i"] eqs011;;

// ------------------------------------------------------------------------- //
// Group theory IV (K&B example 5).                                          //
// ------------------------------------------------------------------------- //

let eqs012 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x"); (parse "11 * x = x"); (parse "i(x) * x = 1"); (parse "j(x) * x = 11")];;
complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs012;;

// ------------------------------------------------------------------------- //
// Central groupoids (K&B example 6).                                        //
// ------------------------------------------------------------------------- //

let eqs013 =  [(parse "(a * b) * (b * c) = b")];;
complete_and_simplify ["*"] eqs013;;

// ------------------------------------------------------------------------- //
// Random axiom (K&B example 7).                                             //
// ------------------------------------------------------------------------- //

(********** Can't orient
let eqs014 =  [(parse "f(a,f(b,c,a),d) = c")];;
complete_and_simplify ["f"] eqs014;;
************)

let eqs015 =  [(parse "f(a,f(b,c,a),d) = c"); (parse "f(a,b,c) = g(a,b)"); (parse "g(a,b) = h(b)")];;
complete_and_simplify ["h"; "g"; "f"] eqs015;;

// ------------------------------------------------------------------------- //
// Another random axiom (K&B example 8).                                     //
// ------------------------------------------------------------------------- //

(************ Can't orient
let eqs016 =  [(parse "(a * b) * (c * b * a) = b")];;
complete_and_simplify ["*"] eqs016;;
 *************)

// ------------------------------------------------------------------------- //
// The cancellation law (K&B example 9).                                     //
// ------------------------------------------------------------------------- //

let eqs017 =  [(parse "f(a,a*b) = b"); (parse "g(a*b,b) = a")];;
complete_and_simplify ["*"; "f"; "g"] eqs017;;

let eqs018 = [(parse "f(a,a*b) = b"); (parse "g(a*b,b) = a"); (parse "1 * a = a"); (parse "a * 1 = a")];;
complete_and_simplify ["1"; "*"; "f"; "g"] eqs018;;

(*** Just for fun; these aren't tried by Knuth and Bendix

let eqs019 = [(parse "(x * y) * z = x * y * z"); (parse "f(a,a*b) = b"); (parse "g(a*b,b) = a"); (parse "1 * a = a"); (parse "a * 1 = a")];;
complete_and_simplify ["1"; "*"; "f"; "g"] eqs019;;

let eqs020 = [(parse "(x * y) * z = x * y * z"); (parse "f(a,a*b) = b"); (parse "g(a*b,b) = a")];;
complete_and_simplify ["*"; "f"; "g"] eqs020;;
complete_and_simplify ["f"; "g"; "*"] eqs020;;

********)

// ------------------------------------------------------------------------- //
// Loops (K&B example 10).                                                   //
// ------------------------------------------------------------------------- //

let eqs021 = [(parse "a * \(a,b) = b"); (parse "/(a,b) * b = a"); (parse "1 * a = a"); (parse "a * 1 = a")];;
complete_and_simplify ["1"; "*"; "\\"; "/"] eqs021;;

let eqs022 = [(parse "a * \(a,b) = b"); (parse "/(a,b) * b = a"); (parse "1 * a = a"); (parse "a * 1 = a"); (parse "f(a,a*b) = b"); (parse "g(a*b,b) = a")];;
complete_and_simplify ["1"; "*"; "\\"; "/"; "f"; "g"] eqs022;;

// ------------------------------------------------------------------------- //
// Another variant of groups (K&B example 11).                               //
// ------------------------------------------------------------------------- //

(******* this is not expected to terminate
let eqs023 =
 [(parse "(x * y) * z = x * y * z");
  (parse "1 * 1 = 1");
  (parse "a * i(a) = 1");
  (parse "f(1,a,b) = a");
  (parse "f(a*b,a,b) = g(a*b,b)")];;
complete_and_simplify ["1"; "g"; "f"; "*"; "i"] eqs023;;

**************)

// ------------------------------------------------------------------------- //
// (l,r)-systems (K&B example 12).                                           //
// ------------------------------------------------------------------------- //

(******* This works, but takes a long time
let eqs024 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x"); (parse "x * i(x) = 1")];;
complete_and_simplify ["1"; "*"; "i"] eqs024;;
 ***********)

// ------------------------------------------------------------------------- //
// (r,l)-systems (K&B example 13).                                           //
// ------------------------------------------------------------------------- //

(*** Note that here the simple LPO approach works, whereas K&B need
 **** some additional hacks.
 ****)

let eqs025 = [(parse "(x * y) * z = x * y * z"); (parse "x * 1 = x"); (parse "i(x) * x = 1")];;
complete_and_simplify ["1"; "*"; "i"] eqs025;;

// ------------------------------------------------------------------------- //
// (l,r) systems II (K&B example 14).                                        //
// ------------------------------------------------------------------------- //

(******* This seems to be too slow. K&B encounter a similar problem
let eqs026 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x"); (parse "11 * x = x"); (parse "x * i(x) = 1"); (parse "x * j(x) = 11")];;
complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs026;;
 ********)

// ------------------------------------------------------------------------- //
// (l,r) systems III (K&B example 15).                                       //
// ------------------------------------------------------------------------- //

(********* According to KB, this wouldn't be expected to work
let eqs027 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x");  (parse "prime(a) * a = star(a)"); (parse "star(a) * b = b")];;
complete_and_simplify ["1"; "*"; "star"; "prime"] eqs027;;
 ************)

(********** These seem too slow too. Maybe just a bad ordering?
let eqs028 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x");  (parse "hash(a) * dollar(a) * a = star(a)"); (parse "star(a) * b = b"); (parse "a * hash(a) = 1"); (parse "a * 1 = hash(hash(a))"); (parse "hash(hash(hash(a))) = hash(a)")];;
complete_and_simplify ["1"; "hash"; "star"; "*"; "dollar"] eqs028;;

let eqs029 = [(parse "(x * y) * z = x * y * z"); (parse "1 * x = x"); (parse "hash(a) * dollar(a) * a = star(a)"); (parse "star(a) * b = b"); (parse "a * hash(a) = 1"); (parse "hash(hash(a)) = a * 1"); (parse "hash(hash(hash(a))) = hash(a)")];;
complete_and_simplify ["1"; "star"; "*"; "hash"; "dollar"] eqs029;;
***********)

// ------------------------------------------------------------------------- //
// Central groupoids II. (K&B example 16).                                   //
// ------------------------------------------------------------------------- //

let eqs030 =
 [(parse "(a * a) * a = one(a)");
  (parse "a * (a * a) = two(a)");
  (parse "(a * b) * (b * c) = b");
  (parse "two(a) * b = a * b")];;

complete_and_simplify ["one"; "two"; "*"] eqs030;;

// ------------------------------------------------------------------------- //
// Central groupoids II. (K&B example 17).                                   //
// ------------------------------------------------------------------------- //

(******* Not ordered right...

let eqs031 =
 [(parse "(a*a * a) = one(a)");
  (parse "(a * a*a) = two(a)");
  (parse "(a*b * b*c) = b")];;

complete_and_simplify ["*"; "one"; "two"] eqs031;;

 ************)

// ------------------------------------------------------------------------- //
// Simply congruence closure.                                                //
// ------------------------------------------------------------------------- //

let eqs032 =  [(parse "f(f(f(f(f(1))))) = 1"); (parse "f(f(f(1))) = 1")];;

complete_and_simplify ["1"; "f"] eqs032;;

// ------------------------------------------------------------------------- //
// Bill McCune's and Deepak Kapur's single axioms for groups.                //
// ------------------------------------------------------------------------- //

(****************

let eqs033 =
 [(parse "x * i(y * (((z * i(z)) * i(u * y)) * x)) = u")];;

complete_and_simplify ["1"; "*"; "i"] eqs033;;

let eqs034 =
 [(parse "((1 / (x / (y / (((x / x) / x) / z)))) / z) = y")];;

complete_and_simplify ["1"; "/"] eqs034;;

let eqs035 =
 [(parse "i(x * i(x)) * (i(i((y * z) * u) * y) * i(u)) = z")];;

complete_and_simplify ["*"; "i"] eqs035;;

**************)

// ------------------------------------------------------------------------- //
// A rather simple example from Baader & Nipkow, p. 141.                     //
// ------------------------------------------------------------------------- //

let eqs036 =  [(parse "f(f(x)) = g(x)")];;
complete_and_simplify ["g"; "f"] eqs036;;

let eqs1,def1,crits1 = funpow 122 (complete1 ord) (eqs036,def,crits);;
let eqs2,def2,crits2 = funpow 123 (complete1 ord) (eqs036,def,crits);;

// ------------------------------------------------------------------------- //
// Some of the exercises (these are taken from Baader & Nipkow).             //
// ------------------------------------------------------------------------- //

let eqs037 =
 [(parse "f(f(x)) = f(x)");
  (parse "g(g(x)) = f(x)");
  (parse "f(g(x)) = g(x)");
  (parse "g(f(x)) = f(x)")];;
complete_and_simplify ["f"; "g"] eqs037;;

let eqs038 =  [(parse "f(g(f(x))) = g(x)")];;
complete_and_simplify ["f"; "g"] eqs038;;

// ------------------------------------------------------------------------- //
// Inductive theorem proving example.                                        //
// ------------------------------------------------------------------------- //

let eqs039 =
 [(parse "0 + y = y");
  (parse "SUC(x) + y = SUC(x + y)");
  (parse "append(nil,l) = l");
  (parse "append(h::t,l) = h::append(t,l)");
  (parse "length(nil) = 0");
  (parse "length(h::t) = SUC(length(t))");
  (parse "rev(nil) = nil");
  (parse "rev(h::t) = append(rev(t),h::nil)")];;
complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "length"; "append"; "rev"] eqs039;;

let iprove eqs' tm =
 complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
   (tm :: eqs' @ eqs039);;

iprove [] (parse "x + 0 = x");;

iprove [] (parse "x + SUC(y) = SUC(x + y)");;

iprove [] (parse "(x + y) + z = x + y + z");;

iprove [] (parse "length(append(x,y)) = length(x) + length(y)");;

iprove [] (parse "append(append(x,y),z) = append(x,append(y,z))");;

iprove [] (parse "append(x,nil) = x");;

iprove [(parse "append(append(x,y),z) = append(x,append(y,z))");
        (parse "append(x,nil) = x")]
        (parse "rev(append(x,y)) = append(rev(y),rev(x))");;

iprove [(parse "rev(append(x,y)) = append(rev(y),rev(x))");
        (parse "append(x,nil) = x");
        (parse "append(append(x,y),z) = append(x,append(y,z))")]
        (parse "rev(rev(x)) = x");;

// ------------------------------------------------------------------------- //
// Here it's not immediately so obvious since we get extra equs.             //
// ------------------------------------------------------------------------- //

iprove [] (parse "rev(rev(x)) = x");;

// ------------------------------------------------------------------------- //
// With fewer lemmas, it may just need more time or may not terminate.       //
// ------------------------------------------------------------------------- //

(******** not enough lemmas...or maybe it just needs more runtime

iprove [(parse "rev(append(x,y)) = append(rev(y),rev(x))")]
        (parse "rev(rev(x)) = x");;

 *********)

// ------------------------------------------------------------------------- //
// Now something actually false...                                           //
// ------------------------------------------------------------------------- //

iprove [] (parse "length(append(x,y)) = length(x)");; (** try something false ***)
