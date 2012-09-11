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

#I @"E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook\bin\Debug"
#r @"Reasoning.Automated.Harrison.Handbook.dll"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
open Reasoning.Automated.Harrison.Handbook.eqelim

// pg. 287
// ------------------------------------------------------------------------- //
// The x^2 = 1 implies Abelian problem.                                      //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// val it : int list = [13]
meson002 
  (parse "(forall x. P(1,x,x)) /\ 
          (forall x. P(x,x,1)) /\ 
          (forall u v w x y z. P(x,y,u) /\ 
          P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
              ==> forall a b c. P(a,b,c) 
          ==> P(b,a,c)");;

// pg. 288
// ------------------------------------------------------------------------- //
// Lemma for equivalence elimination.                                        //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// val it : int list = [4; 3; 9; 3; 2; 7]
meson002 
  (parse "(forall x. R(x,x)) /\ 
          (forall x y. R(x,y) ==>  R(y,x)) /\ 
          (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
          <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z)))");;
   
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// Searching with depth limit 14
// Searching with depth limit 15
// Searching with depth limit 16
// Searching with depth limit 17
// Searching with depth limit 18
// Searching with depth limit 19
// Searching with depth limit 20
// Searching with depth limit 21
// Searching with depth limit 22
// Searching with depth limit 23
// Searching with depth limit 24
// Searching with depth limit 25
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// Searching with depth limit 14
// Searching with depth limit 15
// Searching with depth limit 16
// Searching with depth limit 17
// Searching with depth limit 18
// Searching with depth limit 19
// Searching with depth limit 20
// Searching with depth limit 21
// Searching with depth limit 22
// Searching with depth limit 23
// Searching with depth limit 24
// Searching with depth limit 25
// CPU time (user): 136.218750
// val it : int list = [25; 25]
time bmeson 
  (parse "(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
          (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;          

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// Searching with depth limit 14
// Searching with depth limit 15
// Searching with depth limit 16
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// Searching with depth limit 14
// Searching with depth limit 15
// Searching with depth limit 16
// CPU time (user): 18.515625
// val it : int list = [16; 16]                                                           
time emeson 
  (parse "(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
          (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;        
                                                     
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// Searching with depth limit 14
// Searching with depth limit 15
// Searching with depth limit 16
// Searching with depth limit 17
// Searching with depth limit 18
// Searching with depth limit 19
// CPU time (user): 1007.703125
// val it : int list = [19]
time bmeson 
  (parse "(forall x y z. x * (y * z) = (x * y) * z) /\ (forall x. e * x = x) /\ (forall x. i(x) * x = e) ==> forall x. x * i(x) = e");;

//// ------------------------------------------------------------------------- //
//// Older stuff not now in the text.                                          //
//// ------------------------------------------------------------------------- //
//
//let ewd = (parse "(forall x. f(x) ==> g(x)) /\ (exists x. f(x)) /\ (forall x y. g(x) /\ g(y) ==> x = y) ==> forall y. g(y) ==> f(y)");;
//
//let wishnu = (parse "(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=> (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;
//
//let group1 =
// (parse "(forall x y z. x * (y * z) = (x * y) * z) /\
//   (forall x. e * x = x) /\
//   (forall x. i(x) * x = e)
//   ==> forall x. x * e = x");;
//
//let group2 =
// (parse "(forall x y z. x * (y * z) = (x * y) * z) /\
//   (forall x. e * x = x) /\
//   (forall x. i(x) * x = e)
//   ==> forall x. x * i(x) = e");;
//
//time bmeson ewd;;
//time emeson ewd;;
//
//(***********
//
//time bmeson wishnu;;
//time emeson wishnu;;
//
//time bmeson group1;;
//time emeson group1;;
//
//time bmeson group2;;
//time emeson group2;;
// *************)
//
//// ------------------------------------------------------------------------- //
//// Nice function composition exercise from "Conceptual Mathematics".         //
//// ------------------------------------------------------------------------- //
//
//(***********
//
//let fm = (parse 
//  "(forall x y z. x * (y * z) = (x * y) * z) /\ p * q * p = p
//    ==> exists q'. p * q' * p = p /\ q' * p * q' = q'");;
//
//time bmeson fm;;        //* Seems to take a bit longer than below version  *//
//
//time emeson fm;;        //* Works in 64275 seconds(!), depth 30, on laptop *//
//
// *************)
//
////*** Some other predicate formulations no longer in the main text
//
//meson002
// (parse "(forall x. P(1,x,x)) /\
//   (forall x. P(i(x),x,1)) /\
//   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
//   ==> forall x. P(x,1,x)");;
//
//meson002
// (parse "(forall x. P(1,x,x)) /\
//   (forall x. P(i(x),x,1)) /\
//   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
//   ==> forall x. P(x,i(x),1)");;
//
//// ------------------------------------------------------------------------- //
//// See how efficiency drops when we assert completeness.                     //
//// ------------------------------------------------------------------------- //
//
//meson002 
//  (parse "(forall x. P(1,x,x)) /\
//   (forall x. P(x,x,1)) /\
//   (forall x y. exists z. P(x,y,z)) /\
//   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
//   ==> forall a b c. P(a,b,c) ==> P(b,a,c)");;
//
////** More reductions, not now explicitly in the text.
//
//meson002 
//  (parse "(forall x. R(x,x)) /\
//   (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
//   <=> (forall x y. R(x,y) <=> (forall z. R(y,z) ==> R(x,z)))");;
//
//meson002 (parse "(forall x y. R(x,y) ==>  R(y,x)) <=>
//   (forall x y. R(x,y) <=> R(x,y) /\ R(y,x))");;
//
//// ------------------------------------------------------------------------- //
//// Show how Equiv' reduces to triviality.                                    //
//// ------------------------------------------------------------------------- //
//
//meson002 (parse "(forall x. (forall w. R'(x,w) <=> R'(x,w))) /\
//   (forall x y. (forall w. R'(x,w) <=> R'(y,w))
//                ==> (forall w. R'(y,w) <=> R'(x,w))) /\
//   (forall x y z. (forall w. R'(x,w) <=> R'(y,w)) /\
//                  (forall w. R'(y,w) <=> R'(z,w))
//                  ==> (forall w. R'(x,w) <=> R'(z,w)))");;
//
//// ------------------------------------------------------------------------- //
//// More auxiliary proofs for Brand's S and T modification.                   //
//// ------------------------------------------------------------------------- //
//
//meson002 (parse "(forall x y. R(x,y) <=> (forall z. R'(x,z) <=> R'(y,z))) /\
//   (forall x. R'(x,x))
//   ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;
//
//meson002 (parse "(forall x y. R(x,y) <=> (forall z. R'(y,z) ==> R'(x,z))) /\
//   (forall x. R'(x,x))
//   ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;
//
//meson002 (parse "(forall x y. R(x,y) <=> R'(x,y) /\ R'(y,x))
//   ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;
