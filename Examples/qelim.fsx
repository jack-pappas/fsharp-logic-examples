
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
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
//open Reasoning.Automated.Harrison.Handbook.paramodulation
open Reasoning.Automated.Harrison.Handbook.decidable
open Reasoning.Automated.Harrison.Handbook.qelim

// pg. 335
//  ------------------------------------------------------------------------- // 
//  Examples.                                                                 // 
//  ------------------------------------------------------------------------- // 

// val it : fol formula = True
quelim_dlo (parse "forall x y. exists z. z < x /\ z < y");;

// val it : fol formula = True
quelim_dlo (parse "exists z. z < x /\ z < y");;

// val it : fol formula = Atom (R ("<",[Var "x"; Var "y"]))
quelim_dlo (parse "exists z. x < z /\ z < y");;

// val it : fol formula =
//   Not
//     (Or (Atom (R ("<",[Var "b"; Var "a"])),Atom (R ("<",[Var "b"; Var "a"]))))
quelim_dlo (parse "(forall x. x < a ==> x < b)");;

// val it : fol formula = True
quelim_dlo (parse "forall a b. (forall x. x < a ==> x < b) <=> a <= b");;

// val it : fol formula = True
quelim_dlo (parse "forall a b. (forall x. x < a <=> x < b) <=> a = b");;

// val it : fol formula = False
quelim_dlo (parse "exists x y z. forall u.
                 x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)");;

//  ------------------------------------------------------------------------- // 
//  More tests (not in the text).                                             // 
//  ------------------------------------------------------------------------- // 

// CPU time (user): 0.000000
// val it : fol formula = True
time quelim_dlo (parse "forall x. exists y. x < y");;

time quelim_dlo (parse "forall x y z. x < y /\ y < z ==> x < z");;

time quelim_dlo (parse "forall x y. x < y \/ (x = y) \/ y < x");;

time quelim_dlo (parse "exists x y. x < y /\ y < x");;

time quelim_dlo (parse "forall x y. exists z. z < x /\ x < y");;

time quelim_dlo (parse "exists z. z < x /\ x < y");;

time quelim_dlo (parse "forall x y. exists z. z < x /\ z < y");;

time quelim_dlo (parse "forall x y. x < y ==> exists z. x < z /\ z < y");;

time quelim_dlo
  (parse "forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)");;

time quelim_dlo (parse "exists x. x = x");;

time quelim_dlo (parse "exists x. x = x /\ x = y");;

time quelim_dlo (parse "exists z. x < z /\ z < y");;

time quelim_dlo (parse "exists z. x <= z /\ z <= y");;

time quelim_dlo (parse "exists z. x < z /\ z <= y");;

time quelim_dlo (parse "forall x y z. exists u. u < x /\ u < y /\ u < z");;

time quelim_dlo (parse "forall y. x < y /\ y < z ==> w < z");;

time quelim_dlo (parse "forall x y. x < y");;

time quelim_dlo (parse "exists z. z < x /\ x < y");;

time quelim_dlo (parse "forall a b. (forall x. x < a ==> x < b) <=> a <= b");;

time quelim_dlo (parse "forall x. x < a ==> x < b");;

time quelim_dlo (parse "forall x. x < a ==> x <= b");;

time quelim_dlo (parse "forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)");;

time quelim_dlo (parse "forall x y. x <= y \/ x > y");;

time quelim_dlo (parse "forall x y. x <= y \/ x < y");;
