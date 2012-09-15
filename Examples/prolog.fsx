
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
open Reasoning.Automated.Harrison.Handbook.resolution
open Reasoning.Automated.Harrison.Handbook.prolog

// pg. 208
// ------------------------------------------------------------------------- //
// A Horn example.                                                           //
// ------------------------------------------------------------------------- //

let p32 = hornprove (parse "(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ (forall x. Q(x) /\ H(x) ==> J(x)) /\ (forall x. R(x) ==> H(x)) ==> (forall x. P(x) /\ R(x) ==> J(x))");;

// pg. 208
// ------------------------------------------------------------------------- //
// A non-Horn example.                                                       //
// ------------------------------------------------------------------------- //

// System.Exception: non-Horn clause
hornprove (parse "(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

// pg. 120
// ------------------------------------------------------------------------- //
// Ordering example.                                                         //
// ------------------------------------------------------------------------- //

// val lerules : string list = ["0 <= X"; "S(X) <= S(Y) :- X <= Y"]
let lerules = ["0 <= X"; "S(X) <= S(Y) :- X <= Y"];;

simpleprolog lerules "S(S(0)) <= S(S(S(0)))";;

// System.Exception: tryfind
simpleprolog lerules "S(S(0)) <= S(0)";;

let env = simpleprolog lerules "S(S(0)) <= X";;
apply env "X";;

//
// ------------------------------------------------------------------------- //
// Example again.                                                            //
// ------------------------------------------------------------------------- //
   
// val it : fol formula list =
//   [Atom (R ("=",[Var "X"; Fn ("S",[Fn ("S",[Var "_3"])])]))]
prolog lerules "S(S(0)) <= X";;

// ------------------------------------------------------------------------- //
// Append example, showing symmetry between inputs and outputs.              //
// ------------------------------------------------------------------------- //

let appendrules = ["append(nil,L,L)"; "append(H::T,L,H::A) :- append(T,L,A)"];;

prolog appendrules "append(1::2::nil,3::4::nil,Z)";;

prolog appendrules "append(1::2::nil,Y,1::2::3::4::nil)";;

prolog appendrules "append(X,3::4::nil,1::2::3::4::nil)";;

prolog appendrules "append(X,Y,1::2::3::4::nil)";;

// ------------------------------------------------------------------------- //
// However this way round doesn't work.                                      //
// ------------------------------------------------------------------------- //

//***
//*** prolog appendrules "append(X,3::4::nil,X)";;
//***

// ------------------------------------------------------------------------- //
// A sorting example (from Lloyd's "Foundations of Logic Programming").      //
// ------------------------------------------------------------------------- //

let sortrules =
 ["sort(X,Y) :- perm(X,Y),sorted(Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

prolog sortrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

// ------------------------------------------------------------------------- //
// Yet with a simple swap of the first two predicates...                     //
// ------------------------------------------------------------------------- //

let badrules =
 ["sort(X,Y) :- sorted(Y), perm(X,Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

//** This no longer works

// Process is terminated due to StackOverflowException.
prolog badrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

