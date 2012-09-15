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
//open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux

// pg. 175
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// val p20 : int = 2
let p20p = prawitz (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// Note: compare here is from tableaux module not F# 

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 3 items in list
// 1 ground instances tried; 3 items in list
// 2 ground instances tried; 6 items in list
//
// val p19 : int * int = (3, 3)
let p19c = compare (parse "exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 5 items in list
// 2 ground instances tried; 7 items in list
// 3 ground instances tried; 10 items in list
// 4 ground instances tried; 12 items in list
// 5 ground instances tried; 13 items in list
// 6 ground instances tried; 14 items in list
// 7 ground instances tried; 15 items in list
// 8 ground instances tried; 16 items in list
// 8 ground instances tried; 16 items in list
// 9 ground instances tried; 18 items in list
// 10 ground instances tried; 20 items in list
// 11 ground instances tried; 22 items in list
// 12 ground instances tried; 24 items in list
// 13 ground instances tried; 26 items in list
// 14 ground instances tried; 28 items in list
// 15 ground instances tried; 30 items in list
// 16 ground instances tried; 32 items in list
// 17 ground instances tried; 35 items in list
// 18 ground instances tried; 37 items in list
//
// val p20 : int * int = (2, 19)
let p20c = compare (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
//
// val p24 : int * int = (1, 1)
let p24c = compare (parse "~(exists x. U(x) /\ Q(x)) /\ (forall x. P(x) ==> Q(x) \/ R(x)) /\ ~(exists x. P(x) ==> (exists x. Q(x))) /\ (forall x. Q(x) /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
//
// val p39 : int * int = (1, 1)
let p39c = compare (parse "~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 5 items in list
// 1 ground instances tried; 5 items in list
// 2 ground instances tried; 8 items in list
//
// val p42 : int * int = (2, 3)
let p42c = compare (parse "~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

//**** Too slow?

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 7 items in list
// 2 ground instances tried; 10 items in list
// 3 ground instances tried; 18 items in list
// 4 ground instances tried; 24 items in list
// 5 ground instances tried; 32 items in list
// 6 ground instances tried; 38 items in list
// 7 ground instances tried; 43 items in list
// 8 ground instances tried; 46 items in list
// 8 ground instances tried; 46 items in list
// 9 ground instances tried; 48 items in list
// 10 ground instances tried; 51 items in list
// 11 ground instances tried; 54 items in list
// 12 ground instances tried; 57 items in list
// 13 ground instances tried; 63 items in list
// 14 ground instances tried; 69 items in list
// 15 ground instances tried; 75 items in list
// 16 ground instances tried; 81 items in list
// 17 ground instances tried; 89 items in list
// 18 ground instances tried; 95 items in list
// 19 ground instances tried; 103 items in list
// 20 ground instances tried; 109 items in list
// 21 ground instances tried; 117 items in list
// 22 ground instances tried; 123 items in list
// 23 ground instances tried; 131 items in list
// 24 ground instances tried; 137 items in list
// 25 ground instances tried; 143 items in list
//
// val p43 : int * int = (2, 26)
let p43c = compare (parse "(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)");;

// *****//

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 7 items in list
// 1 ground instances tried; 7 items in list
// 2 ground instances tried; 13 items in list
//
// val p44 : int * int = (2, 3)
let p44c = compare (parse "(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ (exists y. G(y) /\ ~H(x,y))) /\ (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> (exists x. J(x) /\ ~P(x))");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 3 items in list
// 1 ground instances tried; 3 items in list
//
// val p59 : int * int = (2, 2)
let p59c = compare (parse "(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 8 items in list
// 2 ground instances tried; 11 items in list
// 3 ground instances tried; 17 items in list
// 4 ground instances tried; 19 items in list
// 4 ground instances tried; 19 items in list
// 5 ground instances tried; 22 items in list
// 6 ground instances tried; 25 items in list
// 7 ground instances tried; 28 items in list
// 8 ground instances tried; 31 items in list
// 9 ground instances tried; 33 items in list
// 10 ground instances tried; 35 items in list
// 11 ground instances tried; 37 items in list
// 12 ground instances tried; 39 items in list
//
// val p60 : int * int = (1, 13)
let p60c = compare (parse "forall x. P(x,f(x)) <=> exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// pg. 178
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
//
// val p38 : int = 4
let p38t = tab (parse "(forall x. P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> (forall x.(~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

// pg. 178
// ------------------------------------------------------------------------- //
// Example: the Andrews challenge.                                           //
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
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
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
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
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
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
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
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// 
// val p34 : int list =
//   [5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2; 4; 3;
//    3; 3; 3; 3; 4; 4; 4]
let p34s = splittab  (parse "((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> ((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y))))");;

// pg. 179
// ------------------------------------------------------------------------- //
// Another nice example from EWD 1602.                                       //
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
//
// val ewd1062 : int list = [9; 9]
let ewd1062 = splittab (parse "(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ (forall x y. x <= y ==> g(x) <= g(y))");;

// ------------------------------------------------------------------------- //
// Do all the equality-free Pelletier problems, and more, as examples.       //
// ------------------------------------------------------------------------- //

//**********

// CPU time (user): 0.000000
// val p1 : int list = []
let p1 = time splittab (parse "p ==> q <=> ~q ==> ~p");;

#time "on"
let p1t = splittab (parse "p ==> q <=> ~q ==> ~p");;
#time "off"

// CPU time (user): 0.000000
// val p2 : int list = []
let p2 = time splittab (parse "~ ~p <=> p");;

// CPU time (user): 0.000000
// val p3 : int list = []
let p3 = time splittab (parse "~(p ==> q) ==> q ==> p");;

// CPU time (user): 0.000000
// val p4 : int list = []
let p4 = time splittab (parse "~p ==> q <=> ~q ==> p");;

// CPU time (user): 0.000000
// val p5 : int list = []
let p5 = time splittab (parse "(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

let p6 = time splittab (parse "p \/ ~p");;

let p7 = time splittab (parse "p \/ ~ ~ ~p");;

let p8 = time splittab (parse "((p ==> q) ==> p) ==> p");;

let p9 = time splittab (parse "(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

let p10 = time splittab (parse "(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

let p11 = time splittab (parse "p <=> p");;

let p12 = time splittab (parse "((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

let p13 = time splittab (parse "p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

let p14 = time splittab (parse "(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

let p15 = time splittab (parse "p ==> q <=> ~p \/ q");;

let p16 = time splittab (parse "(p ==> q) \/ (q ==> p)");;

let p17 = time splittab (parse "p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// ------------------------------------------------------------------------- //
// Pelletier problems: monadic predicate logic.                              //
// ------------------------------------------------------------------------- //

let p18 = time splittab (parse "exists y. forall x. P(y) ==> P(x)");;

let p19 = time splittab (parse "exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

let p20 = time splittab (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p21 = time splittab (parse "(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

let p22 = time splittab (parse "(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

let p23 = time splittab (parse "(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

let p24 = time splittab (parse "~(exists x. U(x) /\ Q(x)) /\ (forall x. P(x) ==> Q(x) \/ R(x)) /\ ~(exists x. P(x) ==> (exists x. Q(x))) /\ (forall x. Q(x) /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))");;

let p25 = time splittab (parse "(exists x. P(x)) /\ (forall x. U(x) ==> ~G(x) /\ R(x)) /\ (forall x. P(x) ==> G(x) /\ U(x)) /\ ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> (exists x. Q(x) /\ P(x))");;

let p26 = time splittab (parse "((exists x. P(x)) <=> (exists x. Q(x))) /\ (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))");;

let p27 = time splittab (parse "(exists x. P(x) /\ ~Q(x)) /\ (forall x. P(x) ==> R(x)) /\ (forall x. U(x) /\ V(x) ==> P(x)) /\ (exists x. R(x) /\ ~Q(x))  ==> (forall x. U(x) ==> ~R(x)) ==> (forall x. U(x) ==> ~V(x))");;

let p28 = time splittab (parse "(forall x. P(x) ==> (forall x. Q(x))) /\ ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> (forall x. P(x) /\ L(x) ==> M(x))");;

let p29 = time splittab (parse "(exists x. P(x)) /\ (exists x. G(x)) ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

let p30 = time splittab (parse "(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==> (forall x. U(x))");;

let p31 = time splittab (parse "~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ (forall x. ~H(x) ==> J(x)) ==> (exists x. Q(x) /\ J(x))");;

let p32 = time splittab (parse "(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ (forall x. Q(x) /\ H(x) ==> J(x)) /\ (forall x. R(x) ==> H(x)) ==> (forall x. P(x) /\ R(x) ==> J(x))");;

let p33 = time splittab (parse "(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

let p34 = time splittab (parse "((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> ((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y))))");;

let p35 = time splittab (parse "exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// ------------------------------------------------------------------------- //
// Full predicate logic (without identity and functions).                    //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// CPU time (user): 0.000000
//
// val p36 : int list = [6]
let p36 = time splittab (parse "(forall x. exists y. P(x,y)) /\ (forall x. exists y. G(x,y)) /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))  ==> (forall x. exists y. H(x,y))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
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
// CPU time (user): 0.015625
//
// val p37 : int list = [4; 9]
let p37 = time splittab (parse "(forall z. exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ (P(y,w) ==> (exists u. Q(u,w)))) /\ (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> (forall x. exists y. R(x,y))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// CPU time (user): 0.031250
//
// val p38 : int list = [3; 3; 3; 4]
let p38 = time splittab (parse "(forall x. P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> (forall x. (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

// Searching with depth limit 0
// Searching with depth limit 1
// CPU time (user): 0.000000
//
// val p39 : int list = [1]
let p39 = time splittab (parse "~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.000000
//
// val p40 : int list = [3]
let p40 = time splittab (parse "(exists y. forall x. P(x,y) <=> P(x,x)) ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.000000
//
// val p41 : int list = [3]
let p41 = time splittab (parse "(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) ==> ~(exists z. forall x. P(x,z))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.000000
//
// val p42 : int list = [3]
let p42 = time splittab (parse "~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

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
// Searching with depth limit 5
// CPU time (user): 0.765625
//
// val p43 : int list = [5; 5]
let p43 = time splittab (parse "(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.000000
//
// val p44 : int list = [3]
let p44 = time splittab (parse "(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ (exists y. G(y) /\ ~H(x,y))) /\ (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> (exists x. J(x) /\ ~P(x))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// CPU time (user): 0.015625
//
// val p45 : int list = [5]
let p45 = time splittab (parse "(forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\ ~(exists y. L(y) /\ R(y)) /\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 0
// Searching with depth limit 1
// CPU time (user): 0.031250
//
// val p46 : int list = [4; 1]
let p46 = time splittab (parse "(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ ((exists x. P(x) /\ ~G(x)) ==> (exists x. P(x) /\ ~G(x) /\ (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> (forall x. P(x) ==> G(x))");;

// ------------------------------------------------------------------------- //
// Well-known "Agatha" example; cf. Manthey and Bry, CADE-9.                 //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// CPU time (user): 0.187500
//
// val p55 : int list = [6; 6]
let p55 = time splittab (parse "lives(agatha) /\ lives(butler) /\ lives(charles) /\ (killed(agatha,agatha) \/ killed(butler,agatha) \/ killed(charles,agatha)) /\ (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\ (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\ (hates(agatha,agatha) /\ hates(agatha,charles)) /\ (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\ (forall x. hates(agatha,x) ==> hates(butler,x)) /\ (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) ==> killed(agatha,agatha) /\ ~killed(butler,agatha) /\ ~killed(charles,agatha)");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.000000
//
// val p57 : int list = [3]
let p57 = time splittab (parse "P(f((a),b),f(b,c)) /\ P(f(b,c),f(a,c)) /\ (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) ==> P(f(a,b),f(a,c))");;

// ------------------------------------------------------------------------- //
// See info-hol, circa 1500.                                                 //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// CPU time (user): 0.015625
//
// val p58 : int list = [4]
let p58 = time splittab (parse "forall P Q R. forall x. exists v. exists w. forall y. forall z. ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.000000
//
// val p59 : int list = [3]
let p59 = time splittab (parse "(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 0
// Searching with depth limit 1
// CPU time (user): 0.000000
//
// val p60 : int list = [1; 1]
let p60 = time splittab (parse "forall x. P(x,f(x)) <=> exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// ------------------------------------------------------------------------- //
// From Gilmore's classic paper.                                             //
// ------------------------------------------------------------------------- //

//**** This is still too hard for us! Amazing...

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
//
// Process is terminated due to StackOverflowException.
let gilmore_1 = time splittab (parse "exists x. forall y z. ((F(y) ==> G(y)) <=> F(x)) /\ ((F(y) ==> H(y)) <=> G(x)) /\ (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) ==> F(z) /\ G(z) /\ H(z)");;

// *****//

//** This is not valid, according to Gilmore

let gilmore_2 = time splittab (parse "exists x y. forall z. (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) ==> (F(x,y) <=> F(x,z))");;

// **//

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.156250
//
// val gilmore_3 : int list = [3]
let gilmore_3 = time splittab (parse "exists x. forall y z. ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> H(z)) /\ F(x,y) ==> F(z,z)");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// CPU time (user): 5.531250
//
// val gilmore_4 : int list = [7]
let gilmore_4 = time splittab (parse "exists x y. forall z. (F(x,y) ==> F(y,z) /\ F(z,z)) /\ (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// CPU time (user): 0.015625
//
// val gilmore_5 : int list = [4]
let gilmore_5 = time splittab (parse "(forall x. exists y. F(x,y) \/ F(y,x)) /\ (forall x y. F(y,x) ==> F(y,y)) ==> exists z. F(z,z)");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// CPU time (user): 0.000000
//
// val gilmore_6 : int list = [3]
let gilmore_6 = time splittab (parse "forall x. exists y. (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// CPU time (user): 0.000000
//
// val gilmore_7 : int list = [4]
let gilmore_7 = time splittab (parse "(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) ==> exists v w. K(v) /\ L(w) /\ G(v,w)");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// CPU time (user): 0.171875
//
// val gilmore_8 : int list = [7]
let gilmore_8 = time splittab (parse "exists x. forall y z. ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ F(x,y) ==> F(z,z)");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// CPU time (user): 0.250000
//
// val gilmore_9 : int list = [6]
let gilmore_9 = time splittab (parse "forall x. exists y. forall z. ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))");;

// ------------------------------------------------------------------------- //
// Example from Davis-Putnam papers where Gilmore procedure is poor.         //
// ------------------------------------------------------------------------- //

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// CPU time (user): 5.546875
//
// val davis_putnam_example : int list = [7]
let davis_putnam_example = time splittab (parse "exists x. exists y. forall z. (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

//************//




