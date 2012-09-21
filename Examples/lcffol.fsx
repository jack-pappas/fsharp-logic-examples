//  Copyright (c) 2003-2007, John Harrison
//  All rights reserved.
//  
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the following disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the following disclaimer in the
//  IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
//  By downloading, copying, installing or using the software you agree
//  to this license.  If you do not agree to this license, do not
//  download, install, copy or use the software.
//  
//  Copyright (c) 2003-2007, John Harrison
//  All rights reserved.
//  
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the following disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the following disclaimer in the
//  documentation and/or other materials provided with the distribution.
//  
//  * The name of John Harrison may not be used to endorse or promote
//  products derived from this software without specific prior written
//  permission.
//  
//  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
//  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
//  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
//  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
//  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
//  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
//  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
//  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
//  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
//  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
//  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
//  SUCH DAMAGE.
// 
//  ===================================================================
// 
//  Converted to F# 2.0
// 
//  Copyright (c) 2012, Eric Taucher
//  All rights reserved.
// 
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  
//  * Redistributions of source code must retain the above copyright
//  notice, this list of conditions and the previous disclaimer.
//  
//  * Redistributions in binary form must reproduce the above copyright
//  notice, this list of conditions and the previous disclaimer in the
//  documentation and/or other materials provided with the distribution.
//  
//  * The name of Eric Taucher may not be used to endorse or promote
//  products derived from this software without specific prior written
//  permission.
// 
//  ===================================================================

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
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
//open Reasoning.Automated.Harrison.Handbook.paramodulation
//open Reasoning.Automated.Harrison.Handbook.decidable
//open Reasoning.Automated.Harrison.Handbook.qelim
//open Reasoning.Automated.Harrison.Handbook.cooper
//open Reasoning.Automated.Harrison.Handbook.complex
//open Reasoning.Automated.Harrison.Handbook.real
//open Reasoning.Automated.Harrison.Handbook.grobner
//open Reasoning.Automated.Harrison.Handbook.geom
//open Reasoning.Automated.Harrison.Handbook.interpolation
//open Reasoning.Automated.Harrison.Handbook.combining
//open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
//open Reasoning.Automated.Harrison.Handbook.folderived
open Reasoning.Automated.Harrison.Handbook.lcffol

// pg. 501

// TODO: Fix this: System.Exception: lcftab: no proof
lcfrefute (parse "p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))") 1 simpcont;;

lcfrefute (parse "(exists x. ~p(x)) /\ (forall x. p(x))") 1 simpcont;;

// pg. 504
//  ------------------------------------------------------------------------- // 
//  Examples in the text.                                                     // 
//  ------------------------------------------------------------------------- // 

let p58 = lcffol (parse "forall x. exists v. exists w. forall y. forall z. ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

let ewd1062_1 = lcffol (parse "(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> f(x) <= f(y))");;

//  ------------------------------------------------------------------------- // 
//  More exhaustive set of tests not in the main text.                        // 
//  ------------------------------------------------------------------------- // 

let start_time = System.DateTime.Now;;;

let p001 = time lcftaut (parse "p ==> q <=> ~q ==> ~p");;

let p002 = time lcftaut (parse "~ ~p <=> p");;

let p003 = time lcftaut (parse "~(p ==> q) ==> q ==> p");;

let p004 = time lcftaut (parse "~p ==> q <=> ~q ==> p");;

let p005 = time lcftaut (parse "(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

let p006 = time lcftaut (parse "p \/ ~p");;

let p007 = time lcftaut (parse "p \/ ~ ~ ~p");;

let p008 = time lcftaut (parse "((p ==> q) ==> p) ==> p");;

let p009 = time lcftaut (parse "(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

let p010 = time lcftaut (parse "(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

let p011 = time lcftaut (parse "p <=> p");;

let p012 = time lcftaut (parse "((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

let p013 = time lcftaut (parse "p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

let p014 = time lcftaut (parse "(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

let p015 = time lcftaut (parse "p ==> q <=> ~p \/ q");;

let p016 = time lcftaut (parse "(p ==> q) \/ (q ==> p)");;

let p017 = time lcftaut (parse "p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

let p101 = time lcffol (parse "p ==> q <=> ~q ==> ~p");;

let p102 = time lcffol (parse "~ ~p <=> p");;

let p103 = time lcffol (parse "~(p ==> q) ==> q ==> p");;

let p104 = time lcffol (parse "~p ==> q <=> ~q ==> p");;

let p105 = time lcffol (parse "(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

let p106 = time lcffol (parse "p \/ ~p");;

let p107 = time lcffol (parse "p \/ ~ ~ ~p");;

let p108 = time lcffol (parse "((p ==> q) ==> p) ==> p");;

let p109 = time lcffol (parse "(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

let p110 = time lcffol (parse "(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

let p111 = time lcffol (parse "p <=> p");;

let p112 = time lcffol (parse "((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

let p113 = time lcffol (parse "p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

let p114 = time lcffol (parse "(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

let p115 = time lcffol (parse "p ==> q <=> ~p \/ q");;

let p116 = time lcffol (parse "(p ==> q) \/ (q ==> p)");;

let p117 = time lcffol (parse "p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

let p118 = time lcffol (parse "exists y. forall x. P(y) ==> P(x)");;

let p119 = time lcffol (parse "exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

let p120 = time lcffol (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p121 = time lcffol (parse "(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

let p122 = time lcffol (parse "(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

let p123 = time lcffol (parse "(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

let p124 = time lcffol (parse "~(exists x. U(x) /\ Q(x)) /\ (forall x. P(x) ==> Q(x) \/ R(x)) /\ ~(exists x. P(x) ==> (exists x. Q(x))) /\ (forall x. Q(x) /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))");;

let p125 = time lcffol (parse "(exists x. P(x)) /\ (forall x. U(x) ==> ~G(x) /\ R(x)) /\ (forall x. P(x) ==> G(x) /\ U(x)) /\ ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> (exists x. Q(x) /\ P(x))");;

let p126 = time lcffol (parse "((exists x. P(x)) <=> (exists x. Q(x))) /\ (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))");;

let p127 = time lcffol (parse "(exists x. P(x) /\ ~Q(x)) /\ (forall x. P(x) ==> R(x)) /\ (forall x. U(x) /\ V(x) ==> P(x)) /\ (exists x. R(x) /\ ~Q(x)) ==> (forall x. U(x) ==> ~R(x)) ==> (forall x. U(x) ==> ~V(x))");;

let p128 = time lcffol (parse "(forall x. P(x) ==> (forall x. Q(x))) /\ ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> (forall x. P(x) /\ L(x) ==> M(x))");;

let p129 = time lcffol (parse "(exists x. P(x)) /\ (exists x. G(x)) ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

let p130 = time lcffol (parse "(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==> (forall x. U(x))");;

let p131 = time lcffol (parse "~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ (forall x. ~H(x) ==> J(x)) ==> (exists x. Q(x) /\ J(x))");;

let p132 = time lcffol (parse "(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ (forall x. Q(x) /\ H(x) ==> J(x)) /\ (forall x. R(x) ==> H(x)) ==> (forall x. P(x) /\ R(x) ==> J(x))");;

let p133 = time lcffol (parse "(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

// **** NEWLY HARD
let p134 = time lcffol (parse "((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> ((exists x. forall y. Q(x) <=> Q(y)) <=>  ((exists x. P(x)) <=> (forall y. P(y))))");;

let p135 = time lcffol (parse "exists x y. P(x,y) ==> (forall x y. P(x,y))");;

let p136 = time lcffol (parse "(forall x. exists y. P(x,y)) /\ (forall x. exists y. G(x,y)) /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) ==> (forall x. exists y. H(x,y))");;

let p137 = time lcffol (parse "(forall z. exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ (P(y,w) ==> (exists u. Q(u,w)))) /\ (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> (forall x. exists y. R(x,y))");;

let p138 = time lcffol (parse "(forall x. P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> (forall x. (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

let p139 = time lcffol (parse "~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

let p140 = time lcffol (parse "(exists y. forall x. P(x,y) <=> P(x,x)) ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

let p141 = time lcffol (parse "(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) ==> ~(exists z. forall x. P(x,z))");;

let p142 = time lcffol (parse "~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// **** SEEMS HARD
let p143 = time lcffol (parse "(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)");;

let p144 = time lcffol (parse "(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ (exists y. G(y) /\ ~H(x,y))) /\ (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> (exists x. J(x) /\ ~P(x))");;

// *** SEEMS HARD
let p145 = time lcffol (parse "(forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\ ~(exists y. L(y) /\ R(y)) /\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

let p155 = time lcffol (parse "lives(agatha) /\ lives(butler) /\ lives(charles) /\ (killed(agatha,agatha) \/ killed(butler,agatha) \/ killed(charles,agatha)) /\ (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\ (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\ (hates(agatha,agatha) /\ hates(agatha,charles)) /\ (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\ (forall x. hates(agatha,x) ==> hates(butler,x)) /\ (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) ==> killed(agatha,agatha) /\ ~killed(butler,agatha) / ~killed(charles,agatha)");;

let p157 = time lcffol (parse "P(f(a,b),f(b,c)) /\ P(f(b,c),f(a,c)) /\ (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) ==> P(f(a,b),f(a,c))");;

let p158 = time lcffol (parse "forall P Q R. forall x. exists v. exists w. forall y. forall z. ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

let p159 = time lcffol (parse "(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

let p160 = time lcffol (parse "forall x. P(x,f(x)) <=> exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

let gilmore_3 = time lcffol (parse "exists x. forall y z. ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> H(z)) /\ F(x,y) ==> F(z,z)");;

let gilmore_4 = time lcffol (parse "exists x y. forall z. (F(x,y) ==> F(y,z) /\ F(z,z)) /\ (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))");;

let gilmore_5 = time lcffol (parse "(forall x. exists y. F(x,y) \/ F(y,x)) /\ (forall x y. F(y,x) ==> F(y,y)) ==> exists z. F(z,z)");;

let gilmore_6 = time lcffol (parse "forall x. exists y. (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))");;

let gilmore_7 = time lcffol (parse "(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) ==> exists v w. K(v) /\ L(w) /\ G(v,w)");;

let gilmore_8 = time lcffol (parse "exists x. forall y z. ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ F(x,y) ==> F(z,z)");;

let gilmore_9 = time lcffol (parse "forall x. exists y. forall z. ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))");;

let davis_putnam_example = time lcffol (parse "exists x. exists y. forall z. (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// duplicate of above, used for timing.
let ewd1062_1_t = time lcffol (parse "(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> f(x) <= f(y))");;

let ewd1062_2 = time lcffol (parse "(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> g(x) <= g(y))");;

let finish_time = System.DateTime.Now;
let length_time = finish_time.Subtract(start_time);;
printfn "Complete CPU time (user): %O" length_time;;

