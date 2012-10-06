// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.lcffol

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
open Reasoning.Automated.Harrison.Handbook.lcffol
open NUnit.Framework
open FsUnit

// pg. 501

[<TestCase("p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))", 
                Result="|- p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x)) ==> false")>]
[<TestCase("(exists x. ~p(x)) /\ (forall x. p(x))", 
                Result="|- (exists x. ~p(x)) /\ (forall x. p(x)) ==> (~(~p(f_1)) ==> (forall x. ~(~p(x)))) ==> false")>]
let ``lcfrefute`` f =
    lcfrefute (parse f) 1 simpcont 
    |> sprint_thm

// pg. 504
//  ------------------------------------------------------------------------- // 
//  Examples in the text.                                                     // 
//  ------------------------------------------------------------------------- // 

[<TestCase( "forall x. exists v. exists w. forall y. forall z. ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
                        Result="|- forall x. exists v w. forall y z. P(x) /\ Q(y) ==> (P(v) \/ R(w)) /\ (R(z) ==> Q(v))")>]
[<TestCase("(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> f(x) <= f(y))", 
    Result="|- (forall x. x <=x) /\ (forall x y z. x <=y /\ y <=z ==> x <=z) /\ (forall x y. f(x) <=y <=> x <=g(y)) ==> (forall x y. x <=y ==> f(x) <=f(y))")>]
[<TestCase("p ==> q <=> ~q ==> ~p", 
    Result="|- p ==> q <=> ~q ==> ~p")>]
[<TestCase("~ ~p <=> p", 
    Result="|- ~(~p) <=> p")>]
[<TestCase("~(p ==> q) ==> q ==> p", 
    Result="|- ~(p ==> q) ==> q ==> p")>]
[<TestCase("~p ==> q <=> ~q ==> p", 
    Result="|- ~p ==> q <=> ~q ==> p")>]
[<TestCase("(p \/ q ==> p \/ r) ==> p \/ (q ==> r)", 
    Result="|- (p \/ q ==> p \/ r) ==> p \/ (q ==> r)")>]
[<TestCase("p \/ ~p", 
    Result="|- p \/ ~p")>]
[<TestCase("p \/ ~ ~ ~p", 
    Result="|- p \/ ~(~(~p))")>]
[<TestCase("((p ==> q) ==> p) ==> p", 
    Result="|- ((p ==> q) ==> p) ==> p")>]
[<TestCase("(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", 
    Result="|- (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)")>]
[<TestCase("(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", 
    Result="|- (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)")>]
[<TestCase("p <=> p", 
    Result="|- p <=> p")>]
[<TestCase("((p <=> q) <=> r) <=> (p <=> (q <=> r))", 
    Result="|- ((p <=> q) <=> r) <=> p <=> q <=> r")>]
[<TestCase("p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", 
    Result="|- p \/ q /\ r <=> (p \/ q) /\ (p \/ r)")>]
[<TestCase("(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", 
    Result="|- (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)")>]
[<TestCase("(p ==> q) \/ (q ==> p)", 
    Result="|- (p ==> q) \/ (q ==> p)")>]
[<TestCase("p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", 
    Result="|- p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)")>]
let ``lcffol all`` f =
    lcffol (parse f) |> sprint_thm
 
//  ------------------------------------------------------------------------- // 
//  More exhaustive set of tests not in the main text.                        // 
//  ------------------------------------------------------------------------- // 

[<TestCase("(forall x. exists y. F(x,y) \/ F(y,x)) /\ (forall x y. F(y,x) ==> F(y,y)) ==> exists z. F(z,z)", 
    Result="|- (forall x. exists y. F(x,y) \/ F(y,x)) /\ (forall x y. F(y,x) ==> F(y,y)) ==> (exists z. F(z,z))")>]
[<TestCase("forall x. exists y. (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))", 
    Result="|- forall x. exists y. (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))")>]
[<TestCase("(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) ==> exists v w. K(v) /\ L(w) /\ G(v,w)", 
    Result="|- (forall x. K(x) ==> (exists y. L(y) /\ (F(x,y) ==> G(x,y)))) /\ (exists z. K(z) /\ (forall u. L(u) ==> F(z,u))) ==> (exists v w. K(v) /\ L(w) /\ G(v,w))")>]
let ``lcffol gilmore fast`` f =
    lcffol (parse f) |> sprint_thm

[<TestCase("exists x. forall y z. ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> H(z)) /\ F(x,y) ==> F(z,z)", 
    Result="|- exists x. forall y z. ((F(y,z) ==> G(y) ==> H(x)) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> H(z)) /\ F(x,y) ==> F(z,z)"); Category("LongRunning")>]
[<TestCase("exists x y. forall z. (F(x,y) ==> F(y,z) /\ F(z,z)) /\ (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))", 
    Result="|- exists x y. forall z. (F(x,y) ==> F(y,z) /\ F(z,z)) /\ (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))"); Category("LongRunning")>]
[<TestCase("exists x. forall y z. ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ F(x,y) ==> F(z,z)", 
    Result="|- exists x. forall y z. ((F(y,z) ==> G(y) ==> (forall u. exists v. H(u,v,x))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ F(x,y) ==> F(z,z)"); Category("LongRunning")>]
[<TestCase("forall x. exists y. forall z. ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))", 
    Result="|- forall x. exists y. forall z. ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))"); Category("LongRunning")>]
let ``lcffol gilmore slow`` f =
    lcffol (parse f) |> sprint_thm

(* TODO: adding more test cases after p017, except gilmore_* *)
