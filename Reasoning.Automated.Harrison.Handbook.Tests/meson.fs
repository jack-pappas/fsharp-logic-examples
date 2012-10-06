// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.meson

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson

open NUnit.Framework
open FsUnit

// pg. 215
// ------------------------------------------------------------------------- //
// Example of naivety of tableau prover.                                     //
// ------------------------------------------------------------------------- //

// pg. 218
// ------------------------------------------------------------------------- //
// The interesting example where tableaux connections make the proof longer. //
// Unfortuntely this gets hammered by normalization first...                 //
// ------------------------------------------------------------------------- //

[<TestCase(@"forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))", Result=2)>]
[<TestCase(@"forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))", Result=0)>]
[<TestCase(@"~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
            (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
            (~s \/ ~v) /\ (~s \/ ~w) ==> false", Result=0)>]
let ``tab`` f =
    tab (parse f)

// pg. 220
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``meson002 small``() =
    meson002 (parse @"exists x. exists y. forall z. 
                        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
                        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))")
    |> should equal [8] // There is also an equal function in meson module

let private results = [|
                            [8];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [];
                            [1];
                            [2];
                            [3];
                            [2; 3; 2];
                            [2; 2];
                            [2; 1];
                            [4];
                            [2; 3];
                            [5; 5; 1; 1];
                            [5];
                            [1; 2; 2; 2];
                            [3; 2; 2; 3];
                            [4];
                            [4];
                            [7];
                            [3; 3; 3];
                            [3; 3; 3; 1; 2; 2; 2; 1; 3; 2; 2; 1; 3; 2; 2; 1; 2; 1; 2; 1; 3; 1; 2; 1; 2; 1; 2;
                            1; 1; 1; 1; 1];
                            [1];
                            [3];
                            [1; 3];
                            [12; 12; 9; 9];
                            [4];
                            [6];
                            [6];
                            [12];
                            [11; 11];
                            [6];
                            [24];
                            [12; 2];
                            [8; 3];
                            [3];
                            [3];
                            [6];
                            [2; 3];
                            [4];
                            [8];
                            [4];
                            [2];
                            [8];
                            [4];
                            [7];
                            [8];
                            [];
                         |]

[<TestCase(@"
    exists x. exists y. forall z. 
    (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
    ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", 0)>]
[<TestCase(@"
    p ==> q <=> ~q ==> ~p", 1)>]
[<TestCase(@"
    ~ ~p <=> p", 2)>]
[<TestCase(@"
    ~(p ==> q) ==> q ==> p", 3)>]
[<TestCase(@"
    ~p ==> q <=> ~q ==> p", 4)>]
[<TestCase(@"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)", 5)>]
[<TestCase(@"
    p \/ ~p", 6)>]
[<TestCase(@"
    p \/ ~ ~ ~p", 7)>]
[<TestCase(@"
    ((p ==> q) ==> p) ==> p", 8)>]
[<TestCase(@"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", 9)>]
[<TestCase(@"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", 10)>]
[<TestCase(@"
    p <=> p", 11)>]
[<TestCase(@"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))", 12)>]
[<TestCase(@"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", 13)>]
[<TestCase(@"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", 14)>]
[<TestCase(@"
    p ==> q <=> ~p \/ q", 15)>]
[<TestCase(@"
    (p ==> q) \/ (q ==> p)", 16)>]
[<TestCase(@"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", 17)>]
[<TestCase(@"
    exists y. forall x. P(y) ==> P(x)", 18)>]
[<TestCase(@"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", 19)>]
[<TestCase(@"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> 
    (exists x y. P(x) /\ Q(y)) ==> 
    (exists z. R(z))", 20)>]
[<TestCase(@"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))", 21)>]
[<TestCase(@"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", 22)>]
[<TestCase(@"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", 23)>]
[<TestCase(@"~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", 24)>]
[<TestCase(@"(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> 
    (exists x. Q(x) /\ P(x))", 25)>]
[<TestCase(@"((exists x. P(x)) <=> (exists x. Q(x))) /\ 
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> 
    ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))", 26)>]
[<TestCase(@"(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) ==> 
    (forall x. U(x) ==> ~R(x)) ==> 
    (forall x. U(x) ==> ~V(x))", 27)>]
[<TestCase(@"(forall x. P(x) ==> (forall x. Q(x))) /\ 
    ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ 
    ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> 
    (forall x. P(x) /\ L(x) ==> M(x))", 28)>]
[<TestCase(@"(exists x. P(x)) /\ (exists x. G(x)) ==>
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", 29)>]
[<TestCase(@"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> 
    P(x) /\ H(x)) ==> 
    (forall x. U(x))", 30)>]
[<TestCase(@"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) ==> 
    (exists x. Q(x) /\ J(x))", 31)>]
[<TestCase(@"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) ==> 
    (forall x. P(x) /\ R(x) ==> J(x))", 32)>]
[<TestCase(@"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", 33)>]
[<TestCase(@"
    ((exists x. forall y. P(x) <=> P(y)) <=> 
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> 
    ((exists x. forall y. Q(x) <=> Q(y)) <=> 
    ((exists x. P(x)) <=> (forall y. P(y))))", 34)>]
[<TestCase(@"
    exists x y. P(x,y) ==> (forall x y. P(x,y))", 35)>]
[<TestCase(@"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", 36)>]
[<TestCase(@"
    (forall z. 
        exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
        (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", 37)>]
[<TestCase(@"
    (forall x. 
        P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
        (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
        (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
        (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
        (exists z w. P(z) /\ R(x,w) /\ R(w,z))))", 38)>]
[<TestCase(@"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))", 39)>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x)) 
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", 40)>]
[<TestCase(@"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", 41)>]
[<TestCase(@"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", 42)>]
[<TestCase(@"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)", 43)>]
[<TestCase(@"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", 44)>]
[<TestCase(@"
    (forall x. 
        P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
            (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
        (exists x. P(x) /\ (forall y. H(x,y) ==> 
            L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", 45)>]
[<TestCase(@"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
        (exists x. P(x) /\ ~G(x) /\ 
            (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", 46)>]
[<TestCase(@"
    lives(agatha) /\ lives(butler) /\ lives(charles) /\ 
    (killed(agatha,agatha) \/ killed(butler,agatha) \/ 
        killed(charles,agatha)) /\ 
    (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\ 
    (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\ 
    (hates(agatha,agatha) /\ hates(agatha,charles)) /\ 
    (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\ 
    (forall x. hates(agatha,x) ==> hates(butler,x)) /\ 
    (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) 
    ==> killed(agatha,agatha) /\ 
        ~killed(butler,agatha) /\ 
        ~killed(charles,agatha)", 47)>]
[<TestCase(@"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", 48)>]
[<TestCase(@"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", 49)>]
[<TestCase(@"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", 50)>]
[<TestCase(@"
    forall x. P(x,f(x)) <=> 
        exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", 51)>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", 52)>]
[<TestCase(@"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))", 53)>]
[<TestCase(@"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 54)>]
[<TestCase(@"
    forall x. exists y. 
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) 
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ 
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))", 55)>]
[<TestCase(@"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ 
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) 
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)", 56)>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ 
        F(x,y) 
        ==> F(z,z)", 57)>]
[<TestCase(@"
    (forall x y. P(x,y) <=> 
        forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
    ==> forall x. exists y. forall z. 
        (P(y,x) ==> (P(x,z) ==> P(x,y))) /\ 
        (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))", 58)>]
[<TestCase(@"
    exists x. exists y. forall z. 
    (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
    ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", 59)>]
[<TestCase(@" 
    ~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
        (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
        (~s \/ ~v) /\ (~s \/ ~w) ==> false", 60)>]
let ``meson002 all`` (f, idx) =
    meson002 (parse f)
    |> should equal results.[idx]
