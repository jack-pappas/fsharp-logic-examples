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

[<TestCase(@"forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))", Result = 2)>]
[<TestCase(@"forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))", Result = 0)>]
[<TestCase(@"~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
            (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
            (~s \/ ~v) /\ (~s \/ ~w) ==> false", Result = 0)>]
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


[<TestCase(@"
    exists x. exists y. forall z. 
    (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
    ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
    Result = [| 8 |])>]
[<TestCase(@"p ==> q <=> ~q ==> ~p", Result = [||])>]
[<TestCase(@"~ ~p <=> p", Result = [||])>]
[<TestCase(@"~(p ==> q) ==> q ==> p", Result = [||])>]
[<TestCase(@"~p ==> q <=> ~q ==> p", Result = [||])>]
[<TestCase(@"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)", Result = [||])>]
[<TestCase(@"
    p \/ ~p", Result = [||])>]
[<TestCase(@"
    p \/ ~ ~ ~p", Result = [||])>]
[<TestCase(@"
    ((p ==> q) ==> p) ==> p", Result = [||])>]
[<TestCase(@"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", Result = [||])>]
[<TestCase(@"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", Result = [||])>]
[<TestCase(@"
    p <=> p", Result = [||])>]
[<TestCase(@"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))", Result = [||])>]
[<TestCase(@"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", Result = [||])>]
[<TestCase(@"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", Result = [||])>]
[<TestCase(@"
    p ==> q <=> ~p \/ q", Result = [||])>]
[<TestCase(@"
    (p ==> q) \/ (q ==> p)", Result = [||])>]
[<TestCase(@"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", Result = [||])>]
[<TestCase(@"
    exists y. forall x. P(y) ==> P(x)", Result = [| 1 |])>]
[<TestCase(@"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", Result = [| 2 |])>]
[<TestCase(@"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> 
    (exists x y. P(x) /\ Q(y)) ==> 
    (exists z. R(z))", Result = [| 3 |])>]
[<TestCase(@"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))", Result = [| 2; 3; 2 |])>]
[<TestCase(@"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", Result = [| 2; 2 |])>]
[<TestCase(@"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", Result = [| 2; 1 |])>]
[<TestCase(@"~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", Result = [| 4 |])>]
[<TestCase(@"(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> 
    (exists x. Q(x) /\ P(x))", Result = [| 2; 3 |])>]
[<TestCase(@"((exists x. P(x)) <=> (exists x. Q(x))) /\ 
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> 
    ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))", Result = [| 5; 5; 1; 1 |])>]
[<TestCase(@"(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) ==> 
    (forall x. U(x) ==> ~R(x)) ==> 
    (forall x. U(x) ==> ~V(x))", Result = [| 5 |])>]
[<TestCase(@"(forall x. P(x) ==> (forall x. Q(x))) /\ 
    ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ 
    ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> 
    (forall x. P(x) /\ L(x) ==> M(x))", Result = [| 1; 2; 2; 2 |])>]
[<TestCase(@"(exists x. P(x)) /\ (exists x. G(x)) ==>
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", Result = [| 3; 2; 2; 3 |])>]
[<TestCase(@"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> 
    P(x) /\ H(x)) ==> 
    (forall x. U(x))", Result = [| 4 |])>]
[<TestCase(@"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) ==> 
    (exists x. Q(x) /\ J(x))", Result = [| 4 |])>]
[<TestCase(@"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) ==> 
    (forall x. P(x) /\ R(x) ==> J(x))", Result = [| 7 |])>]
[<TestCase(@"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", Result = [| 3; 3; 3 |])>]
[<TestCase(@"
    ((exists x. forall y. P(x) <=> P(y)) <=> 
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> 
    ((exists x. forall y. Q(x) <=> Q(y)) <=> 
    ((exists x. P(x)) <=> (forall y. P(y))))", Result = [|3; 3; 3; 1; 2; 2; 2; 1; 3; 2; 2; 1; 3; 2; 2; 1; 2; 1; 2; 1; 3; 1; 2; 1; 2; 1; 2; 1; 1; 1; 1; 1|])>]
[<TestCase(@"
    exists x y. P(x,y) ==> (forall x y. P(x,y))", Result = [| 1 |])>]
[<TestCase(@"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", Result = [| 3 |])>]
[<TestCase(@"
    (forall z. 
        exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
        (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", Result = [| 1; 3 |])>]
[<TestCase(@"
    (forall x. 
        P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
        (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
        (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
        (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
        (exists z w. P(z) /\ R(x,w) /\ R(w,z))))", Result = [| 12; 12; 9; 9 |])>]
[<TestCase(@"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))", Result = [| 4 |])>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x)) 
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", Result = [| 6 |])>]
[<TestCase(@"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", Result = [| 6 |])>]
[<TestCase(@"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", Result = [| 6 |])>]
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
        ~killed(charles,agatha)", Result = [| 8; 3 |])>]
[<TestCase(@"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", Result = [| 3 |])>]
[<TestCase(@"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", Result = [| 3 |])>]
[<TestCase(@"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", Result = [| 6 |])>]
[<TestCase(@"
    forall x. P(x,f(x)) <=> 
        exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", Result = [| 2; 3 |])>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [| 4 |])>]
[<TestCase(@"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))", Result = [| 8 |])>]
[<TestCase(@"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [| 4 |])>]
[<TestCase(@"
    forall x. exists y. 
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) 
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ 
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))", Result = [| 2 |])>]
[<TestCase(@"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ 
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) 
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)", Result = [| 8 |])>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [| 4 |])>]
[<TestCase(@"
    (forall x y. P(x,y) <=> 
        forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
    ==> forall x. exists y. forall z. 
        (P(y,x) ==> (P(x,z) ==> P(x,y))) /\ 
        (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))", Result = [| 7 |])>]
[<TestCase(@"
    exists x. exists y. forall z. 
    (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
    ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", Result = [| 8 |])>]
[<TestCase(@" 
    ~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
        (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
        (~s \/ ~v) /\ (~s \/ ~w) ==> false", Result = [||])>]
[<TestCase(@"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", Result = [| 12 |], Category="LongRunning")>]
[<TestCase(@"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)", Result = [| 11; 11 |], Category="LongRunning")>]
[<TestCase(@"
    (forall x. 
        P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
            (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
        (exists x. P(x) /\ (forall y. H(x,y) ==> 
            L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", Result = [| 24 |], Category="LongRunning")>]
[<TestCase(@"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
        (exists x. P(x) /\ ~G(x) /\ 
            (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", Result = [| 12; 2 |], Category="LongRunning")>]
let ``meson002 all`` f =
    parse f
    |> meson002
    |> List.toArray
