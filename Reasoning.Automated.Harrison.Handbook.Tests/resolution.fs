// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.resolution

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.resolution

open NUnit.Framework
open FsUnit

// pg. 185
// ------------------------------------------------------------------------- //
// Simple example that works well.                                           //
// ------------------------------------------------------------------------- //

[<Test>]
let ``resolution001``() =
    resolution001 (parse @"
        exists x. exists y. forall z. 
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))")
    |> should equal [true]

// pg. 192
// ------------------------------------------------------------------------- //
// This is now a lot quicker.                                                //
// ------------------------------------------------------------------------- //

[<Test>]
let ``resolution002``() =
    resolution002 (parse @"
        exists x. exists y. forall z. 
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))")
    |> should equal [true]

let private results = [|
                        [true]; // 0
                        []; // 1
                        []; // 2
                        []; // 3
                        []; // 4
                        []; // 5
                        []; // 6
                        []; // 7
                        []; // 8
                        []; // 9
                        []; // 10
                        []; // 11
                        []; // 12
                        []; // 13
                        []; // 14
                        []; // 15
                        []; // 16
                        []; // 17
                        [true]; // 18
                        [true]; // 19
                        [true]; // 20
                        [true; true; true]; // 21
                        [true; true]; // 22
                        [true; true]; // 23
                        [true]; // 24
                        [true; true]; // 25
                        [true; true]; // 26
                        [true]; // 27
                        [true]; // 28
                        [true; true; true; true]; // 29
                        [true]; // 30
                        [true]; // 31
                        [true]; // 32
                        [true; true; true]; // 33
                        [true; true; true; true; true; true; true; true; true; true; true; true; true;
                         true; true; true; true; true; true; true; true; true; true; true; true; true;
                         true; true; true; true; true; true]; // 34
                        [true]; // 35
                        [true]; // 36
                        [true; true]; // 37
                        [true]; // 38
                        [true]; // 39
                        [true]; // 40
                        [true]; // 41
                        [true]; // 42
                        [true]; // 43
                        [true; true]; // 44
                        [true; true]; // 45
                        [true]; // 46
                        [true]; // 47
                        [true]; // 48
                        [true; true]; // 49
                        [true]; // 50
                        [true]; // 51
                        [true]; // 52
                        [true]; // 53
                        [true]; // 54
                        [true]; // 55
                        [true]; // 56
                        [true]; // 57
                            |]

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
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", 20)>]
[<TestCase(@"
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", 21)>]
[<TestCase(@"
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", 22)>]
[<TestCase(@"
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", 23)>]
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", 24)>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", 25)>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", 26)>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", 27)>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", 28)>]
[<TestCase(@"
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", 29)>]
[<TestCase(@"
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))", 30)>]
[<TestCase(@"
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))", 31)>]
[<TestCase(@"
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))", 32)>]
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
	~(exists x. forall y. P(y,x) <=> ~P(y,y))", 38)>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", 39)>]
[<TestCase(@"
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", 40)>]
[<TestCase(@"
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", 41)>]
[<TestCase(@"
	(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", 42)>]
[<TestCase(@"
	(forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", 43)>]
[<TestCase(@"
	(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", 44)>]
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
        ~killed(charles,agatha)", 45)>]
[<TestCase(@"
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", 46)>]
[<TestCase(@"
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", 47)>]
[<TestCase(@"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", 48)>]
[<TestCase(@"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", 49)>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", 51)>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", 52)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 53)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 54)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 55)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 56)>]
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", 57)>]
let ``presolution all`` (f, idx) =
    presolution (parse f)
    |> should equal results.[idx]

[<TestCase(@"
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))", 0); Category("LongRunning")>]
[<TestCase(@"
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)", 50)>]
let ``presolution slow`` (f, idx) =
    presolution (parse f)
    |> should equal results.[idx]

let private resolution_results = [|
                                    [true]; // 0
                                    []; // 1
                                    []; // 2
                                    []; // 3
                                    []; // 4
                                    []; // 5
                                    []; // 6
                                    []; // 7
                                    []; // 8
                                    []; // 9
                                    []; // 10
                                    []; // 11
                                    []; // 12
                                    []; // 13
                                    []; // 14
                                    []; // 15
                                    []; // 16
                                    []; // 17
                                    [true]; // 18
                                    [true]; // 19
                                    [true]; // 20
                                    [true; true; true]; // 21
                                    [true; true]; // 22
                                    [true; true]; // 23
                                    [true]; // 24
                                    [true; true]; // 25
                                    [true; true]; // 26
                                    [true]; // 27
                                    [true]; // 28
                                    [true; true; true; true]; // 29
                                    [true]; // 30
                                    [true]; // 31
                                    [true]; // 32
                                    [true; true; true]; // 33
                                    [true; true; true; true; true; true; true; true; true; true; true; true; true;
                                     true; true; true; true; true; true; true; true; true; true; true; true; true;
                                     true; true; true; true; true; true]; // 34
                                    [true]; // 35
                                    [true]; // 36
                                    [true; true]; // 37
                                    [true]; // 38
                                    [true]; // 39
                                    [true]; // 40
                                    [true]; // 41
                                    [true; true]; // 42
                                    [true]; // 43
                                    [true]; // 44
                                    [true]; // 45
                                    [true; true]; // 46
                                    [true]; // 47
                                    [true]; // 48
                                    [true]; // 49
                                    [true]; // 50
                                    [true]; // 51
                                    [true]; // 52
                                        |]

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
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", 20)>]
[<TestCase(@"
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", 21)>]
[<TestCase(@"
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", 22)>]
[<TestCase(@"
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", 23)>]
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", 24)>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", 25)>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", 26)>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", 27)>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", 28)>]
[<TestCase(@"
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", 29)>]
[<TestCase(@"
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))", 30)>]
[<TestCase(@"
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))", 31)>]
[<TestCase(@"
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))", 32)>]
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
	~(exists x. forall y. P(y,x) <=> ~P(y,y))", 38)>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", 39)>]
[<TestCase(@"
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", 40)>]
[<TestCase(@"
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", 41)>]
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
        ~killed(charles,agatha)", 42)>]
[<TestCase(@"
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", 43)>]
[<TestCase(@"
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", 44)>]
[<TestCase(@"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", 45)>]
[<TestCase(@"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", 46)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 48)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 49)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 50)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 51)>]
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", 52)>]
let ``resolution003 all`` (f, idx) =
    resolution003 (parse f)
    |> should equal resolution_results.[idx]

[<TestCase(@"
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)", 0); Category("LongRunning")>]
[<TestCase(@"
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)", 47)>]
let ``resolution003 slow`` (f, idx) =
    resolution003 (parse f)
    |> should equal resolution_results.[idx]

