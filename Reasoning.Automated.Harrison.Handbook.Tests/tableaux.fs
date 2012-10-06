// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.tableaux

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand
open Reasoning.Automated.Harrison.Handbook.tableaux

open NUnit.Framework
open FsUnit

// pg. 175
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

[<Test>]
let ``prawitz``() =
    prawitz (parse @"
        (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")
    |> should equal 2

[<TestCase(@"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", 3, 3)>]
[<TestCase(@"(forall x y. exists z. forall w. P(x) /\ Q(y) 
            ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", 2, 19)>]
[<TestCase(@"~(exists x. U(x) /\ Q(x)) /\ 
            (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
            ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
            (forall x. Q(x) /\ R(x) ==> U(x)) 
            ==> (exists x. P(x) /\ R(x))", 1, 1)>]
[<TestCase(@"~(exists x. forall y. P(y,x) <=> ~P(y,y))", 1, 1)>]
[<TestCase(@"~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", 2, 3)>]
[<TestCase(@"(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)", 2, 26)>]
[<TestCase(@"(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
            (exists y. G(y) /\ ~H(x,y))) /\ 
            (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) 
            ==> (exists x. J(x) /\ ~P(x))", 2, 3)>]
[<TestCase(@"(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", 2, 2)>]
[<TestCase(@"forall x. P(x,f(x)) <=> 
                exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", 1, 13)>]
let ``compare`` (f, x, y) =
    compare (parse f)
    |> should equal (x, y)

// pg. 178
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``tab``() =
    tab (parse @"
	    (forall x. 
            P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
        (forall x. 
            (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
            (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))))")
    |> should equal 4

let private results = [|
                        [5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2; 4; 3; 3; 3;
                         3; 3; 4; 4; 4]; // 0
                        [9; 9]; // 1
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
                        []; // 18
                        [2]; // 19
                        [2]; // 20
                        [4]; // 21
                        [1; 2; 1]; // 22
                        [1; 2]; // 23
                        [1; 1]; // 24
                        [4]; // 25
                        [2; 3]; // 26
                        [2; 3]; // 27
                        [3]; // 28
                        [3]; // 29
                        [2; 2; 1; 2]; // 30
                        [2]; // 31
                        [3]; // 32
                        [3]; // 33
                        [1; 1; 1]; // 34
                        [5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2; 4; 3; 3; 3;
                         3; 3; 4; 4; 4]; // 35
                        [2]; // 36
                        [6]; // 37
                        [4; 9]; // 38
                        [3; 3; 3; 4]; // 39
                        [1]; // 40
                        [3]; // 41
                        [3]; // 42
                        [3]; // 43
                        [5; 5]; // 44
                        [3]; // 45
                        [5]; // 46
                        [4; 1]; // 47
                        [6; 6]; // 48
                        [3]; // 49
                        [4]; // 50
                        [3]; // 51
                        [1; 1]; // 52
                        [3]; // 53
                        [3]; // 54
                        [4]; // 55
                        [4]; // 56
                        [4]; // 57
                        [4]; // 58
                        [6]; // 59
                        [7]; // 60
                            |]

[<TestCase(@"
    (forall x. x <= x) /\ 
    (forall x y z. x <= y /\ y <= z ==> x <= z) /\ 
    (forall x y. f(x) <= y <=> x <= g(y)) 
    ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ 
        (forall x y. x <= y ==> g(x) <= g(y))", 1)>]
[<TestCase(@"
	p ==> q <=> ~q ==> ~p", 2)>]
[<TestCase(@"
	~ ~p <=> p", 3)>]
[<TestCase(@"
	~(p ==> q) ==> q ==> p", 4)>]
[<TestCase(@"
	~p ==> q <=> ~q ==> p", 5)>]
[<TestCase(@"
	(p \/ q ==> p \/ r) ==> p \/ (q ==> r)", 6)>]
[<TestCase(@"
	p \/ ~p", 7)>]
[<TestCase(@"
	p \/ ~ ~ ~p", 8)>]
[<TestCase(@"
	((p ==> q) ==> p) ==> p", 9)>]
[<TestCase(@"
	(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", 10)>]
[<TestCase(@"
	(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", 11)>]
[<TestCase(@"
	p <=> p", 12)>]
[<TestCase(@"
	((p <=> q) <=> r) <=> (p <=> (q <=> r))", 13)>]
[<TestCase(@"
	p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", 14)>]
[<TestCase(@"
	(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", 15)>]
[<TestCase(@"
	p ==> q <=> ~p \/ q", 16)>]
[<TestCase(@"
	(p ==> q) \/ (q ==> p)", 17)>]
[<TestCase(@"
	p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", 18)>]
[<TestCase(@"
	exists y. forall x. P(y) ==> P(x)", 19)>]
[<TestCase(@"
	exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", 20)>]
[<TestCase(@"
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", 21)>]
[<TestCase(@"
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", 22)>]
[<TestCase(@"
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", 23)>]
[<TestCase(@"
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", 24)>]
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", 25)>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", 26)>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", 27)>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", 28)>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", 29)>]
[<TestCase(@"
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", 30)>]
[<TestCase(@"
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))", 31)>]
[<TestCase(@"
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))", 32)>]
[<TestCase(@"
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))", 33)>]
[<TestCase(@"
	(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", 34)>]
[<TestCase(@"
	exists x y. P(x,y) ==> (forall x y. P(x,y))", 36)>]
[<TestCase(@"
	(forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", 37)>]
[<TestCase(@"
	(forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", 38)>]
[<TestCase(@"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))", 39)>]
[<TestCase(@"
	~(exists x. forall y. P(y,x) <=> ~P(y,y))", 40)>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", 41)>]
[<TestCase(@"
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", 42)>]
[<TestCase(@"
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", 43)>]
[<TestCase(@"
	(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)", 44)>]
[<TestCase(@"
	(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", 45)>]
[<TestCase(@"
	(forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", 46)>]
[<TestCase(@"
	(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", 47)>]
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
        ~killed(charles,agatha)", 48)>]
[<TestCase(@"
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", 49)>]
[<TestCase(@"
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", 50)>]
[<TestCase(@"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", 51)>]
[<TestCase(@"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", 52)>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", 53)>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", 54)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 55)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 56)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 57)>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", 58)>]
[<TestCase(@"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))", 59)>]

let ``splittab all`` (f, idx) =
    splittab (parse f)
    |> should equal results.[idx]

[<TestCase(@"
	((exists x. forall y. P(x) <=> P(y)) <=> 
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> 
    ((exists x. forall y. Q(x) <=> Q(y)) <=> 
     ((exists x. P(x)) <=> (forall y. P(y))))", 0); Category("LongRunning")>]
[<TestCase(@"
	((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))", 35)>]
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", 60)>]
let ``splittab slow`` (f, idx) =
    splittab (parse f)
    |> should equal results.[idx]

