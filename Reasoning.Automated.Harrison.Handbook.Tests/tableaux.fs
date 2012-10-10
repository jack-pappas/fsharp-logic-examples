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


[<TestCase(@"
    (forall x. x <= x) /\ 
    (forall x y z. x <= y /\ y <= z ==> x <= z) /\ 
    (forall x y. f(x) <= y <=> x <= g(y)) 
    ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ 
        (forall x y. x <= y ==> g(x) <= g(y))", Result = [|9; 9|])>]
[<TestCase(@"
	p ==> q <=> ~q ==> ~p", Result = [||])>]
[<TestCase(@"
	~ ~p <=> p", Result = [||])>]
[<TestCase(@"
	~(p ==> q) ==> q ==> p", Result = [||])>]
[<TestCase(@"
	~p ==> q <=> ~q ==> p", Result = [||])>]
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
	exists y. forall x. P(y) ==> P(x)", Result = [| 2 |])>]
[<TestCase(@"
	exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", Result = [| 2 |])>]
[<TestCase(@"
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", Result = [| 4 |])>]
[<TestCase(@"
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", Result = [| 1; 2; 1 |])>]
[<TestCase(@"
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", Result = [| 1; 2 |])>]
[<TestCase(@"
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", Result = [| 1; 1 |])>]
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", Result = [| 4 |])>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", Result = [| 2; 3 |])>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", Result = [| 2; 3 |])>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", Result = [| 3 |])>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", Result = [| 3 |])>]
[<TestCase(@"
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", Result = [| 2; 2; 1; 2 |])>]
[<TestCase(@"
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))", Result = [| 2 |])>]
[<TestCase(@"
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))", Result = [| 3 |])>]
[<TestCase(@"
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))", Result = [| 3 |])>]
[<TestCase(@"
	(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", Result = [| 1; 1; 1 |])>]
[<TestCase(@"
	exists x y. P(x,y) ==> (forall x y. P(x,y))", Result = [| 2 |])>]
[<TestCase(@"
	(forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", Result = [| 6 |])>]
[<TestCase(@"
	(forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", Result = [| 4; 9 |])>]
[<TestCase(@"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))", Result = [| 3; 3; 3; 4 |])>]
[<TestCase(@"
	~(exists x. forall y. P(y,x) <=> ~P(y,y))", Result = [| 1 |])>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", Result = [| 3 |])>]
[<TestCase(@"
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", Result = [| 3 |])>]
[<TestCase(@"
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", Result = [| 3 |])>]
[<TestCase(@"
	(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)", Result = [| 5; 5 |])>]
[<TestCase(@"
	(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", Result = [| 3 |])>]
[<TestCase(@"
	(forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", Result = [| 5 |])>]
[<TestCase(@"
	(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", Result = [| 4; 1 |])>]
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
        ~killed(charles,agatha)", Result = [| 6; 6 |])>]
[<TestCase(@"
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", Result = [| 3 |])>]
[<TestCase(@"
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", Result = [| 4 |])>]
[<TestCase(@"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", Result = [| 3 |])>]
[<TestCase(@"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", Result = [| 1; 1 |])>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [| 3 |])>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [| 3 |])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [| 4 |])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [| 4 |])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [| 4 |])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [| 4 |])>]
[<TestCase(@"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))", Result = [| 6 |])>]
[<TestCase(@"
	((exists x. forall y. P(x) <=> P(y)) <=> 
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> 
    ((exists x. forall y. Q(x) <=> Q(y)) <=> 
     ((exists x. P(x)) <=> (forall y. P(y))))",
     Result = [| 5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2; 4; 3; 3; 3; 3; 3; 4; 4; 4 |], Category = "LongRunning")>]
[<TestCase(@"
	((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))", Result = [| 5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2; 4; 3; 3; 3; 3; 3; 4; 4; 4 |], Category = "LongRunning")>]
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", Result = [| 7 |], Category = "LongRunning")>]
let ``splittab all`` f =
    parse f
    |> splittab
    |> List.toArray
