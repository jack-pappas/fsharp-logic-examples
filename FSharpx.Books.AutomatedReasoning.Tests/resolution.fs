// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.resolution

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.unif
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.resolution

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


[<TestCase(@"
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
    Result = [|true|], Category = "LongRunning")>]
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
	exists y. forall x. P(y) ==> P(x)", Result = [|true|])>]
[<TestCase(@"
	exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", Result = [|true|])>]
[<TestCase(@"
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", Result = [|true|])>]
[<TestCase(@"
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", Result = [|true; true; true|])>]
[<TestCase(@"
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", Result = [|true; true|])>]
[<TestCase(@"
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", Result = [|true; true|])>]
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", Result = [| true |])>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", Result = [|true; true|])>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", Result = [|true; true|])>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", Result = [| true |])>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", Result = [| true |])>]
[<TestCase(@"
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", Result = [|true; true; true; true|])>]
[<TestCase(@"
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))", Result = [| true |])>]
[<TestCase(@"
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))", Result = [| true |])>]
[<TestCase(@"
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))", Result = [| true |])>]
[<TestCase(@"
	(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", Result = [|true; true; true|])>]
[<TestCase(@"
	((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))",
     Result = [|true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true|])>]
[<TestCase(@"
	exists x y. P(x,y) ==> (forall x y. P(x,y))", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", Result = [|true|])>]
[<TestCase(@"
	(forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", Result = [|true; true|])>]
[<TestCase(@"
	~(exists x. forall y. P(y,x) <=> ~P(y,y))", Result = [|true|])>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", Result = [|true|])>]
[<TestCase(@"
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", Result = [|true|])>]
[<TestCase(@"
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", Result = [|true|])>]
[<TestCase(@"
	(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", Result = [|true|])>]
[<TestCase(@"
	(forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", Result = [|true|])>]
[<TestCase(@"
	(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", Result = [|true; true|])>]
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
        ~killed(charles,agatha)", Result = [|true; true|])>]
[<TestCase(@"
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", Result = [|true|] )>]
[<TestCase(@"
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", Result = [|true|] )>]
[<TestCase(@"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", Result = [|true|] )>]
[<TestCase(@"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", Result = [|true; true|])>]
[<TestCase(@"
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)",
    Result = [|true|], Category = "LongRunning")>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [|true|])>]
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", Result = [|true|])>]
let ``presolution all`` f =
    parse f
    |> presolution
    |> List.toArray


[<TestCase(@"
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)", Result = [| true |], Category = "LongRunning")>]
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
	exists y. forall x. P(y) ==> P(x)", Result = [| true |])>]
[<TestCase(@"
	exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", Result = [| true |])>]
[<TestCase(@"
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", Result = [| true |])>]
[<TestCase(@"
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", Result = [| true; true; true |])>]
[<TestCase(@"
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", Result = [| true; true |])>]
[<TestCase(@"
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", Result = [| true; true |])>]
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", Result = [| true |])>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", Result = [| true; true |])>]
[<TestCase(@"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", Result = [| true; true |])>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", Result = [| true |])>]
[<TestCase(@"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", Result = [| true |])>]
[<TestCase(@"
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", Result = [|true; true; true; true|])>]
[<TestCase(@"
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))", Result = [|true|])>]
[<TestCase(@"
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))", Result = [|true|])>]
[<TestCase(@"
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))", Result = [|true|])>]
[<TestCase(@"
	(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", Result = [|true; true; true|])>]
[<TestCase(@"
	((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))",
     Result = [|true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true|])>]
[<TestCase(@"
	exists x y. P(x,y) ==> (forall x y. P(x,y))", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", Result = [|true|])>]
[<TestCase(@"
	(forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", Result = [| true; true |])>]
[<TestCase(@"
	~(exists x. forall y. P(y,x) <=> ~P(y,y))", Result = [|true|])>]
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", Result = [|true|])>]
[<TestCase(@"
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", Result = [|true|])>]
[<TestCase(@"
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", Result = [|true|])>]
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
        ~killed(charles,agatha)", Result = [| true; true |])>]
[<TestCase(@"
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", Result = [| true |])>]
[<TestCase(@"
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", Result = [| true |])>]
[<TestCase(@"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", Result = [| true |])>]
[<TestCase(@"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", Result = [| true; true |])>]
[<TestCase(@"
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)", Result = [| true |], Category = "LongRunning")>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [|true|])>]
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", Result = [|true|])>]
let ``resolution003 all`` f =
    parse f
    |> resolution003
    |> List.toArray


