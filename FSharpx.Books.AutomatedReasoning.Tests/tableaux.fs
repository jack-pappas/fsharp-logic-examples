// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.tableaux

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.herbrand
open FSharpx.Books.AutomatedReasoning.tableaux

open NUnit.Framework
open FsUnit

// pg. 175
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// tableaux.p001
// Pelletier #20
[<TestCase(
    @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==>
    R(z) /\ U(w)) ==>
    (exists x y. P(x) /\ Q(y)) ==>
    (exists z. R(z))",
    Result = 2,
    TestName = "Pelletier #20"
    )>]

let ``1 Prawitz`` f =
    parse f
    |> prawitz

// tableaux.p002
// Pelletier #19
[<TestCase(@"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", 3, 3, TestName = "Pelletier #19")>]
// tableaux.p003
// Pelletier #20
[<TestCase(@"(forall x y. exists z. forall w. P(x) /\ Q(y) 
            ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", 2, 19, TestName = "Pelletier #20")>]
// tableaux.p004
// Pelletier #24
[<TestCase(@"~(exists x. U(x) /\ Q(x)) /\ 
            (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
            ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
            (forall x. Q(x) /\ R(x) ==> U(x)) 
            ==> (exists x. P(x) /\ R(x))", 1, 1, TestName = "Pelletier #24")>]
// tableaux.p005
// Pelletier #39
[<TestCase(@"~(exists x. forall y. P(y,x) <=> ~P(y,y))", 1, 1, TestName = "Pelletier #39")>]
// tableaux.p006
// Pelletier #42
[<TestCase(@"~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", 2, 3, TestName = "Pelletier #42")>]
// tableaux.p007
// Pelletier #43
[<TestCase(@"(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)", 2, 26, TestName = "Pelletier #43")>]
// tableaux.p008
// Pelletier #44
[<TestCase(@"(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
            (exists y. G(y) /\ ~H(x,y))) /\ 
            (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) 
            ==> (exists x. J(x) /\ ~P(x))", 2, 3, TestName = "Pelletier #44")>]
// tableaux.p009
// Pelletier #59
[<TestCase(@"(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", 2, 2, TestName = "Pelletier #59")>]
// tableaux.p010
// Pelletier #60
[<TestCase(@"forall x. P(x,f(x)) <=> 
                exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", 1, 13, TestName = "Pelletier #60")>]

let ``2 Comparison of number of ground instances`` (f, x, y) =
    compare (parse f)
    |> should equal (x, y)

// pg. 178
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// tableaux.p011
// Pelletier #38
[<TestCase(
    @"(forall x. 
            P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
        (forall x. 
            (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
            (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))))",
    Result = 4,
    TestName = "Pelletier #38"
    )>]

let ``3 tableaux`` f =
    parse f
    |> tab

// Note: tableaux.p012 is also tableaux.p047

// tableaux.p013
// Dijkstra #1
[<TestCase(@"
    (forall x. x <= x) /\ 
    (forall x y z. x <= y /\ y <= z ==> x <= z) /\ 
    (forall x y. f(x) <= y <=> x <= g(y)) 
    ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ 
        (forall x y. x <= y ==> g(x) <= g(y))", Result = [|9; 9|], TestName = "Dijkstra #1")>]
// tableaux.p014
// Pelletier #01
[<TestCase(@"
    p ==> q <=> ~q ==> ~p", Result = [||], TestName = "Pelletier #01")>]
// tableaux.p015
// Pelletier #02
[<TestCase(@"
    ~ ~p <=> p", Result = [||], TestName = "Pelletier #02")>]
// tableaux.p016
// Pelletier #03
[<TestCase(@"
    ~(p ==> q) ==> q ==> p", Result = [||], TestName = "Pelletier #03")>]
// tableaux.p017
// Pelletier #04
[<TestCase(@"
    ~p ==> q <=> ~q ==> p", Result = [||], TestName = "Pelletier #04")>]
// tableaux.p018
// Pelletier #05
[<TestCase(@"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)", Result = [||], TestName = "Pelletier #05")>]
// tableaux.p019
// Pelletier #06
[<TestCase(@"
    p \/ ~p", Result = [||], TestName = "Pelletier #06")>]
// tableaux.p020
// Pelletier #07
[<TestCase(@"
    p \/ ~ ~ ~p", Result = [||], TestName = "Pelletier #07")>]
// tableaux.p021
// Pelletier #08
[<TestCase(@"
    ((p ==> q) ==> p) ==> p", Result = [||], TestName = "Pelletier #08")>]
// tableaux.p022
// Pelletier #09
[<TestCase(@"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", Result = [||], TestName = "Pelletier #09")>]
// tableaux.p023
// Pelletier #10
[<TestCase(@"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", Result = [||], TestName = "Pelletier #10")>]
// tableaux.p024
// Pelletier #11
[<TestCase(@"
    p <=> p", Result = [||], TestName = "Pelletier #11")>]
// tableaux.p025
// Pelletier #12
[<TestCase(@"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))", Result = [||], TestName = "Pelletier #12")>]
// Pelletier #13
// tableaux.p026
[<TestCase(@"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", Result = [||], TestName = "Pelletier #13")>]
// tableaux.p027
// Pelletier #14
[<TestCase(@"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", Result = [||], TestName = "Pelletier #14")>]
// tableaux.p028
// Pelletier #15
[<TestCase(@"
    p ==> q <=> ~p \/ q", Result = [||], TestName = "Pelletier #15")>]
// tableaux.p029
// Pelletier #16
[<TestCase(@"
    (p ==> q) \/ (q ==> p)", Result = [||], TestName = "Pelletier #16")>]
// tableaux.p030
// Pelletier #17
[<TestCase(@"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", Result = [||], TestName = "Pelletier #17")>]
// tableaux.p031
// Pelletier #18
[<TestCase(@"
    exists y. forall x. P(y) ==> P(x)", Result = [| 2 |], TestName = "Pelletier #18")>]
// tableaux.p032
// Pelletier #19
[<TestCase(@"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", Result = [| 2 |], TestName = "Pelletier #19")>]
// tableaux.p033
// Pelletier #20
[<TestCase(@"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", Result = [| 4 |], TestName = "Pelletier #20")>]
// tableaux.p034
// Pelletier #21
[<TestCase(@"
    (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", Result = [| 1; 2; 1 |], TestName = "Pelletier #21")>]
// tableaux.p035
// Pelletier #22
[<TestCase(@"
    (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", Result = [| 1; 2 |], TestName = "Pelletier #22")>]
// tableaux.p036
// Pelletier #23
[<TestCase(@"
    (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", Result = [| 1; 1 |], TestName = "Pelletier #23")>]
// tableaux.p037
// Pelletier #24
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", Result = [| 4 |], TestName = "Pelletier #24")>]
// tableaux.p038
// Pelletier #25
[<TestCase(@"
    (exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))", Result = [| 2; 3 |], TestName = "Pelletier #25")>]
// tableaux.p039
// Pelletier #26
[<TestCase(@"
    ((exists x. P(x)) <=> (exists x. Q(x))) /\
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
    ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))", Result = [| 3; 3; 1; 2 |], TestName = "Pelletier #26")>]
// tableaux.p040
// Pelletier #27
[<TestCase(@"
    (exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))", Result = [| 3 |], TestName = "Pelletier #27")>]
// tableaux.p041
// Pelletier #28
[<TestCase(@"
    (forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))", Result = [| 1; 1; 3; 1 |], TestName = "Pelletier #28")>]
// tableaux.p042
// Pelletier #29
[<TestCase(@"
    (exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", Result = [| 2; 2; 1; 2 |], TestName = "Pelletier #29")>]
// tableaux.p043
// Pelletier #30
[<TestCase(@"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))", Result = [| 2 |], TestName = "Pelletier #30")>]
// tableaux.p044
// Pelletier #31
[<TestCase(@"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))", Result = [| 3 |], TestName = "Pelletier #31")>]
// tableaux.p045
// Pelletier #32
[<TestCase(@"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))", Result = [| 3 |], TestName = "Pelletier #32")>]
// tableaux.p046
// Pelletier #33
[<TestCase(@"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", Result = [| 1; 1; 1 |], TestName = "Pelletier #33")>]

// tableaux.p047
// Pelletier #34
[<TestCase(@"
    ((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))",
   Result = [| 5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2;4; 3; 3; 3; 3; 3; 4; 4; 4 |],
   TestName = "Pelletier #34")>]

// tableaux.p048
// Pelletier #35
[<TestCase(@"
    exists x y. P(x,y) ==> (forall x y. P(x,y))", Result = [| 2 |], TestName = "Pelletier #35")>]
// tableaux.p049
// Pelletier #36
[<TestCase(@"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", Result = [| 6 |], TestName = "Pelletier #36")>]
// tableaux.p050
// Pelletier #37
[<TestCase(@"
    (forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", Result = [| 4; 9 |], TestName = "Pelletier #37")>]
// tableaux.p051
// Pelletier #38
[<TestCase(@"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))", Result = [| 3; 3; 3; 4 |], TestName = "Pelletier #38")>]
// tableaux.p052
// Pelletier #39
[<TestCase(@"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))", Result = [| 1 |], TestName = "Pelletier #39")>]
// tableaux.p053
// Pelletier #40
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", Result = [| 3 |], TestName = "Pelletier #40")>]
// tableaux.p054
// Pelletier #41
[<TestCase(@"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", Result = [| 3 |], TestName = "Pelletier #41")>]
// tableaux.p055
// Pelletier #42
[<TestCase(@"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", Result = [| 3 |], TestName = "Pelletier #42")>]
// tableaux.p056
// Pelletier #43
[<TestCase(@"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)", Result = [| 5; 5 |], TestName = "Pelletier #43")>]
// tableaux.p057
// Pelletier #44
[<TestCase(@"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", Result = [| 3 |], TestName = "Pelletier #44")>]
// tableaux.p058
// Pelletier #45
[<TestCase(@"
    (forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", Result = [| 5 |], TestName = "Pelletier #45")>]
// tableaux.p059
// Pelletier #46
[<TestCase(@"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", Result = [| 4; 1 |], TestName = "Pelletier #46")>]
// tableaux.p060
// Pelletier #55
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
        ~killed(charles,agatha)", Result = [| 6; 6 |], TestName = "Pelletier #55")>]
// tableaux.p061
// Pelletier #57
[<TestCase(@"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", Result = [| 3 |], TestName = "Pelletier #57")>]
// tableaux.p062
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
[<TestCase(@"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", Result = [| 4 |], TestName = "Pelletier #58")>]
// tableaux.p063
// Pelletier #59
[<TestCase(@"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", Result = [| 3 |], TestName = "Pelletier #59")>]
// tableaux.p064
// Pelletier #60
[<TestCase(@"
    forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", Result = [| 1; 1 |], TestName = "Pelletier #60")>]

// tableaux.p065
// Gilmore #1
[<TestCase(@"
    exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)",
    Result = [|true|], Category = "LongRunning", TestName = "Gilmore #1")>]

// tableaux.p066
// Gilmore #2 
[<TestCase(@"
    exists x y. forall z. 
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
        ==> (F(x,y) <=> F(x,z))",
    Result = [|false|], Category = "LongRunning", TestName = "Gilmore #2")>]

// tableaux.p067
// Gilmore #3
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [| 3 |], TestName = "Gilmore #3")>]

// tableaux.p068
// Gilmore #4
[<TestCase(@"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))", Result = [| 7 |], TestName = "Gilmore #4")>]

// tableaux.p069
// Gilmore #5
[<TestCase(@"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [| 4 |], TestName = "Gilmore #5")>]

// tableaux.p070
// Gilmore #6
[<TestCase(@"
    forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))", Result = [| 3 |], TestName = "Gilmore #6")>]

// tableaux.p071
// Gilmore #7
[<TestCase(@"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)", Result = [| 4 |], TestName = "Gilmore #7")>]

// tableaux.p072
// Gilmore #8
[<TestCase(@"
    exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)", Result = [| 7 |], TestName = "Gilmore #8")>]

// tableaux.p073
// Gilmore #9
[<TestCase(@"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))", Result = [| 6 |], TestName = "Gilmore #9")>]

// tableaux.p074
// Davis Putnam #1
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", Result = [| 7 |], TestName = "Davis Putnam #1")>]

let ``4 Split tableaux`` f =
    parse f
    |> splittab
    |> List.toArray
