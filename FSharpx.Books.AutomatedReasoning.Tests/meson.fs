// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.meson

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.prolog
open FSharpx.Books.AutomatedReasoning.meson

open NUnit.Framework
open FsUnit

// pg. 215
// ------------------------------------------------------------------------- //
// Example of naivety of tableau prover.                                     //
// ------------------------------------------------------------------------- //

// meson.p001
// Harrison #08.a
[<TestCase(@"forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))",
    Result = 2, TestName = "1 Pointless case split")>]

// meson.p002
// Harrison #08.b
[<TestCase(@"forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))",
    Result = 0, TestName = "2 No case split")>]

// pg. 218
// ------------------------------------------------------------------------- //
// The interesting example where tableaux connections make the proof longer. //
// Unfortuntely this gets hammered by normalization first...                 //
// ------------------------------------------------------------------------- //

// meson.p003
// Harrison #09
[<TestCase(@"~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
            (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
            (~s \/ ~v) /\ (~s \/ ~w) ==> false",
    Result = 0, TestName = "3 Efficient tableau proof")>]
     
let ``tableaux`` f =
    tab (parse f)

// pg. 220
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// meson.p004
// Davis Putnam #1
[<Test>]
[<TestCase(@"
    exists x. exists y. forall z. 
                        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
                        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
    Result = [| 8 |], TestName = "Davis Putnam #1")>]

// meson.p005
// Los #1
[<TestCase(@"
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
    Result = [| 20 |], Category = "LongRunning", TestName = "Los #1")>]

// meson.p006
// long running
[<TestCase(@"
    ((forall x. P1(x) ==> P0(x)) /\ (exists x. P1(x))) /\ 
    ((forall x. P2(x) ==> P0(x)) /\ (exists x. P2(x))) /\ 
    ((forall x. P3(x) ==> P0(x)) /\ (exists x. P3(x))) /\ 
    ((forall x. P4(x) ==> P0(x)) /\ (exists x. P4(x))) /\ 
    ((forall x. P5(x) ==> P0(x)) /\ (exists x. P5(x))) /\ 
    ((exists x. Q1(x)) /\ (forall x. Q1(x) ==> Q0(x))) /\ 
    (forall x. P0(x) 
                ==> (forall y. Q0(y) ==> R(x,y)) \/ 
                    ((forall y. P0(y) /\ S0(y,x) /\ 
                            (exists z. Q0(z) /\ R(y,z)) 
                                ==> R(x,y)))) /\ 
    (forall x y. P3(y) /\ (P5(x) \/ P4(x)) ==> S0(x,y)) /\ 
    (forall x y. P3(x) /\ P2(y) ==> S0(x,y)) /\ 
    (forall x y. P2(x) /\ P1(y) ==> S0(x,y)) /\ 
    (forall x y. P1(x) /\ (P2(y) \/ Q1(y)) ==> ~(R(x,y))) /\ 
    (forall x y. P3(x) /\ P4(y) ==> R(x,y)) /\ 
    (forall x y. P3(x) /\ P5(y) ==> ~(R(x,y))) /\ 
    (forall x. (P4(x) \/ P5(x)) ==> exists y. Q0(y) /\ R(x,y)) 
    ==> exists x y. P0(x) /\ P0(y) /\ 
                exists z. Q1(z) /\ R(y,z) /\ R(x,y)", Result = [| |], Category = "LongRunning", TestName = "steamroller")>]

// meson.p007
// Pelletier #01
[<TestCase(@"p ==> q <=> ~q ==> ~p", Result = [||], TestName = "Pelletier #01")>]

// meson.p008
// Pelletier #02
[<TestCase(@"~ ~p <=> p", Result = [||], TestName = "Pelletier #02")>]

// meson.p009
// Pelletier #03
[<TestCase(@"~(p ==> q) ==> q ==> p", Result = [||], TestName = "Pelletier #03")>]

// meson.p010
// Pelletier #04
[<TestCase(@"~p ==> q <=> ~q ==> p", Result = [||], TestName = "Pelletier #04")>]

// meson.p011
// Pelletier #05
[<TestCase(@"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)", Result = [||], TestName = "Pelletier #05")>]

// meson.p012
// Pelletier #06
[<TestCase(@"
    p \/ ~p", Result = [||], TestName = "Pelletier #06")>]

// meson.p013
// Pelletier #07
[<TestCase(@"
    p \/ ~ ~ ~p", Result = [||], TestName = "Pelletier #07")>]

// meson.p014
// Pelletier #08
[<TestCase(@"
    ((p ==> q) ==> p) ==> p", Result = [||], TestName = "Pelletier #08")>]

// meson.p015
// Pelletier #09
[<TestCase(@"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", Result = [||], TestName = "Pelletier #09")>]

// meson.p016
// Pelletier #10
[<TestCase(@"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", Result = [||], TestName = "Pelletier #10")>]

// meson.p017
// Pelletier #11
[<TestCase(@"
    p <=> p", Result = [||], TestName = "Pelletier #11")>]

// meson.p018
// Pelletier #12
[<TestCase(@"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))", Result = [||], TestName = "Pelletier #12")>]

// meson.p019
// Pelletier #13
[<TestCase(@"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", Result = [||], TestName = "Pelletier #13")>]

// meson.p020
// Pelletier #14
[<TestCase(@"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", Result = [||], TestName = "Pelletier #14")>]

// meson.p021
// Pelletier #15
[<TestCase(@"
    p ==> q <=> ~p \/ q", Result = [||], TestName = "Pelletier #15")>]

// meson.p022
// Pelletier #16
[<TestCase(@"
    (p ==> q) \/ (q ==> p)", Result = [||], TestName = "Pelletier #16")>]

// meson.p023
// Pelletier #17
[<TestCase(@"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", Result = [||], TestName = "Pelletier #17")>]

// meson.p024
// Pelletier #18
[<TestCase(@"
    exists y. forall x. P(y) ==> P(x)", Result = [| 1 |], TestName = "Pelletier #18")>]

// meson.p025
// Pelletier #19
[<TestCase(@"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", Result = [| 2 |], TestName = "Pelletier #19")>]

// meson.p026
// Pelletier #20
[<TestCase(@"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> 
    (exists x y. P(x) /\ Q(y)) ==> 
    (exists z. R(z))", Result = [| 3 |], TestName = "Pelletier #20")>]

// meson.p027
// Pelletier #21
[<TestCase(@"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))", Result = [| 2; 3; 2 |], TestName = "Pelletier #21")>]

// meson.p028
// Pelletier #22
[<TestCase(@"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", Result = [| 2; 2 |], TestName = "Pelletier #22")>]

// meson.p029
// Pelletier #23
[<TestCase(@"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", Result = [| 2; 1 |], TestName = "Pelletier #23")>]

// meson.p030
// Pelletier #24
[<TestCase(@"~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))", Result = [| 4 |], TestName = "Pelletier #24")>]

// meson.p031
// Pelletier #25
[<TestCase(@"(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> 
    (exists x. Q(x) /\ P(x))", Result = [| 2; 3 |], TestName = "Pelletier #25")>]

// meson.p032
// Pelletier #26
[<TestCase(@"((exists x. P(x)) <=> (exists x. Q(x))) /\ 
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> 
    ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))", Result = [| 5; 5; 1; 1 |], TestName = "Pelletier #26")>]

// meson.p033
// Pelletier #27
[<TestCase(@"(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) ==> 
    (forall x. U(x) ==> ~R(x)) ==> 
    (forall x. U(x) ==> ~V(x))", Result = [| 5 |], TestName = "Pelletier #27")>]

// meson.p034
// Pelletier #28
[<TestCase(@"(forall x. P(x) ==> (forall x. Q(x))) /\ 
    ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ 
    ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> 
    (forall x. P(x) /\ L(x) ==> M(x))", Result = [| 1; 2; 2; 2 |], TestName = "Pelletier #28")>]

// meson.p035
// Pelletier #29
[<TestCase(@"(exists x. P(x)) /\ (exists x. G(x)) ==>
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", Result = [| 3; 2; 2; 3 |], TestName = "Pelletier #29")>]

// meson.p036
// Pelletier #30
[<TestCase(@"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> 
    P(x) /\ H(x)) ==> 
    (forall x. U(x))", Result = [| 4 |], TestName = "Pelletier #30")>]

// meson.p037
// Pelletier #31
[<TestCase(@"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) ==> 
    (exists x. Q(x) /\ J(x))", Result = [| 4 |], TestName = "Pelletier #31")>]

// meson.p038
// Pelletier #32
[<TestCase(@"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) ==> 
    (forall x. P(x) /\ R(x) ==> J(x))", Result = [| 7 |], TestName = "Pelletier #32")>]

// meson.p039
// Pelletier #33
[<TestCase(@"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", Result = [| 3; 3; 3 |], TestName = "Pelletier #33")>]

// meson.p040
// Pelletier #34
[<TestCase(@"
    ((exists x. forall y. P(x) <=> P(y)) <=> 
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> 
    ((exists x. forall y. Q(x) <=> Q(y)) <=> 
    ((exists x. P(x)) <=> (forall y. P(y))))", Result = [|3; 3; 3; 1; 2; 2; 2; 1; 3; 2; 2; 1; 3; 2; 2; 1; 2; 1; 2; 1; 3; 1; 2; 1; 2; 1; 2; 1; 1; 1; 1; 1|], TestName = "Pelletier #34")>]

// meson.p041
// Pelletier #35
[<TestCase(@"
    exists x y. P(x,y) ==> (forall x y. P(x,y))", Result = [| 1 |], TestName = "Pelletier #35")>]

// meson.p042
// Pelletier #36
[<TestCase(@"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))", Result = [| 3 |], TestName = "Pelletier #36")>]

// meson.p043
// Pelletier #37
[<TestCase(@"
    (forall z. 
        exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
        (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", Result = [| 1; 3 |], TestName = "Pelletier #37")>]

// meson.p044
// Pelletier #38
[<TestCase(@"
    (forall x. 
        P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
        (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
        (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
        (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
        (exists z w. P(z) /\ R(x,w) /\ R(w,z))))", Result = [| 12; 12; 9; 9 |], TestName = "Pelletier #38")>]

// meson.p045
// Pelletier #39
[<TestCase(@"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))", Result = [| 4 |], TestName = "Pelletier #39")>]

// meson.p046
// Pelletier #40
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x)) 
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))", Result = [| 6 |], TestName = "Pelletier #40")>]

// meson.p047
// Pelletier #41
[<TestCase(@"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))", Result = [| 6 |], TestName = "Pelletier #41")>]

// meson.p048
[<TestCase(@"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", Result = [| 12 |], TestName = "Pelletier #42")>]

// meson.p049
[<TestCase(@"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)", Result = [| 11; 11 |], TestName = "Pelletier #43")>]

// meson.p050
// Pelletier #44
[<TestCase(@"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))", Result = [| 6 |], TestName = "Pelletier #44")>]

// meson.p051
[<TestCase(@"
    (forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))", Result = [| 24 |], TestName = "Pelletier #45")>]

// meson.p052
[<TestCase(@"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))", Result = [| 12; 2 |], TestName = "Pelletier #46")>]

// meson.p053
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
        ~killed(charles,agatha)", Result = [| 8; 3 |], TestName = "Pelletier #55")>]

// meson.p054
// Pelletier #57
[<TestCase(@"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))", Result = [| 3 |], TestName = "Pelletier #57")>]

// meson.p055
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
[<TestCase(@"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", Result = [| 3 |], TestName = "Pelletier #58")>]

// meson.p056
// Pelletier #59
[<TestCase(@"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", Result = [| 6 |], TestName = "Pelletier #59")>]

// meson.p057
// Pelletier #60
[<TestCase(@"
    forall x. P(x,f(x)) <=> 
        exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", Result = [| 2; 3 |], TestName = "Pelletier #60")>]

// meson.p058
[<TestCase(@"
    exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)",
    Result = [|true|], Category = "LongRunning", TestName = "Gilmore #1")>]

// meson.p059
[<TestCase(@"
    exists x y. forall z. 
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
        ==> (F(x,y) <=> F(x,z))",
    Result = [|false|], Category = "LongRunning", TestName = "Gilmore #2")>]

// meson.p060
// Gilmore #3
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [| 4 |], TestName = "Gilmore #3")>]

// meson.p061
// Gilmore #4
[<TestCase(@"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))", Result = [| 8 |], TestName = "Gilmore #4")>]

// meson.p062
// Gilmore #5
[<TestCase(@"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)", Result = [| 4 |], TestName = "Gilmore #5")>]

// meson.p063
// Gilmore #6
[<TestCase(@"
    forall x. exists y. 
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) 
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ 
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))", Result = [| 2 |], TestName = "Gilmore #6")>]

// meson.p064
// Gilmore #7
[<TestCase(@"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ 
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) 
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)", Result = [| 8 |], TestName = "Gilmore #7")>]

// meson.p065
// Gilmore #8
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ 
        F(x,y) 
        ==> F(z,z)", Result = [| 4 |], TestName = "Gilmore #8")>]

// meson.p066
[<TestCase(@"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))", Result = [| 6 |], Category = "LongRunning", TestName = "Gilmore #9")>]

// meson.p067
// Gilmore #9a
[<TestCase(@"
    (forall x y. P(x,y) <=> 
        forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
    ==> forall x. exists y. forall z. 
        (P(y,x) ==> (P(x,z) ==> P(x,y))) /\ 
        (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))", Result = [| 7 |], TestName = "Gilmore #09a")>]

// meson.p068
// Davis Putnam #1
[<TestCase(@"
    exists x. exists y. forall z. 
    (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
    ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))", Result = [| 8 |], TestName = "Davis Putnam #1")>]

// meson.p069
// Harrison #09
[<TestCase(@" 
    ~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
        (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
        (~s \/ ~v) /\ (~s \/ ~w) ==> false", Result = [||], TestName = "Harrison #09")>]

let ``meson`` f =
    parse f
    |> meson002
    |> List.toArray
