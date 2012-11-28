// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.lcffol

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop
open FSharpx.Books.AutomatedReasoning.lcffol

open NUnit.Framework
open FsUnit

// pg. 501

// lcffol.p001
// Temporary use string comparison due to a subtle bug in the parsers.
[<TestCase(@"p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))", 
                Result = "|- p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x)) ==> false")>]

// lcffol.p002
[<TestCase(@"(exists x. ~p(x)) /\ (forall x. p(x))", 
                Result = "|- (exists x. ~p(x)) /\ (forall x. p(x)) ==> (~(~p(f_1)) ==> (forall x. ~(~p(x)))) ==> false")>]

let ``lcfrefute`` f =
    lcfrefute (parse f) 1 simpcont 
    |> sprint_thm

// pg. 504
//  ------------------------------------------------------------------------- // 
//  Examples in the text.                                                     // 
//  ------------------------------------------------------------------------- // 

let private lcffol_results = [| 
                                @"forall x.
                                    exists v w.
                                    forall y z. P(x) /\ Q(y) ==> (P(v) \/ R(w)) /\ (R(z) ==> Q(v))"; // 0
                                // Dijkstra #1
                                @"(forall x. x <= x) /\
                                    (forall x y z. x <= y /\ y <= z ==> x <= z) /\
                                    (forall x y. f(x) <= y <=> x <= g(y)) ==>
                                    (forall x y. x <= y ==> f(x) <= f(y))"; // 1

                                // Pelletier #01
                                @"p ==> q <=> ~q ==> ~p"; // 2
                                @"~(~p) <=> p"; // 3
                                // Pelletier #03
                                @"~(p ==> q) ==> q ==> p"; // 4
                                // Pelletier #04
                                @"~p ==> q <=> ~q ==> p"; // 5
                                // Pelletier #05
                                @"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)"; // 6
                                // Pelletier #06
                                @"p \/ ~p"; // 7
                                @"p \/ ~(~(~p))"; // 8
                                // Pelletier #08
                                @"((p ==> q) ==> p) ==> p"; // 9
                                // Pelletier #09
                                @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)"; // 10
                                // Pelletier #10
                                @"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)"; // 11
                                // Pelletier #11
                                @"p <=> p"; // 12
                                @"((p <=> q) <=> r) <=> p <=> q <=> r"; // 13
                                // Pelletier #13
                                @"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)"; // 14
                                // Pelletier #14
                                @"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)"; // 15
                                // Pelletier #15
                                @"p ==> q <=> ~p \/ q"; // 16
                                // Pelletier #16
                                @"(p ==> q) \/ (q ==> p)"; // 17
                                // Pelletier #17
                                @"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)"; // 18
                                // Pelletier #01
                                @"p ==> q <=> ~q ==> ~p"; // 19
                                @"~(~p) <=> p"; // 20
                                // Pelletier #03
                                @"~(p ==> q) ==> q ==> p"; // 21
                                // Pelletier #04
                                @"~p ==> q <=> ~q ==> p"; // 22
                                // Pelletier #05
                                @"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)"; // 23
                                // Pelletier #06
                                @"p \/ ~p"; // 24
                                @"p \/ ~(~(~p))"; // 25
                                // Pelletier #08
                                @"((p ==> q) ==> p) ==> p"; // 26
                                // Pelletier #09
                                @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)"; // 27
                                // Pelletier #10
                                @"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)"; // 28
                                @"((p <=> q) <=> r) <=> p <=> q <=> r"; // 29
                                // Pelletier #13
                                @"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)"; // 30
                                // Pelletier #14
                                @"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)"; // 31
                                // Pelletier #15
                                @"p ==> q <=> ~p \/ q"; // 32
                                // Pelletier #16
                                @"(p ==> q) \/ (q ==> p)"; // 33
                                // Pelletier #17
                                @"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)"; // 34
                                // Pelletier #18
                                @"exists y. forall x. P(y) ==> P(x)"; // 35
                                // Pelletier #19
                                @"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)"; // 36
                                // Pelletier #20
                                @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"; // 37
                                // Pelletier #21
                                @"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))"; // 38
                                // Pelletier #22
                                @"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))"; // 39
                                // Pelletier #23
                                @"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))"; // 40
                                // Pelletier #24
                                @"~(exists x. U(x) /\ Q(x)) /\ (forall x. P(x) ==> Q(x) \/ R(x)) /\ ~(exists x. P(x) ==> (exists x. Q(x))) /\ (forall x. Q(x) /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))"; // 41
                                // Pelletier #25
                                @"(exists x. P(x)) /\ (forall x. U(x) ==> ~G(x) /\ R(x)) /\ (forall x. P(x) ==> G(x) /\ U(x)) /\ ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> (exists x. Q(x) /\ P(x))"; // 42
                                // Pelletier #26
                                @"((exists x. P(x)) <=> (exists x. Q(x))) /\ (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))"; // 43
                                // Pelletier #27
                                @"(exists x. P(x) /\ ~Q(x)) /\ (forall x. P(x) ==> R(x)) /\ (forall x. U(x) /\ V(x) ==> P(x)) /\ (exists x. R(x) /\ ~Q(x)) ==> (forall x. U(x) ==> ~R(x)) ==> (forall x. U(x) ==> ~V(x))"; // 44
                                // Pelletier #28
                                @"(forall x. P(x) ==> (forall x. Q(x))) /\ ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> (forall x. P(x) /\ L(x) ==> M(x))"; // 45
                                // Pelletier #29
                                @"(exists x. P(x)) /\ (exists x. G(x)) ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))"; // 46
                                // Pelletier #30
                                @"(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==> (forall x. U(x))"; // 47
                                // Pelletier #31
                                @"~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ (forall x. ~H(x) ==> J(x)) ==> (exists x. Q(x) /\ J(x))"; // 48
                                // Pelletier #32
                                @"(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ (forall x. Q(x) /\ H(x) ==> J(x)) /\ (forall x. R(x) ==> H(x)) ==> (forall x. P(x) /\ R(x) ==> J(x))"; // 49
                                // Pelletier #33
                                @"(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))"; // 50
                                    |]

// lcffol.p005
// Pelletier #01
[<TestCase(@"p ==> q <=> ~q ==> ~p", 2)>]

// lcffol.p006
// Pelletier #02
[<TestCase(@"~ ~p <=> p", 3)>]

// lcffol.p007
// Pelletier #03
[<TestCase(@"~(p ==> q) ==> q ==> p", 4)>]

// lcffol.p008
// Pelletier #04
[<TestCase(@"~p ==> q <=> ~q ==> p", 5)>]

// lcffol.p009
// Pelletier #05
[<TestCase(@"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)", 6)>]

// lcffol.p010
// Pelletier #06
[<TestCase(@"p \/ ~p", 7)>]

// lcffol.p011
// Pelletier #07
[<TestCase(@"p \/ ~ ~ ~p", 8)>]

// lcffol.p012
// Pelletier #08
[<TestCase(@"((p ==> q) ==> p) ==> p", 9)>]

// lcffol.p013
// Pelletier #09
[<TestCase(@"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", 10)>]

// lcffol.p014
// Pelletier #10
[<TestCase(@"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", 11)>]

// lcffol.p015
// Pelletier #11
[<TestCase(@"p <=> p", 12)>]

// lcffol.p016
// Pelletier #12
[<TestCase(@"((p <=> q) <=> r) <=> (p <=> (q <=> r))", 13)>]

// lcffol.p017
// Pelletier #13
[<TestCase(@"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", 14)>]

// lcffol.p018
// Pelletier #14
[<TestCase(@"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", 15)>]

// lcffol.p019
// Pelletier #15
[<TestCase(@"p ==> q <=> ~p \/ q", 16)>]

// lcffol.p020
// Pelletier #16
[<TestCase(@"(p ==> q) \/ (q ==> p)", 17)>]

// lcffol.p021
// Pelletier #17
[<TestCase(@"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", 18)>]

// lcffol.p022 - Wrong test for test case
// Pelletier #01
[<TestCase(@"p ==> q <=> ~q ==> ~p", 19)>]

// lcffol.p023 - Wrong test for test case
// Pelletier #02
[<TestCase(@"~ ~p <=> p", 20)>]

// lcffol.p024 - Wrong test for test case
// Pelletier #03
[<TestCase(@"~(p ==> q) ==> q ==> p", 21)>]

let ``lcftaut`` (f, idx) =
    lcftaut (parse f) 
    |> should equal (parse lcffol_results.[idx])

// lcffol.p069
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
[<TestCase(@"forall x. exists v. exists w. forall y. forall z. ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))", 0)>]

// lcffol.p080
// Dijkstra #1
[<TestCase(@"(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> f(x) <= f(y))", 1)>]

// lcffol.p025
// Pelletier #04
[<TestCase(@"~p ==> q <=> ~q ==> p", 22)>]

// lcffol.p026
// Pelletier #05
[<TestCase(@"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)", 23)>]

// lcffol.p027
// Pelletier #06
[<TestCase(@"p \/ ~p", 24)>]

// lcffol.p028
// Pelletier #07
[<TestCase(@"p \/ ~ ~ ~p", 25)>]

// lcffol.p029
// Pelletier #08
[<TestCase(@"((p ==> q) ==> p) ==> p", 26)>]

// lcffol.p030
// Pelletier #09
[<TestCase(@"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)", 27)>]

// lcffol.p031
// Pelletier #10
[<TestCase(@"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)", 28)>]

// lcffol.p033
// Pelletier #12
[<TestCase(@"((p <=> q) <=> r) <=> (p <=> (q <=> r))", 29)>]

// lcffol.p034
// Pelletier #13
[<TestCase(@"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)", 30)>]

// lcffol.p035
// Pelletier #14
[<TestCase(@"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)", 31)>]

// lcffol.p036
// Pelletier #15
[<TestCase(@"p ==> q <=> ~p \/ q", 32)>]

// lcffol.p037
// Pelletier #16
[<TestCase(@"(p ==> q) \/ (q ==> p)", 33)>]

// lcffol.p038
// Pelletier #17
[<TestCase(@"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)", 34)>]

// lcffol.p039
// Pelletier #18
[<TestCase(@"exists y. forall x. P(y) ==> P(x)", 35)>]

// lcffol.p040
// Pelletier #19
[<TestCase(@"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", 36)>]

// lcffol.p041
// Pelletier #20
[<TestCase(@"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", 37)>]

// lcffol.p042
// Pelletier #21
[<TestCase(@"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))", 38)>]

// lcffol.p043
// Pelletier #22
[<TestCase(@"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))", 39)>]

// lcffol.p044
// Pelletier #23
[<TestCase(@"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))", 40)>]

// lcffol.p045
// Pelletier #24
[<TestCase(@"~(exists x. U(x) /\ Q(x)) /\ (forall x. P(x) ==> Q(x) \/ R(x)) /\ ~(exists x. P(x) ==> (exists x. Q(x))) /\ (forall x. Q(x) /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))", 41)>]

// lcffol.p046
// Pelletier #25
[<TestCase(@"(exists x. P(x)) /\ (forall x. U(x) ==> ~G(x) /\ R(x)) /\ (forall x. P(x) ==> G(x) /\ U(x)) /\ ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> (exists x. Q(x) /\ P(x))", 42)>]

// lcffol.p047
// Pelletier #26
[<TestCase(@"((exists x. P(x)) <=> (exists x. Q(x))) /\ (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))", 43)>]

// lcffol.p048
// Pelletier #27
[<TestCase(@"(exists x. P(x) /\ ~Q(x)) /\ (forall x. P(x) ==> R(x)) /\ (forall x. U(x) /\ V(x) ==> P(x)) /\ (exists x. R(x) /\ ~Q(x)) ==> (forall x. U(x) ==> ~R(x)) ==> (forall x. U(x) ==> ~V(x))", 44)>]

// lcffol.p049
// Pelletier #28
[<TestCase(@"(forall x. P(x) ==> (forall x. Q(x))) /\ ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> (forall x. P(x) /\ L(x) ==> M(x))", 45)>]

// lcffol.p050
// Pelletier #29
[<TestCase(@"(exists x. P(x)) /\ (exists x. G(x)) ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))", 46)>]

// lcffol.p051
// Pelletier #30
[<TestCase(@"(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==> (forall x. U(x))", 47)>]

// lcffol.p052
// Pelletier #31
[<TestCase(@"~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ (forall x. ~H(x) ==> J(x)) ==> (exists x. Q(x) /\ J(x))", 48)>]

// lcffol.p053
// Pelletier #32
[<TestCase(@"(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ (forall x. Q(x) /\ H(x) ==> J(x)) /\ (forall x. R(x) ==> H(x)) ==> (forall x. P(x) /\ R(x) ==> J(x))", 49)>]

// lcffol.p054
// Pelletier #33
[<TestCase(@"(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))", 50)>]

let ``lcffol all`` (f, idx) =
    lcffol (parse f) 
    |> should equal (parse lcffol_results.[idx])
 
//  ------------------------------------------------------------------------- // 
//  More exhaustive set of tests not in the main text.                        // 
//  ------------------------------------------------------------------------- // 

let private lcffol_gilmore_results = [| 
                                        @"exists x.
                                            forall y z.
                                            ((F(y,z) ==> G(y) ==> H(x)) ==> F(x,x)) /\
                                            ((F(z,x) ==> G(x)) ==> H(z)) /\ F(x,y) ==> F(z,z)"; // 0
                                        @"exists x y.
                                            forall z.
                                            (F(x,y) ==> F(y,z) /\ F(z,z)) /\
                                            (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))"; // 1
                                        @"(forall x. exists y. F(x,y) \/ F(y,x)) /\
                                            (forall x y. F(y,x) ==> F(y,y)) ==> (exists z. F(z,z))"; // 2
                                        @"forall x.
                                            exists y.
                                            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) ==>
                                            (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                                            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))"; // 3
                                        @"(forall x. K(x) ==> (exists y. L(y) /\ (F(x,y) ==> G(x,y)))) /\
                                            (exists z. K(z) /\ (forall u. L(u) ==> F(z,u))) ==>
                                            (exists v w. K(v) /\ L(w) /\ G(v,w))"; // 4
                                        @"exists x.
                                            forall y z.
                                            ((F(y,z) ==> G(y) ==> (forall u. exists v. H(u,v,x))) ==> F(x,x)) /\
                                            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ F(x,y) ==>
                                            F(z,z)"; // 5
                                        @"forall x.
                                            exists y.
                                            forall z.
                                            ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) ==>
                                            (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==>
                                            (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
                                            ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) ==>
                                            ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==>
                                            (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                                            (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))"; // 6
                                    |]

// lcffol.p072
// Gilmore #3
[<TestCase(@"exists x. forall y z. ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> H(z)) /\ F(x,y) ==> F(z,z)", 0, Category = "LongRunning")>]

// lcffol.p073
// Gilmore #4
[<TestCase(@"exists x y. forall z. (F(x,y) ==> F(y,z) /\ F(z,z)) /\ (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))", 1, Category = "LongRunning")>]

// lcffol.p074
// Gilmore #5
[<TestCase(@"(forall x. exists y. F(x,y) \/ F(y,x)) /\ (forall x y. F(y,x) ==> F(y,y)) ==> exists z. F(z,z)", 2)>]

// lcffol.p075
// Gilmore #6
[<TestCase(@"forall x. exists y. (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))", 3)>]

// lcffol.p076
// Gilmore #7
[<TestCase(@"(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\ (exists z. K(z) /\ forall u. L(u) ==> F(z,u)) ==> exists v w. K(v) /\ L(w) /\ G(v,w)", 4)>]

// lcffol.p077
// Gilmore #8
[<TestCase(@"exists x. forall y z. ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ F(x,y) ==> F(z,z)", 5, Category = "LongRunning")>]

// lcffol.p078
// Gilmore #9
[<TestCase(@"forall x. exists y. forall z. ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))", 6, Category = "LongRunning")>]

let ``lcffol gilmore`` (f, idx) =
    lcffol (parse f) 
    |> should equal (parse lcffol_gilmore_results.[idx])
