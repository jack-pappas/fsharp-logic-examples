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

let private tabValues : (string * int)[] = [| 
    (
        // idx 0
        // meson.p001
        @"forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))",
        2
    );
    (
        // idx 1
        // meson.p002
        @"forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))",
        0
    );
    (
        // idx 2
        // meson.p003
        // Harrison #09
        @" ~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
        (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
        (~s \/ ~v) /\ (~s \/ ~w) ==> false",
        0
    );
    |]
    
[<TestCase(0, TestName = "meson.p001")>]
[<TestCase(1, TestName = "meson.p002")>]
[<TestCase(2, TestName = "meson.p003")>]

let ``tab tests`` (idx) =
    let (formula, _) = tabValues.[idx]
    let (_, result) = tabValues.[idx]
    tab (parse formula)
    |> should equal result

// -------------------------------------------------------------------------------

let private meson002Values : (string * int list)[] = [| 
    (
        // idx 0
        // meson.p007
        // Pelletier #01
        @"p ==> q <=> ~q ==> ~p",
        []
    );
    (
        // idx 1
        // meson.p008
        // Pelletier #02
        @"~ ~p <=> p",
        []
    );
    (
        // idx 2
        // meson.p009
        // Pelletier #03
        @"~(p ==> q) ==> q ==> p",
        []
    );
    (
        // idx 3
        // meson.p010
        // Pelletier #04
        @"~p ==> q <=> ~q ==> p",
        []
    );
    (
        // idx 4
        // meson.p011
        // Pelletier #05
        @"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)",
        []
    );
    (
        // idx 5
        // meson.p012
        // Pelletier #06
        @"p \/ ~p",
        []
    );
    (
        // idx 6
        // meson.p013
        // Pelletier #07
        @"p \/ ~ ~ ~p",
        []
    );
    (
        // idx 7
        // meson.p014
        // Pelletier #08
        @"((p ==> q) ==> p) ==> p",
        []
    );
    (
        // idx 8
        // meson.p015
        // Pelletier #09
        @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)",
        []
    );
    (
        // idx 9
        // meson.p016
        // Pelletier #10
        @"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)",
        []
    );
    (
        // idx 10
        // meson.p017
        // Pelletier #11
        @"p <=> p",
        []
    );
    (
        // idx 11
        // meson.p018
        // Pelletier #12
        @"((p <=> q) <=> r) <=> (p <=> (q <=> r))",
        []
    );
    (
        // idx 12
        // meson.p019
        // Pelletier #13
        @"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)",
        []
    );
    (
        // idx 13
        // meson.p020
        // Pelletier #14
        @"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)",
        []
    );
    (
        // idx 14
        // meson.p021
        // Pelletier #15
        @"p ==> q <=> ~p \/ q",
        []
    );
    (
        // idx 15
        // meson.p022
        // Pelletier #16
        @"(p ==> q) \/ (q ==> p)",
        []
    );
    (
        // idx 16
        // meson.p023
        // Pelletier #17
        @"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)",
        []
    );
    (
        // idx 17
        // meson.p024
        // Pelletier #18
        @"exists y. forall x. P(y) ==> P(x)",
        [1]
    );
    (
        // idx 18
        // meson.p025
        // Pelletier #19
        @"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)",
        [2]
    );
    (
        // idx 19
        // meson.p026
        // Pelletier #20
        @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
        [3]
    );
    (
        // idx 20
        // meson.p027
        // Pelletier #21
        @"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
        ==> (exists x. P <=> Q(x))",
        [2; 3; 2]
    );
    (
        // idx 21
        // meson.p028
        // Pelletier #22
        @"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))",
        [2; 2]
    );
    (
        // idx 22
        // meson.p029
        // Pelletier #23
        @"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))",
        [2; 1]
    );
    (
        // idx 23
        // meson.p030
        // Pelletier #24
        @"~(exists x. U(x) /\ Q(x)) /\
        (forall x. P(x) ==> Q(x) \/ R(x)) /\
        ~(exists x. P(x) ==> (exists x. Q(x))) /\
        (forall x. Q(x) /\ R(x) ==> U(x)) ==>
        (exists x. P(x) /\ R(x))",
        [4]
    );
    (
        // idx 24
        // meson.p031
        // Pelletier #25
        @"(exists x. P(x)) /\
        (forall x. U(x) ==> ~G(x) /\ R(x)) /\
        (forall x. P(x) ==> G(x) /\ U(x)) /\
        ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
        ==> (exists x. Q(x) /\ P(x))",
        [2; 3]
    );
    (
        // idx 25
        // meson.p032
        // Pelletier #26
        @"((exists x. P(x)) <=> (exists x. Q(x))) /\
        (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x))
        <=> (forall x. Q(x) ==> U(x)))",
        [5; 5; 1; 1]
    );
    (
        // idx 26
        // meson.p033
        // Pelletier #27
        @"(exists x. P(x) /\ ~Q(x)) /\
        (forall x. P(x) ==> R(x)) /\
        (forall x. U(x) /\ V(x) ==> P(x)) /\
        (exists x. R(x) /\ ~Q(x))
        ==> (forall x. U(x) ==> ~R(x))
            ==> (forall x. U(x) ==> ~V(x))",
        [5]
    );
    (
        // idx 27
        // meson.p034
        // Pelletier #28
        @"(forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))",
        [1; 2; 2; 2]
    );
    (
        // idx 28
        // meson.p035
        // Pelletier #29
        @"(exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
        [3; 2; 2; 3 ]
    );
    (
        // idx 29
        // meson.p036
        // Pelletier #30
        @"(forall x. P(x) \/ G(x) ==> ~H(x)) /\
        (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
        ==> (forall x. U(x))",
        [4]
    );
    (
        // idx 30
        // meson.p037
        // Pelletier #31
        @"~(exists x. P(x) /\ (G(x) \/ H(x))) /\
        (exists x. Q(x) /\ P(x)) /\
        (forall x. ~H(x) ==> J(x))
        ==> (exists x. Q(x) /\ J(x))",
        [4]
    );
    (
        // idx 31
        // meson.p038
        // Pelletier #32
        @"(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
        (forall x. Q(x) /\ H(x) ==> J(x)) /\
        (forall x. R(x) ==> H(x))
        ==> (forall x. P(x) /\ R(x) ==> J(x))",
        [7]
    );
    (
        // idx 32
        // meson.p039
        // Pelletier #33
        @"(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
        (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))",
        [3; 3; 3]
    );
    (
        // idx 33
        // meson.p040
        // Pelletier #34
        // Ran for 9.5 hours with out completion.
        @"((exists x. forall y. P(x) <=> P(y)) <=>
            ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
            ((exists x. P(x)) <=> (forall y. P(y))))",
        [3; 3; 3; 1; 2; 2; 2; 1; 3; 2; 2; 1; 3; 2; 2; 1; 2; 1; 2; 1; 3; 1; 2; 1; 2; 1; 2; 1; 1; 1; 1; 1]
    );
    (
        // idx 34
        // meson.p041
        // Pelletier #35
        @"exists x y. P(x,y) ==> (forall x y. P(x,y))",
        [1]
    );
    (
        // idx 35
        // meson.p042
        // Pelletier #36
        @"(forall x. exists y. P(x,y)) /\
        (forall x. exists y. G(x,y)) /\
        (forall x y. P(x,y) \/ G(x,y)
        ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
            ==> (forall x. exists y. H(x,y))",
        [3]
    );
    (
        // idx 36
        // meson.p043
        // Pelletier #37
        @"(forall z.
            exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
            (P(y,w) ==> (exists u. Q(u,w)))) /\
        (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
        ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
        (forall x. exists y. R(x,y))",
        [1; 3]
    );
    (
        // idx 37
        // meson.p044
        // Pelletier #38
        @"(forall x.
            P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
        (forall x.
            (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
            (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))))",
        [12; 12; 9; 9]
    );
    (
        // idx 38
        // meson.p045
        // Pelletier #39
        @"~(exists x. forall y. P(y,x) <=> ~P(y,y))",
        [4]
    );
    (
        // idx 39
        // meson.p046
        // Pelletier #40
        @"(exists y. forall x. P(x,y) <=> P(x,x))
        ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))",
        [6]
    );
    (
        // idx 40
        // meson.p047
        // Pelletier #41
        @"(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
        ==> ~(exists z. forall x. P(x,z))",
        [6]
    );
    (
        // idx 41
        // meson.p048
        // Pelletier #42
        @"~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))",
        [12]
    );
    (
        // idx 42
        // meson.p049
        // Pelletier #43
        @"(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)",
        [11; 11]
    );
    (
        // idx 43
        // meson.p050
        // Pelletier #44
        @"(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
        (exists y. G(y) /\ ~H(x,y))) /\
        (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
        (exists x. J(x) /\ ~P(x))",
        [6]
    );
    (
        // idx 44
        // meson.p051
        // Pelletier #45
        @"(forall x.
            P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
                (forall y. G(y) /\ H(x,y) ==> R(y))) /\
        ~(exists y. L(y) /\ R(y)) /\
        (exists x. P(x) /\ (forall y. H(x,y) ==>
            L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
        (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))",
        [24]
    );
    (
        // idx 45
        // meson.p052
        // Pelletier #46
        @"(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
        ((exists x. P(x) /\ ~G(x)) ==> 
         (exists x. P(x) /\ ~G(x) /\ 
                    (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
        (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
        (forall x. P(x) ==> G(x))",
        [12; 2]
    );
    (
        // idx 46
        // meson.p006
        // Pelletier #47
        @"((forall x. P1(x) ==> P0(x)) /\ (exists x. P1(x))) /\ 
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
                    exists z. Q1(z) /\ R(y,z) /\ R(x,y)",
        []
    );
    (
        // idx 47
        // Pelletier #48
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 48
        // Pelletier #49
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 49
        // Pelletier #50
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 50
        // Pelletier #51
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 51
        // Pelletier #52
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 52
        // Pelletier #53
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 53
        // Pelletier #54
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 54
        // meson.p053
        // Pelletier #55
        @"lives(agatha) /\ lives(butler) /\ lives(charles) /\
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
            ~killed(charles,agatha)",
        [8; 3]
    );
    (
        // idx 55
        // Pelletier #56
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 56
        // meson.p054
        // Pelletier #57
        @"P(f(a,b),f(b,c)) /\
        P(f(b,c),f(a,c)) /\
        (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z))
        ==> P(f(a,b),f(a,c))",
        [3]
    );
    (
        // idx 57
        // meson.p055
        // Pelletier #58 1
        // TODO: Is this a conrrect translation from Pelletier #58? No
        @"forall P Q R. forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
        [3]
    );
    (
        // idx 58
        // meson.p056
        // Pelletier #59
        @"(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))",
        [6]
    );
    (
        // idx 59
        // meson.p057
        // Pelletier #60
        @"forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)",
        [2; 3]
    );
    (
        // idx 60
        // Pelletier #61
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 61
        // Pelletier #62
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 62
        // Pelletier #63
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 63
        // Pelletier #64
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 64
        // Pelletier #65
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 65
        // Pelletier #66
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 66
        // Pelletier #67
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 67
        // Pelletier #68
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 68
        // Pelletier #69
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 69
        // Pelletier #70
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 70
        // Pelletier #71
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 71
        // Pelletier #72
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 72
        // Pelletier #73
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 73
        // Pelletier #74
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 74
        // Pelletier #75
        @"formula_place_holder_for_future_use",
        [999;999]
    );
    (
        // idx 75
        // meson.p058
        // Gilmore #1
        @"exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)",
        [-99]
    );
    (
        // idx 76
        // meson.p059
        // Gilmore #2
        @"exists x y. forall z. 
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
        ==> (F(x,y) <=> F(x,z))",
        [-99]
    );
    (
        // idx 77
        // meson.p060
        // Gilmore #3
        @"exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> H(z)) /\
            F(x,y)
            ==> F(z,z)",
        [4]
    );
    (
        // idx 78
        // meson.p061
        // Gilmore #4
        @"exists x y. forall z.
            (F(x,y) ==> F(y,z) /\ F(z,z)) /\
            (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))",
        [8]
    );
    (
        // idx 79
        // meson.p062
        // Gilmore #5
        @"(forall x. exists y. F(x,y) \/ F(y,x)) /\
        (forall x y. F(y,x) ==> F(y,y))
        ==> exists z. F(z,z)",
        [4]
    );
    (
        // idx 80
        // meson.p063
        // Gilmore #6
        @"forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))",
        [2]
    );
    (
        // idx 81
        // meson.p064
        // Gilmore #7
        @"(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
        (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
        ==> exists v w. K(v) /\ L(w) /\ G(v,w)",
        [8]
    );
    (
        // idx 82
        // meson.p065
        // Gilmore #8
        @"exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)",
        [4]
    );
    (
        // idx 83
        // meson.p066
        // Gilmore #9
        @"forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
            ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
            ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
        ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
        ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
            (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))",
        [6]
    );
    (
        // idx 84
        // meson.p004
        // meson.p068
        // Davis Putnam #1
        @"exists x. exists y. forall z.
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
        [8]
    );
    (
        // idx 85
        // Dijkstra #1
        @"(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y))",
        [999;999]
    );
    (
        // idx 86
        // Dijkstra #2
        @"(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> g(x) <= g(y))",
        [999;999]
    );
    (
        // idx 87
        // Pelletier #58 2
        // TODO: Is this a conrrect translation from Pelletier #58? No
        @"forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
        [999;999]
    );
    (
        // idx 88
        // meson.p005
        // Los #1
        @"(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
        (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
        (forall x y. Q(x,y) ==> Q(y,x)) /\ 
        (forall x y. P(x,y) \/ Q(x,y)) 
        ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
        [20]
    );
    (
        // idx 89
        // meson.p067
        // Gilmore #9a
        @"(forall x y. P(x,y) <=> 
            forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
        ==> forall x. exists y. forall z. 
            (P(y,x) ==> (P(x,z) ==> P(x,y))) /\ 
            (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))",
        [7]
    );
    (
        // idx 90
        // meson.p069
        // Harrison #09
        @"~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\ 
        (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\ 
        (~s \/ ~v) /\ (~s \/ ~w) ==> false",
        []
    );
    |]

[<TestCase(0, TestName = "Pelletier #01")>]
[<TestCase(1, TestName = "Pelletier #02")>]
[<TestCase(2, TestName = "Pelletier #03")>]
[<TestCase(3, TestName = "Pelletier #04")>]
[<TestCase(4, TestName = "Pelletier #05")>]
[<TestCase(5, TestName = "Pelletier #06")>]
[<TestCase(6, TestName = "Pelletier #07")>]
[<TestCase(7, TestName = "Pelletier #08")>]
[<TestCase(8, TestName = "Pelletier #09")>]
[<TestCase(9, TestName = "Pelletier #10")>]
[<TestCase(10, TestName = "Pelletier #11")>]
[<TestCase(11, TestName = "Pelletier #12")>]
[<TestCase(12, TestName = "Pelletier #13")>]
[<TestCase(13, TestName = "Pelletier #14")>]
[<TestCase(14, TestName = "Pelletier #15")>]
[<TestCase(15, TestName = "Pelletier #16")>]
[<TestCase(16, TestName = "Pelletier #17")>]
[<TestCase(17, TestName = "Pelletier #18")>]
[<TestCase(18, TestName = "Pelletier #19")>]
[<TestCase(19, TestName = "Pelletier #20")>]
[<TestCase(20, TestName = "Pelletier #21")>]
[<TestCase(21, TestName = "Pelletier #22")>]
[<TestCase(22, TestName = "Pelletier #23")>]
[<TestCase(23, TestName = "Pelletier #24")>]
[<TestCase(24, TestName = "Pelletier #25")>]
[<TestCase(25, TestName = "Pelletier #26")>]
[<TestCase(26, TestName = "Pelletier #27")>]
[<TestCase(27, TestName = "Pelletier #28")>]
[<TestCase(28, TestName = "Pelletier #29")>]
[<TestCase(29, TestName = "Pelletier #30")>]
[<TestCase(30, TestName = "Pelletier #31")>]
[<TestCase(31, TestName = "Pelletier #32")>]
[<TestCase(32, TestName = "Pelletier #33")>]
[<TestCase(33, TestName = "Pelletier #34")>]
[<TestCase(34, TestName = "Pelletier #35")>]
[<TestCase(35, TestName = "Pelletier #36")>]
[<TestCase(36, TestName = "Pelletier #37")>]
[<TestCase(37, TestName = "Pelletier #38")>]
[<TestCase(38, TestName = "Pelletier #39")>]
[<TestCase(39, TestName = "Pelletier #40")>]
[<TestCase(40, TestName = "Pelletier #41")>]
[<TestCase(41, TestName = "Pelletier #42")>]
[<TestCase(42, TestName = "Pelletier #43")>]
[<TestCase(43, TestName = "Pelletier #44")>]
[<TestCase(44, TestName = "Pelletier #45")>]
[<TestCase(45, TestName = "Pelletier #46")>]
[<TestCase(46, TestName = "Pelletier #47", Category = "LongRunning")>]
[<TestCase(54, TestName = "Pelletier #55")>]
[<TestCase(56, TestName = "Pelletier #57")>]
[<TestCase(57, TestName = "Pelletier #58 1")>]
[<TestCase(75, TestName = "Gilmore #1", Category = "LongRunning")>]
[<TestCase(76, TestName = "Gilmore #2", Category = "LongRunning")>]
[<TestCase(77, TestName = "Gilmore #3")>]
[<TestCase(78, TestName = "Gilmore #4")>]
[<TestCase(79, TestName = "Gilmore #5")>]
[<TestCase(80, TestName = "Gilmore #6")>]
[<TestCase(81, TestName = "Gilmore #7")>]
[<TestCase(82, TestName = "Gilmore #8")>]
[<TestCase(83, TestName = "Gilmore #9", Category = "LongRunning")>]
//[<TestCase(58, TestName = "Pelletier #59")>]
//[<TestCase(59, TestName = "Pelletier #60")>]
[<TestCase(84, TestName = "Davis Putnam #1")>]
//[<TestCase(85, TestName = "Dijkstra #1")>]
//[<TestCase(86, TestName = "Dijkstra #2")>]
//[<TestCase(87, TestName = "Pelletier #58 2")>]
[<TestCase(88, TestName = "Los #1", Category = "LongRunning")>]
[<TestCase(89, TestName = "Gilmore #9a")>]
[<TestCase(90, TestName = "Harrison #09")>]

let ``meson002 tests`` (idx) =
    let (formula, _) = meson002Values.[idx]
    let (_, result) = meson002Values.[idx]
    meson002 (parse formula)
    |> should equal result
