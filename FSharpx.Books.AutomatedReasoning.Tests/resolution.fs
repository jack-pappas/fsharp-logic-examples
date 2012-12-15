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

let private barberValues : (string * formula<fol> list list)[] = [| 
    (
        // idx 0
        // resolution.p001
        // Barber's paradox
        @"~(exists b. forall x. shaves(b,x) <=> ~shaves(x,x))",
        [[Atom (R ("shaves",[Var "x"; Var "x"]));
        Atom (R ("shaves",[Fn ("c_b",[]); Var "x"]))];
        [Not (Atom (R ("shaves",[Var "x"; Var "x"])));
        Not (Atom (R ("shaves",[Fn ("c_b",[]); Var "x"])))]]
    );
    |]
    
[<TestCase(0, TestName = "Barber's paradox")>]

let ``simpcnf tests`` (idx) =
    let (formula, _) = barberValues.[idx]
    let (_, result) = barberValues.[idx]
    simpcnf(skolemize(Not (parse formula))) 
    |> should equal result    

let private resolutionValues : (string * bool list)[] = [| 
    (
        // idx 0
        // resolution.p005
        // resolution.p067
        // Pelletier #01
        @"p ==> q <=> ~q ==> ~p",
        []
    );
    (
        // idx 1
        // resolution.p006
        // resolution.p068
        // Pelletier #02
        @"~ ~p <=> p",
        []
    );
    (
        // idx 2
        // resolution.p007
        // resolution.p069
        // Pelletier #03
        @"~(p ==> q) ==> q ==> p",
        []
    );
    (
        // idx 3
        // resolution.p008
        // resolution.p070
        // Pelletier #04
        @"~p ==> q <=> ~q ==> p",
        []
    );
    (
        // idx 4
        // resolution.p009
        // resolution.p071
        // Pelletier #05
        @"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)",
        []
    );
    (
        // idx 5
        // resolution.p010
        // resolution.p072
        // Pelletier #06
        @"p \/ ~p",
        []
    );
    (
        // idx 6
        // resolution.p011
        // resolution.p073
        // Pelletier #07
        @"p \/ ~ ~ ~p",
        []
    );
    (
        // idx 7
        // resolution.p012
        // resolution.p074
        // Pelletier #08
        @"((p ==> q) ==> p) ==> p",
        []
    );
    (
        // idx 8
        // resolution.p013
        // resolution.p075
        // Pelletier #09
        @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)",
        []
    );
    (
        // idx 9
        // resolution.p014
        // resolution.p076
        // Pelletier #10
        @"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)",
        []
    );
    (
        // idx 10
        // resolution.p015
        // resolution.p077
        // Pelletier #11
        @"p <=> p",
        []
    );
    (
        // idx 11
        // resolution.p016
        // resolution.p078
        // Pelletier #12
        @"((p <=> q) <=> r) <=> (p <=> (q <=> r))",
        []
    );
    (
        // idx 12
        // resolution.p017
        // resolution.p079
        // Pelletier #13
        @"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)",
        []
    );
    (
        // idx 13
        // resolution.p018
        // resolution.p080
        // Pelletier #14
        @"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)",
        []
    );
    (
        // idx 14
        // resolution.p019
        // resolution.p081
        // Pelletier #15
        @"p ==> q <=> ~p \/ q",
        []
    );
    (
        // idx 15
        // resolution.p020
        // resolution.p082
        // Pelletier #16
        @"(p ==> q) \/ (q ==> p)",
        []
    );
    (
        // idx 16
        // resolution.p021
        // resolution.p083
        // Pelletier #17
        @"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)",
        []
    );
    (
        // idx 17
        // resolution.p022
        // resolution.p084
        // Pelletier #18
        @"exists y. forall x. P(y) ==> P(x)",
        [true]
    );
    (
        // idx 18
        // resolution.p023
        // resolution.p085
        // Pelletier #19
        @"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)",
        [true]
    );
    (
        // idx 19
        // resolution.p024
        // resolution.p086
        // Pelletier #20
        @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
        [true]
    );
    (
        // idx 20
        // resolution.p025
        // resolution.p087
        // Pelletier #21
        @"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
        ==> (exists x. P <=> Q(x))",
        [true; true; true]
    );
    (
        // idx 21
        // resolution.p026
        // resolution.p088
        // Pelletier #22
        @"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))",
        [true; true]
    );
    (
        // idx 22
        // resolution.p027
        // resolution.p089
        // Pelletier #23
        @"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))",
        [true; true]
    );
    (
        // idx 23
        // resolution.p028
        // resolution.p090
        // Pelletier #24
        @"~(exists x. U(x) /\ Q(x)) /\
        (forall x. P(x) ==> Q(x) \/ R(x)) /\
        ~(exists x. P(x) ==> (exists x. Q(x))) /\
        (forall x. Q(x) /\ R(x) ==> U(x)) ==>
        (exists x. P(x) /\ R(x))",
        [true]
    );
    (
        // idx 24
        // resolution.p029
        // resolution.p091
        // Pelletier #25
        @"(exists x. P(x)) /\
        (forall x. U(x) ==> ~G(x) /\ R(x)) /\
        (forall x. P(x) ==> G(x) /\ U(x)) /\
        ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
        ==> (exists x. Q(x) /\ P(x))",
        [true; true]
    );
    (
        // idx 25
        // resolution.p030
        // resolution.p092
        // Pelletier #26
        @"((exists x. P(x)) <=> (exists x. Q(x))) /\
        (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x))
        <=> (forall x. Q(x) ==> U(x)))",
        [true; true; true; true]
    );
    (
        // idx 26
        // resolution.p031
        // resolution.p093
        // Pelletier #27
        @"(exists x. P(x) /\ ~Q(x)) /\
        (forall x. P(x) ==> R(x)) /\
        (forall x. U(x) /\ V(x) ==> P(x)) /\
        (exists x. R(x) /\ ~Q(x))
        ==> (forall x. U(x) ==> ~R(x))
            ==> (forall x. U(x) ==> ~V(x))",
        [true]
    );
    (
        // idx 27
        // resolution.p032
        // resolution.p094
        // Pelletier #28
        @"(forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))",
        [true; true; true; true ]
    );
    (
        // idx 28
        // resolution.p033
        // resolution.p095
        // Pelletier #29
        @"(exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
        [true; true; true; true ]
    );
    (
        // idx 29
        // resolution.p034
        // resolution.p096
        // Pelletier #30
        @"(forall x. P(x) \/ G(x) ==> ~H(x)) /\
        (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
        ==> (forall x. U(x))",
        [true]
    );
    (
        // idx 30
        // resolution.p035
        // resolution.p097
        // Pelletier #31
        @"~(exists x. P(x) /\ (G(x) \/ H(x))) /\
        (exists x. Q(x) /\ P(x)) /\
        (forall x. ~H(x) ==> J(x))
        ==> (exists x. Q(x) /\ J(x))",
        [true]
    );
    (
        // idx 31
        // resolution.p036
        // resolution.p098
        // Pelletier #32
        @"(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
        (forall x. Q(x) /\ H(x) ==> J(x)) /\
        (forall x. R(x) ==> H(x))
        ==> (forall x. P(x) /\ R(x) ==> J(x))",
        [true]
    );
    (
        // idx 32
        // resolution.p037
        // resolution.p099
        // Pelletier #33
        @"(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
        (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))",
        [true; true; true]
    );
    (
        // idx 33
        // resolution.p038
        // resolution.p100
        // Pelletier #34
        @"((exists x. forall y. P(x) <=> P(y)) <=>
            ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
            ((exists x. P(x)) <=> (forall y. P(y))))",
        [true; true; true; true; true; true; true; true; true; true; true; true; true;
        true; true; true; true; true; true; true; true; true; true; true; true; true;
        true; true; true; true; true; true]
    );
    (
        // idx 34
        // resolution.p039
        // resolution.p101
        // Pelletier #35
        @"exists x y. P(x,y) ==> (forall x y. P(x,y))",
        [true]
    );
    (
        // idx 35
        // resolution.p040
        // resolution.p102
        // Pelletier #36
        @"(forall x. exists y. P(x,y)) /\
        (forall x. exists y. G(x,y)) /\
        (forall x y. P(x,y) \/ G(x,y)
        ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
            ==> (forall x. exists y. H(x,y))",
        [true]
    );
    (
        // idx 36
        // resolution.p041
        // resolution.p103
        // Pelletier #37
        @"(forall z.
            exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
            (P(y,w) ==> (exists u. Q(u,w)))) /\
        (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
        ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
        (forall x. exists y. R(x,y))",
        [true; true]
    );
    (
        // idx 37
        // resolution.p042
        // resolution.p104
        // Pelletier #38
        @"(forall x.
            P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
        (forall x.
            (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
            (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))))",
        [true]
    );
    (
        // idx 38
        // resolution.p043
        // resolution.p105
        // Pelletier #39
        @"~(exists x. forall y. P(y,x) <=> ~P(y,y))",
        [true]
    );
    (
        // idx 39
        // resolution.p044
        // resolution.p106
        // Pelletier #40
        @"(exists y. forall x. P(x,y) <=> P(x,x))
        ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))",
        [true]
    );
    (
        // idx 40
        // resolution.p045
        // resolution.p107
        // Pelletier #41
        @"(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
        ==> ~(exists z. forall x. P(x,z))",
        [true]
    );
    (
        // idx 41
        // resolution.p046
        // resolution.p108
        // Pelletier #42
        @"~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))",
        [true]
    );
    (
        // idx 42
        // resolution.p047
        // resolution.p109
        // Pelletier #43
        @"(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)",
        [true]
    );
    (
        // idx 43
        // resolution.p048
        // resolution.p110
        // Pelletier #44
        @"(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
        (exists y. G(y) /\ ~H(x,y))) /\
        (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
        (exists x. J(x) /\ ~P(x))",
        [true]
    );
    (
        // idx 44
        // resolution.p049
        // resolution.p111
        // Pelletier #45
        @"(forall x.
            P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
                (forall y. G(y) /\ H(x,y) ==> R(y))) /\
        ~(exists y. L(y) /\ R(y)) /\
        (exists x. P(x) /\ (forall y. H(x,y) ==>
            L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
        (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))",
        [true]
    );
    (
        // idx 45
        // resolution.p050
        // resolution.p112
        // Pelletier #46
        @"(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
        ((exists x. P(x) /\ ~G(x)) ==> 
         (exists x. P(x) /\ ~G(x) /\ 
                    (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
        (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
        (forall x. P(x) ==> G(x))",
        [true; true]
    );
    (
        // idx 46
        // Pelletier #47
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 47
        // Pelletier #48
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 48
        // Pelletier #49
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 49
        // Pelletier #50
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 50
        // Pelletier #51
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 51
        // Pelletier #52
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 52
        // Pelletier #53
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 53
        // Pelletier #54
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 54
        // resolution.p051
        // resolution.p113
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
        [true; true]
    );
    (
        // idx 55
        // Pelletier #56
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 56
        // resolution.p052
        // resolution.p114
        // Pelletier #57
        @"P(f(a,b),f(b,c)) /\
        P(f(b,c),f(a,c)) /\
        (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z))
        ==> P(f(a,b),f(a,c))",
        [true]
    );
    (
        // idx 57
        // resolution.p053
        // resolution.p115
        // Pelletier #58 1
        // TODO: Is this a conrrect translation from Pelletier #58? No
        @"forall P Q R. forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
        [true]
    );
    (
        // idx 58
        // resolution.p054
        // resolution.p116
        // Pelletier #59
        @"(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))",
        [true]
    );
    (
        // idx 59
        // resolution.p055
        // resolution.p117
        // Pelletier #60
        @"forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)",
        [true; true]
    );
    (
        // idx 60
        // Pelletier #61
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 61
        // Pelletier #62
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 62
        // Pelletier #63
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 63
        // Pelletier #64
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 64
        // Pelletier #65
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 65
        // Pelletier #66
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 66
        // Pelletier #67
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 67
        // Pelletier #68
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 68
        // Pelletier #69
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 69
        // Pelletier #70
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 70
        // Pelletier #71
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 71
        // Pelletier #72
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 72
        // Pelletier #73
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 73
        // Pelletier #74
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 74
        // Pelletier #75
        @"formula_place_holder_for_future_use",
        [true]
    );
    (
        // idx 75
        // resolution.p056
        // resolution.p118
        // Gilmore #1
        @"exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)",
        [true]
    );
    (
        // idx 76
        // resolution.p057
        // resolution.p119
        // Gilmore #2
        @"exists x y. forall z. 
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
        ==> (F(x,y) <=> F(x,z))",
        [false]
    );
    (
        // idx 77
        // resolution.p058
        // resolution.p120
        // Gilmore #3
        @"exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> H(z)) /\
            F(x,y)
            ==> F(z,z)",
        [true]
    );
    (
        // idx 78
        // resolution.p059
        // resolution.p121
        // Gilmore #4
        @"exists x y. forall z.
            (F(x,y) ==> F(y,z) /\ F(z,z)) /\
            (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))",
        [true]
    );
    (
        // idx 79
        // resolution.p060
        // resolution.p122
        // Gilmore #5
        @"(forall x. exists y. F(x,y) \/ F(y,x)) /\
        (forall x y. F(y,x) ==> F(y,y))
        ==> exists z. F(z,z)",
        [true]
    );
    (
        // idx 80
        // resolution.p061
        // resolution.p123
        // Gilmore #6
        @"forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))",
        [true]
    );
    (
        // idx 81
        // resolution.p062
        // resolution.p124
        // Gilmore #7
        @"(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
        (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
        ==> exists v w. K(v) /\ L(w) /\ G(v,w)",
        [true]
    );
    (
        // idx 82
        // resolution.p063
        // resolution.p125
        // Gilmore #8
        @"exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)",
        [true]
    );
    (
        // idx 83
        // resolution.p064
        // resolution.p126
        // Gilmore #9
        @"forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
            ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
            ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
        ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
        ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
            (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))",
        [true]
    );
    (
        // idx 84
        // resolution.p065
        // resolution.p127
        // Davis Putnam #1
        @"exists x. exists y. forall z.
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
        [true]
    );
    (
        // idx 85
        // Dijkstra #1
        @"(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y))",
        [true]
    );
    (
        // idx 86
        // Dijkstra #2
        @"(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> g(x) <= g(y))",
        [true]
    );
    (
        // idx 87
        // Pelletier #58 2
        // TODO: Is this a conrrect translation from Pelletier #58? No
        @"forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
        [true]
    );
    (
        // idx 88
        // resolution.p004
        // resolution.p128
        // Los #1
        @"(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
        (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
        (forall x y. Q(x,y) ==> Q(y,x)) /\ 
        (forall x y. P(x,y) \/ Q(x,y)) 
        ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
        [true]
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
[<TestCase(37, TestName = "Pelletier #38", Category = "LongRunning")>]
[<TestCase(38, TestName = "Pelletier #39")>]
[<TestCase(39, TestName = "Pelletier #40")>]
[<TestCase(40, TestName = "Pelletier #41")>]
[<TestCase(41, TestName = "Pelletier #42")>]
[<TestCase(42, TestName = "Pelletier #43", Category = "LongRunning")>]
[<TestCase(43, TestName = "Pelletier #44")>]
[<TestCase(44, TestName = "Pelletier #45")>]
[<TestCase(45, TestName = "Pelletier #46")>]
[<TestCase(54, TestName = "Pelletier #55")>]
[<TestCase(56, TestName = "Pelletier #57")>]
[<TestCase(57, TestName = "Pelletier #58 1")>]
[<TestCase(75, TestName = "Gilmore #1")>]
[<TestCase(76, TestName = "Gilmore #2", Category = "LongRunning")>]
[<TestCase(77, TestName = "Gilmore #3")>]
[<TestCase(78, TestName = "Gilmore #4")>]
[<TestCase(79, TestName = "Gilmore #5")>]
[<TestCase(80, TestName = "Gilmore #6")>]
[<TestCase(81, TestName = "Gilmore #7")>]
[<TestCase(82, TestName = "Gilmore #8")>]
[<TestCase(83, TestName = "Gilmore #9", Category = "LongRunning")>]
[<TestCase(84, TestName = "Davis Putnam #1")>]
[<TestCase(88, TestName = "Los #1")>]

let ``Pure Resolution`` (idx) =
    let (formula, _) = resolutionValues.[idx]
    let (_, result) = resolutionValues.[idx]
    presolution (parse formula) 
    |> should equal result

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
[<TestCase(37, TestName = "Pelletier #38", Category = "LongRunning")>]
[<TestCase(38, TestName = "Pelletier #39")>]
[<TestCase(39, TestName = "Pelletier #40")>]
[<TestCase(40, TestName = "Pelletier #41")>]
[<TestCase(41, TestName = "Pelletier #42")>]
[<TestCase(42, TestName = "Pelletier #43", Category = "LongRunning")>]
[<TestCase(43, TestName = "Pelletier #44")>]
[<TestCase(44, TestName = "Pelletier #45")>]
[<TestCase(45, TestName = "Pelletier #46")>]
[<TestCase(54, TestName = "Pelletier #55")>]
[<TestCase(56, TestName = "Pelletier #57")>]
[<TestCase(57, TestName = "Pelletier #58 1")>]
[<TestCase(75, TestName = "Gilmore #1")>]
[<TestCase(76, TestName = "Gilmore #2", Category = "LongRunning")>]
[<TestCase(77, TestName = "Gilmore #3")>]
[<TestCase(78, TestName = "Gilmore #4")>]
[<TestCase(79, TestName = "Gilmore #5")>]
[<TestCase(80, TestName = "Gilmore #6")>]
[<TestCase(81, TestName = "Gilmore #7")>]
[<TestCase(82, TestName = "Gilmore #8")>]
[<TestCase(83, TestName = "Gilmore #9", Category = "LongRunning")>]
[<TestCase(84, TestName = "Davis Putnam #1")>]
[<TestCase(88, TestName = "Los #1")>]

let ``Positive Resolution`` (idx) =
    let (formula, _) = resolutionValues.[idx]
    let (_, result) = resolutionValues.[idx]
    resolution003 (parse formula) 
    |> should equal result

[<TestCase(84, TestName = "Davis Putnam #1")>]

let ``Basic Resolution`` (idx) =
    let (formula, _) = resolutionValues.[idx]
    let (_, result) = resolutionValues.[idx]
    resolution001 (parse formula) 
    |> should equal result

[<TestCase(84, TestName = "Davis Putnam #1")>]

let ``Resolution with subsumption and tautology deletion`` (idx) =
    let (formula, _) = resolutionValues.[idx]
    let (_, result) = resolutionValues.[idx]
    resolution002 (parse formula) 
    |> should equal result
