// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop
open FSharpx.Books.AutomatedReasoning.lcffol

fsi.AddPrinter sprint_thm

// pg. 501

// lcffol.p001
lcfrefute (parse @"p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))") 1 simpcont;;

// lcffol.p002
lcfrefute (parse @"(exists x. ~p(x)) /\ (forall x. p(x))") 1 simpcont;;

// pg. 504
//  ------------------------------------------------------------------------- // 
//  Examples in the text.                                                     // 
//  ------------------------------------------------------------------------- // 

// lcffol.p003
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
let p58 = 
    time lcffol (parse @"
        forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

// lcffol.p004
// Dijkstra #1
let ewd1062_1 = 
    time lcffol (parse @"
        (forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y)) 
        ==> (forall x y. x <= y ==> f(x) <= f(y))");;

//  ------------------------------------------------------------------------- // 
//  More exhaustive set of tests not in the main text.                        // 
//  ------------------------------------------------------------------------- // 

let timer = System.Diagnostics.Stopwatch.StartNew ();;

// lcffol.p005
// Pelletier #01
let p001 = time lcftaut (parse @"p ==> q <=> ~q ==> ~p");;

// lcffol.p006
// Pelletier #02
let p002 = time lcftaut (parse @"~ ~p <=> p");;

// lcffol.p007
// Pelletier #03
let p003 = time lcftaut (parse @"~(p ==> q) ==> q ==> p");;

// lcffol.p008
// Pelletier #04
let p004 = time lcftaut (parse @"~p ==> q <=> ~q ==> p");;

// lcffol.p009
// Pelletier #05
let p005 = time lcftaut (parse @"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

// lcffol.p010
// Pelletier #06
let p006 = time lcftaut (parse @"p \/ ~p");;

// lcffol.p011
// Pelletier #07
let p007 = time lcftaut (parse @"p \/ ~ ~ ~p");;

// lcffol.p012
// Pelletier #08
let p008 = time lcftaut (parse @"((p ==> q) ==> p) ==> p");;

// lcffol.p013
// Pelletier #09
let p009 = time lcftaut (parse @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

// lcffol.p014
// Pelletier #10
let p010 = time lcftaut (parse @"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

// lcffol.p015
// Pelletier #11
let p011 = time lcftaut (parse @"p <=> p");;

// lcffol.p016
// Pelletier #12
let p012 = time lcftaut (parse @"((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

// lcffol.p017
// Pelletier #13
let p013 = time lcftaut (parse @"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

// lcffol.p018
// Pelletier #14
let p014 = time lcftaut (parse @"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

// lcffol.p019
// Pelletier #15
let p015 = time lcftaut (parse @"p ==> q <=> ~p \/ q");;

// lcffol.p020
// Pelletier #16
let p016 = time lcftaut (parse @"(p ==> q) \/ (q ==> p)");;

// lcffol.p021
// Pelletier #17
let p017 = time lcftaut (parse @"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// lcffol.p022
// Pelletier #01
let p101 = time lcffol (parse @"p ==> q <=> ~q ==> ~p");;

// lcffol.p023
// Pelletier #02
let p102 = time lcffol (parse @"~ ~p <=> p");;

// lcffol.p024
// Pelletier #03
let p103 = time lcffol (parse @"~(p ==> q) ==> q ==> p");;

// lcffol.p025
// Pelletier #04
let p104 = time lcffol (parse @"~p ==> q <=> ~q ==> p");;

// lcffol.p026
// Pelletier #05
let p105 = time lcffol (parse @"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

// lcffol.p027
// Pelletier #06
let p106 = time lcffol (parse @"p \/ ~p");;

// lcffol.p028
// Pelletier #07
let p107 = time lcffol (parse @"p \/ ~ ~ ~p");;

// lcffol.p029
// Pelletier #08
let p108 = time lcffol (parse @"((p ==> q) ==> p) ==> p");;

// lcffol.p030
// Pelletier #09
let p109 = time lcffol (parse @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

// lcffol.p031
// Pelletier #10
let p110 = time lcffol (parse @"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

// lcffol.p032
// Pelletier #11
let p111 = time lcffol (parse @"p <=> p");;

// lcffol.p033
// Pelletier #12
let p112 = time lcffol (parse @"((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

// lcffol.p034
// Pelletier #13
let p113 = time lcffol (parse @"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

// lcffol.p035
// Pelletier #14
let p114 = time lcffol (parse @"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

// lcffol.p036
// Pelletier #15
let p115 = time lcffol (parse @"p ==> q <=> ~p \/ q");;

// lcffol.p037
// Pelletier #16
let p116 = time lcffol (parse @"(p ==> q) \/ (q ==> p)");;

// lcffol.p038
// Pelletier #17
let p117 = time lcffol (parse @"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// lcffol.p039
// Pelletier #18
let p118 = time lcffol (parse @"exists y. forall x. P(y) ==> P(x)");;

// lcffol.p040
// Pelletier #19
let p119 = time lcffol (parse @"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

// lcffol.p041
// Pelletier #20
let p120 = 
    time lcffol (parse @"
        (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// lcffol.p042
// Pelletier #21
let p121 = 
    time lcffol (parse @"
        (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
        ==> (exists x. P <=> Q(x))");;

// lcffol.p043
// Pelletier #22
let p122 = 
    time lcffol (parse @"
        (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

// lcffol.p044
// Pelletier #23
let p123 = 
    time lcffol (parse @"
        (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

// lcffol.p045
// Pelletier #24
let p124 = 
    time lcffol (parse @"
        ~(exists x. U(x) /\ Q(x)) /\
        (forall x. P(x) ==> Q(x) \/ R(x)) /\
        ~(exists x. P(x) ==> (exists x. Q(x))) /\
        (forall x. Q(x) /\ R(x) ==> U(x)) ==>
        (exists x. P(x) /\ R(x))");;

// lcffol.p046
// Pelletier #25
let p125 = 
    time lcffol (parse @"
        (exists x. P(x)) /\
        (forall x. U(x) ==> ~G(x) /\ R(x)) /\
        (forall x. P(x) ==> G(x) /\ U(x)) /\
        ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
        ==> (exists x. Q(x) /\ P(x))");;

// lcffol.p047
// Pelletier #26
let p126 = 
    time lcffol (parse @"
        ((exists x. P(x)) <=> (exists x. Q(x))) /\
        (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x))
        <=> (forall x. Q(x) ==> U(x)))");;

// lcffol.p048
// Pelletier #27
let p127 =
    time lcffol (parse @"
        (exists x. P(x) /\ ~Q(x)) /\
        (forall x. P(x) ==> R(x)) /\
        (forall x. U(x) /\ V(x) ==> P(x)) /\
        (exists x. R(x) /\ ~Q(x))
        ==> (forall x. U(x) ==> ~R(x))
            ==> (forall x. U(x) ==> ~V(x))");;

// lcffol.p049
// Pelletier #28
let p128 =
    time lcffol (parse @"
        (forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))");;

// lcffol.p050
// Pelletier #29
let p129 =
    time lcffol (parse @"
        (exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

// lcffol.p051
// Pelletier #30
let p130 =
    time lcffol (parse @"
        (forall x. P(x) \/ G(x) ==> ~H(x)) /\
        (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
        ==> (forall x. U(x))");;

// lcffol.p052
// Pelletier #31
let p131 =
    time lcffol (parse @"
        ~(exists x. P(x) /\ (G(x) \/ H(x))) /\
        (exists x. Q(x) /\ P(x)) /\
        (forall x. ~H(x) ==> J(x))
        ==> (exists x. Q(x) /\ J(x))");;

// lcffol.p053
// Pelletier #32
let p132 =
    time lcffol (parse @"
        (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
        (forall x. Q(x) /\ H(x) ==> J(x)) /\
        (forall x. R(x) ==> H(x))
        ==> (forall x. P(x) /\ R(x) ==> J(x))");;

// lcffol.p054
// Pelletier #33
let p133 =
    time lcffol (parse @"
        (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
        (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

// lcffol.p055
// Pelletier #34
// **** NEWLY HARD
// long running
let p134 =
    time lcffol (parse @"
        ((exists x. forall y. P(x) <=> P(y)) <=>
            ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
            ((exists x. P(x)) <=> (forall y. P(y))))");;

// lcffol.p056
// Pelletier #35
let p135 = time lcffol (parse @"exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// lcffol.p057
// Pelletier #36
let p136 =
    time lcffol (parse @"
        (forall x. exists y. P(x,y)) /\
        (forall x. exists y. G(x,y)) /\
        (forall x y. P(x,y) \/ G(x,y)
        ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
            ==> (forall x. exists y. H(x,y))");;

// lcffol.p058
// Pelletier #37
let p137 =
    time lcffol (parse @"
        (forall z.
            exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
            (P(y,w) ==> (exists u. Q(u,w)))) /\
        (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
        ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
        (forall x. exists y. R(x,y))");;

// lcffol.p059
// Pelletier #38
let p138 =
    time lcffol (parse @"
        (forall x.
            P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
        (forall x.
            (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
            (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

// lcffol.p060
// Pelletier #39
let p139 =
    time lcffol (parse @"
        ~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

// lcffol.p061
// Pelletier #40
let p140 =
    time lcffol (parse @"
        (exists y. forall x. P(x,y) <=> P(x,x))
        ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

// lcffol.p062
// Pelletier #41
let p141 =
    time lcffol (parse @"
        (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
        ==> ~(exists z. forall x. P(x,z))");;

// lcffol.p063
// Pelletier #42
let p142 =
    time lcffol (parse @"
        ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// lcffol.p064
// **** SEEMS HARD
// long running
// Pelletier #43
let p143 =
    time lcffol (parse @"
        (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)");;

// lcffol.p065
// Pelletier #44
let p144 =
    time lcffol (parse @"
        (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
        (exists y. G(y) /\ ~H(x,y))) /\
        (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
        (exists x. J(x) /\ ~P(x))");;

// lcffol.p066
// *** SEEMS HARD
// Pelletier #45
// Real: 00:00:14.165, CPU: 00:00:14.156, GC gen0: 115, gen1: 114, gen2: 0
let p145 =
    time lcffol (parse @"
        (forall x.
            P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
                (forall y. G(y) /\ H(x,y) ==> R(y))) /\
        ~(exists y. L(y) /\ R(y)) /\
        (exists x. P(x) /\ (forall y. H(x,y) ==>
            L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
        (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

// lcffol.p067
// Pelletier #55
// Real: 00:01:23.245, CPU: 00:01:23.203, GC gen0: 495, gen1: 9, gen2: 1
let p155 =
    time lcffol (parse @"
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
            ~killed(charles,agatha)");;

// lcffol.p068
// Pelletier #57
let p157 =
    time lcffol (parse @"
        P(f(a,b),f(b,c)) /\
        P(f(b,c),f(a,c)) /\
        (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z))
        ==> P(f(a,b),f(a,c))");;

// lcffol.p069
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
let p158 =
    time lcffol (parse @"
        forall P Q R. forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

// lcffol.p070
// Pelletier #59
let p159 = time lcffol (parse @"(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

// lcffol.p071
// Pelletier #60
let p160 =
    time lcffol (parse @"
        forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// lcffol.p072
// Gilmore #3
let gilmore_3 =
    time lcffol (parse @"
        exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> H(z)) /\
            F(x,y)
            ==> F(z,z)");;

// lcffol.p073
// Gilmore #4
// Real: 00:00:12.579, CPU: 00:00:12.562, GC gen0: 74, gen1: 2, gen2: 0
let gilmore_4 =
    time lcffol (parse @"
        exists x y. forall z.
            (F(x,y) ==> F(y,z) /\ F(z,z)) /\
            (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))");;

// lcffol.p074
// Gilmore #5
let gilmore_5 =
    time lcffol (parse @"
        (forall x. exists y. F(x,y) \/ F(y,x)) /\
        (forall x y. F(y,x) ==> F(y,y))
        ==> exists z. F(z,z)");;

// lcffol.p075
// Gilmore #6
let gilmore_6 =
    time lcffol (parse @"
        forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))");;

// lcffol.p076
// Gilmore #7
let gilmore_7 =
    time lcffol (parse @"
        (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
        (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
        ==> exists v w. K(v) /\ L(w) /\ G(v,w)");;

// lcffol.p077
// Gilmore #8
let gilmore_8 =
    time lcffol (parse @"
        exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)");;

// lcffol.p078
// Gilmore #9
// Real: 00:00:12.352, CPU: 00:00:12.328, GC gen0: 31, gen1: 3, gen2: 1
let gilmore_9 =
    time lcffol (parse @"
        forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
            ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
            ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
        ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
        ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
            (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))");;

// lcffol.p079
// Davis Putnam #1
// Real: 00:00:12.618, CPU: 00:00:12.578, GC gen0: 74, gen1: 1, gen2: 0
let davis_putnam_example =
    time lcffol (parse @"
        exists x. exists y. forall z.
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// lcffol.p080
// Dijkstra #1
// duplicate of above, used for timing.
let ewd1062_1_t =
    time lcffol (parse @"
        (forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y))");;

// lcffol.p081
// Dijkstra #2
let ewd1062_2 =
    time lcffol (parse @"
        (forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> g(x) <= g(y))");;

do
    timer.Stop ()
    printfn "Complete CPU time (user): %O" timer.Elapsed;;