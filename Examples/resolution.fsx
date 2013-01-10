// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.unif
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.resolution

fsi.AddPrinter sprint_term
fsi.AddPrinter sprint_fol_formula

// pg. 181
// ------------------------------------------------------------------------- //
// Barber's paradox is an example of why we need factoring.                  //
// ------------------------------------------------------------------------- //

// resolution.p001
// Barber's paradox
simpcnf(skolemize(Not barb));;

// pg. 185
// ------------------------------------------------------------------------- //
// Simple example that works well.                                           //
// ------------------------------------------------------------------------- //

// resolution.p002
// Davis Putnam #1
let davis_putnam_example001 = resolution001 (parse @"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// pg. 192
// ------------------------------------------------------------------------- //
// This is now a lot quicker.                                                //
// ------------------------------------------------------------------------- //

// resolution.p003
// Davis Putnam #1
let davis_putnam_example002 = resolution002 (parse @"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// pg. 198
// ------------------------------------------------------------------------- //
// Example: the (in)famous Los problem.                                      //
// ------------------------------------------------------------------------- //

// resolution.p004
// Los #1
let losp = time presolution (parse @"
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))");;

// ------------------------------------------------------------------------- //
// The Pelletier examples again.                                             //
// ------------------------------------------------------------------------- //

// resolution.p005
// Pelletier #01
let p1p = time presolution (parse @"
    p ==> q <=> ~q ==> ~p");;

// resolution.p006
// Pelletier #02
let p2p = time presolution (parse @"
    ~ ~p <=> p");;

// resolution.p007
// Pelletier #03
let p3p = time presolution (parse @"
    ~(p ==> q) ==> q ==> p");;

// resolution.p008
// Pelletier #04
let p4p = time presolution (parse @"
    ~p ==> q <=> ~q ==> p");;

// resolution.p009
// Pelletier #05
let p5p = time presolution (parse @"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

// resolution.p010
// Pelletier #06
let p6p = time presolution (parse @"
    p \/ ~p");;

// resolution.p011
// Pelletier #07
let p7p = time presolution (parse @"
    p \/ ~ ~ ~p");;

// resolution.p012
// Pelletier #08
let p8p = time presolution (parse @"
    ((p ==> q) ==> p) ==> p");;

// resolution.p013
// Pelletier #09
let p9p = time presolution (parse @"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

// resolution.p014
// Pelletier #10
let p10p = time presolution (parse @"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

// resolution.p015
// Pelletier #11
let p11p = time presolution (parse @"
    p <=> p");;

// resolution.p016
// Pelletier #12
let p12p = time presolution (parse @"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

// resolution.p017
// Pelletier #13
let p13p = time presolution (parse @"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

// resolution.p018
// Pelletier #14
let p14p = time presolution (parse @"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

// resolution.p019
// Pelletier #15
let p15p = time presolution (parse @"
    p ==> q <=> ~p \/ q");;

// resolution.p020
// Pelletier #16
let p16p = time presolution (parse @"
    (p ==> q) \/ (q ==> p)");;

// resolution.p021
// Pelletier #17
let p17p = time presolution (parse @"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// ------------------------------------------------------------------------- //
// Monadic Predicate Logic.                                                  //
// ------------------------------------------------------------------------- //

// resolution.p022
// Pelletier #18
let p18p = time presolution (parse @"
    exists y. forall x. P(y) ==> P(x)");;

// resolution.p023
// Pelletier #19
let p19p = time presolution (parse @"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

// resolution.p024
// Pelletier #20
let p20p = time presolution (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// resolution.p025
// Pelletier #21
let p21p = time presolution (parse @"
    (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

// resolution.p026
// Pelletier #22
let p22p = time presolution (parse @"
    (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

// resolution.p027
// Pelletier #23
let p23p = time presolution (parse @"
    (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

// resolution.p028
// Pelletier #24
let p24p = time presolution (parse @"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))");;

// resolution.p029
// Pelletier #25
let p25p = time presolution (parse @"
    (exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

// resolution.p030
// Pelletier #26
let p26p = time presolution (parse @"
    ((exists x. P(x)) <=> (exists x. Q(x))) /\
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
    ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))");;

// resolution.p031
// Pelletier #27
let p27p = time presolution (parse @"
    (exists x. P(x) /\ ~Q(x)) /\
    (forall x. P(x) ==> R(x)) /\
    (forall x. U(x) /\ V(x) ==> P(x)) /\
    (exists x. R(x) /\ ~Q(x))
    ==> (forall x. V(x) ==> ~R(x))
        ==> (forall x. U(x) ==> ~V(x))");;

// resolution.p032
// Pelletier #28
let p28p = time presolution (parse @"
    (forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))");;

// resolution.p033
// Pelletier #29
let p29p = time presolution (parse @"
    (exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

// resolution.p034
// Pelletier #30
let p30p = time presolution (parse @"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))");;

// resolution.p035
// Pelletier #31
let p31p = time presolution (parse @"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))");;

// resolution.p036
// Pelletier #32
let p32p = time presolution (parse @"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))");;

// resolution.p037
// Pelletier #33
let p33p = time presolution (parse @"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

// resolution.p038
// Pelletier #34
let p34p = time presolution (parse @"
    ((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))");;

// resolution.p039
// Pelletier #35
let p35p = time presolution (parse @"
    exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// ------------------------------------------------------------------------- //
// Full predicate logic (without Identity and Functions)                     //
// ------------------------------------------------------------------------- //

// resolution.p040
// Pelletier #36
let p36p = time presolution (parse @"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))");;

// resolution.p041
// Pelletier #37
let p37p = time presolution (parse @"
    (forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))");;

// resolution.p042
// long running
// Pelletier #38
let p38p = time presolution (parse @"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

// resolution.p043
// Pelletier #39
let p39p = time presolution (parse @"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

// resolution.p044
// Pelletier #40
let p40p = time presolution (parse @"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

// resolution.p045
// Pelletier #41
let p41p = time presolution (parse @"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))");;

// resolution.p046
// Pelletier #42
let p42p = time presolution (parse @"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// resolution.p047
// long running
// Pelletier #43
let p43p = time presolution (parse @"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)");;

// resolution.p048
// Pelletier #44
let p44p = time presolution (parse @"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))");;

// resolution.p049
// Pelletier #45
let p45p = time presolution (parse @"
    (forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

// resolution.p050
// Pelletier #46
let p46p = time presolution (parse @"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))");;

// ------------------------------------------------------------------------- //
// Example from Manthey and Bry, CADE-9.                                     //
// ------------------------------------------------------------------------- //

// resolution.p051
// Pelletier #55
let p55p = time presolution (parse @"
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

// resolution.p052
// Pelletier #57
let p57p = time presolution (parse @"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))");;

// ------------------------------------------------------------------------- //
// See info-hol, circa 1500.                                                 //
// ------------------------------------------------------------------------- //

// resolution.p053
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
let p58p = time presolution (parse @"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

// resolution.p054
// Pelletier #59
let p59p = time presolution (parse @"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

// resolution.p055
// Pelletier #60
let p60p = time presolution (parse @"
    forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// ------------------------------------------------------------------------- //
// From Gilmore's classic paper.                                             //
// ------------------------------------------------------------------------- //

// resolution.p056
// Gilmore #1
let gilmore_1p = time presolution (parse @"
    exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)");;

// resolution.p057
// Gilmore #2
// long running
//** This is not valid, according to Gilmore
let gilmore_2p = time presolution (parse @"
    exists x y. forall z. 
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
        ==> (F(x,y) <=> F(x,z))");;

// resolution.p058
// Gilmore #3
let gilmore_3p = time presolution (parse @"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

// resolution.p059
// Gilmore #4
let gilmore_4p = time presolution (parse @"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))");;

// resolution.p060
// Gilmore #5
let gilmore_5p = time presolution (parse @"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

// resolution.p061
// Gilmore #6
let gilmore_6p = time presolution (parse @"
    forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))");;

// resolution.p062
// Gilmore #7
let gilmore_7p = time presolution (parse @"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)");;

// resolution.p063
// Gilmore #8
let gilmore_8p = time presolution (parse @"
    exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)");;

// resolution.p064
// Gilmore #9
// long running
let gilmore_9p = time presolution (parse @"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))");;

// ------------------------------------------------------------------------- //
// Example from Davis-Putnam papers where Gilmore procedure is poor.         //
// ------------------------------------------------------------------------- //

// resolution.p065
// Davis Putnam #1
let davis_putnam_examplep = time presolution (parse @"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// ------------------------------------------------------------------------- //
// Example                                                                   //
// ------------------------------------------------------------------------- //

// resolution.p066
// Gilmore #1
// Real: 00:00:11.829, CPU: 00:00:11.812, GC gen0: 71, gen1: 71, gen2: 0
let gilmore_1 = time resolution003 (parse @"
    exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)");;

// ------------------------------------------------------------------------- //
// Pelletiers yet again.                                                     //
// ------------------------------------------------------------------------- //

// resolution.p067
// Pelletier #01
let p1r = time resolution003 (parse @"
    p ==> q <=> ~q ==> ~p");;

// resolution.p068
// Pelletier #02
let p2r = time resolution003 (parse @"
    ~ ~p <=> p");;

// resolution.p069
// Pelletier #03
let p3r = time resolution003 (parse @"
    ~(p ==> q) ==> q ==> p");;

// resolution.p070
// Pelletier #04
let p4r = time resolution003 (parse @"
    ~p ==> q <=> ~q ==> p");;

// resolution.p071
// Pelletier #05
let p5r = time resolution003 (parse @"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

// resolution.p072
// Pelletier #06
let p6r = time resolution003 (parse @"
    p \/ ~p");;

// resolution.p073
// Pelletier #07
let p7r = time resolution003 (parse @"
    p \/ ~ ~ ~p");;

// resolution.p074
// Pelletier #08
let p8r = time resolution003 (parse @"
    ((p ==> q) ==> p) ==> p");;

// resolution.p075
// Pelletier #09
let p9r = time resolution003 (parse @"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

// resolution.p076
// Pelletier #10
let p10r = time resolution003 (parse @"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

// resolution.p077
// Pelletier #11
let p11r = time resolution003 (parse @"
    p <=> p");;

// resolution.p078
// Pelletier #12
let p12r = time resolution003 (parse @"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

// resolution.p079
// Pelletier #13
let p13r = time resolution003 (parse @"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

// resolution.p080
// Pelletier #14
let p14r = time resolution003 (parse @"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

// resolution.p081
// Pelletier #15
let p15r = time resolution003 (parse @"
    p ==> q <=> ~p \/ q");;

// resolution.p082
// Pelletier #16
let p16r = time resolution003 (parse @"
    (p ==> q) \/ (q ==> p)");;

// resolution.p083
// Pelletier #17
let p17r = time resolution003 (parse @"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// ------------------------------------------------------------------------- //
// Monadic Predicate Logic.                                                  //
// ------------------------------------------------------------------------- //

// resolution.p084
// Pelletier #18
let p18r = time resolution003 (parse @"
    exists y. forall x. P(y) ==> P(x)");;

// resolution.p085
// Pelletier #19
let p19r = time resolution003 (parse @"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

// resolution.p086
// Pelletier #20
let p20r = time resolution003 (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// resolution.p087
// Pelletier #21
let p21r = time resolution003 (parse @"
    (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

// resolution.p088
// Pelletier #22
let p22r = time resolution003 (parse @"
    (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

// resolution.p089
// Pelletier #23
let p23r = time resolution003 (parse @"
    (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

// resolution.p090
// Pelletier #24
let p24r = time resolution003 (parse @"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))");;

// resolution.p091
// Pelletier #25
let p25r = time resolution003 (parse @"
    (exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

// resolution.p092
// Pelletier #26
let p26r = time resolution003 (parse @"
    ((exists x. P(x)) <=> (exists x. Q(x))) /\
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
    ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))");;

// resolution.p093
// Pelletier #27
let p27r = time resolution003 (parse @"
    (exists x. P(x) /\ ~Q(x)) /\
    (forall x. P(x) ==> R(x)) /\
    (forall x. U(x) /\ V(x) ==> P(x)) /\
    (exists x. R(x) /\ ~Q(x))
    ==> (forall x. V(x) ==> ~R(x))
        ==> (forall x. U(x) ==> ~V(x))");;

// resolution.p094
// Pelletier #28
let p28r = time resolution003 (parse @"
    (forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))");;

// resolution.p095
// Pelletier #29
let p29r = time resolution003 (parse @"
    (exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

// resolution.p096
// Pelletier #30
let p30r = time resolution003 (parse @"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))");;

// resolution.p097
// Pelletier #31
let p31r = time resolution003 (parse @"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))");;

// resolution.p098
// Pelletier #32
let p32r = time resolution003 (parse @"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))");;

// resolution.p099
// Pelletier #33
let p33r = time resolution003 (parse @"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

// resolution.p100
// Pelletier #34
let p34r = time resolution003 (parse @"
    ((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))");;

// resolution.p101
// Pelletier #35
let p35r = time resolution003 (parse @"
    exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// ------------------------------------------------------------------------- //
// Full predicate logic (without Identity and Functions)                     //
// ------------------------------------------------------------------------- //

// resolution.p102
// Pelletier #36
let p36r = time resolution003 (parse @"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))");;

// resolution.p103
// Pelletier #37
let p37r = time resolution003 (parse @"
    (forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))");;

// resolution.p104
// long running
// Pelletier #38
let p38r = time resolution003 (parse @"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

// resolution.p105
// Pelletier #39
let p39r = time resolution003 (parse @"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

// resolution.p106
// Pelletier #40
let p40r = time resolution003 (parse @"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

// resolution.p107
// Pelletier #41
let p41r = time resolution003 (parse @"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))");;

// resolution.p108
// Pelletier #42
let p42r = time resolution003 (parse @"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// resolution.p109
// long running
// Pelletier #43
let p43r = time resolution003 (parse @"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)");;

// resolution.p110
// Pelletier #44
let p44r = time resolution003 (parse @"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))");;

// resolution.p111
// Real: 00:01:26.218, CPU: 00:01:26.140, GC gen0: 440, gen1: 62, gen2: 1
// Pelletier #45
let p45r = time resolution003 (parse @"
    (forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

// resolution.p112
// Pelletier #46
// Real: 00:00:20.876, CPU: 00:00:20.750, GC gen0: 108, gen1: 3, gen2: 1
let p46r = time resolution003 (parse @"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))");;

// ------------------------------------------------------------------------- //
// Example from Manthey and Bry, CADE-9.                                     //
// ------------------------------------------------------------------------- //

// resolution.p113
// Pelletier #55
let p55r = time resolution003 (parse @"
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

// resolution.p114
// Pelletier #57
let p57r = time resolution003 (parse @"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))");;

// ------------------------------------------------------------------------- //
// See info-hol, circa 1500.                                                 //
// ------------------------------------------------------------------------- //

// resolution.p115
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
let p58r = time resolution003 (parse @"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

// resolution.p116
// Pelletier #59
let p59r = time resolution003 (parse @"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

// resolution.p117
// Pelletier #60
let p60r = time resolution003 (parse @"
    forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// ------------------------------------------------------------------------- //
// From Gilmore's classic paper.                                             //
// ------------------------------------------------------------------------- //

// resolution.p118
// Gilmore #1
// Real: 00:00:12.059, CPU: 00:00:11.906, GC gen0: 71, gen1: 2, gen2: 0
let gilmore_1r = time resolution003 (parse @"
    exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)");;

// resolution.p119
// Gilmore #2
// long running
//** This is not valid, according to Gilmore
let gilmore_2r = time resolution003 (parse @"
    exists x y. forall z. 
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
        ==> (F(x,y) <=> F(x,z))");;

// resolution.p120
// Gilmore #3
let gilmore_3r = time resolution003 (parse @"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

// resolution.p121
// Gilmore #3
let gilmore_4r = time resolution003 (parse @"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z)");;

// resolution.p122
// Gilmore #5
let gilmore_5r = time resolution003 (parse @"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

// resolution.p123
// Gilmore #6
let gilmore_6r = time resolution003 (parse @"
    forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))");;

// resolution.p124
// Gilmore #7
let gilmore_7r = time resolution003 (parse @"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)");;

// resolution.p125
// Gilmore #8
let gilmore_8r = time resolution003 (parse @"
    exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)");;

// resolution.p126
// Gilmore #9
// long running
let gilmore_9r = time resolution003 (parse @"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))");;

// ------------------------------------------------------------------------- //
// Example from Davis-Putnam papers where Gilmore procedure is poor.         //
// ------------------------------------------------------------------------- //

// resolution.p127
// Davis Putnam #1
let davis_putnam_exampler = time resolution003 (parse @"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// ------------------------------------------------------------------------- //
// The (in)famous Los problem.                                               //
// ------------------------------------------------------------------------- //

// resolution.p128
// Los #1
// Real: 00:00:14.421, CPU: 00:00:14.390, GC gen0: 76, gen1: 2, gen2: 0
let losr = time resolution003 (parse @"
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))");;
