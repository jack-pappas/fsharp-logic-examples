// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.initialization
open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.herbrand
open FSharpx.Books.AutomatedReasoning.tableaux

fsi.AddPrinter sprint_fol_formula

// pg. 175
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// tableaux.p001
// Pelletier #20
let p20p = prawitz (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// tableaux.p002
// Pelletier #19
let p19c = compare (parse @"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

// tableaux.p003
// Pelletier #20
let p20c = compare (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) 
    ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// tableaux.p004
// Pelletier #24
let p24c = compare (parse @"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) 
    ==> (exists x. P(x) /\ R(x))");;

// tableaux.p005
// Pelletier #39
let p39c = compare (parse @"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

// tableaux.p006
// Pelletier #42
let p42c = compare (parse @"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// tableaux.p007
// Pelletier #43
let p43c = compare (parse @"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)");;

// tableaux.p008
// Pelletier #44
let p44c = compare (parse @"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) 
    ==> (exists x. J(x) /\ ~P(x))");;

// tableaux.p009
// Pelletier #59
let p59c = compare (parse @"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

// tableaux.p010
// Pelletier #60
let p60c = compare (parse @"
    forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// pg. 178
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// tableaux.p011
// Pelletier #38
let p38t = tab (parse @"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

// pg. 178
// ------------------------------------------------------------------------- //
// Example: the Andrews challenge.                                           //
// ------------------------------------------------------------------------- //

// tableaux.p012
// Pelletier #34
let p34s = splittab (parse @"
    ((exists x. forall y. P(x) <=> P(y)) <=>
        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
        ((exists x. P(x)) <=> (forall y. P(y))))");;

// pg. 179
// ------------------------------------------------------------------------- //
// Another nice example from EWD 1062.                                       //
// ------------------------------------------------------------------------- //

// tableaux.p013
// Dijkstra #1
let ewd1062 = time splittab (parse @"
    (forall x. x <= x) /\ 
    (forall x y z. x <= y /\ y <= z ==> x <= z) /\ 
    (forall x y. f(x) <= y <=> x <= g(y)) 
    ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ 
        (forall x y. x <= y ==> g(x) <= g(y))");;

// ------------------------------------------------------------------------- //
// Do all the equality-free Pelletier problems, and more, as examples.       //
// ------------------------------------------------------------------------- //

// tableaux.p014
// Pelletier #01
let p1 = time splittab (parse @"
    p ==> q <=> ~q ==> ~p");;

// tableaux.p015
// Pelletier #02
let p2 = time splittab (parse @"
    ~ ~p <=> p");;

// tableaux.p016
// Pelletier #03
let p3 = time splittab (parse @"
    ~(p ==> q) ==> q ==> p");;

// tableaux.p017
// Pelletier #04
let p4 = time splittab (parse @"
    ~p ==> q <=> ~q ==> p");;

// tableaux.p018
// Pelletier #05
let p5 = time splittab (parse @"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

// tableaux.p019
// Pelletier #06
let p6 = time splittab (parse @"
    p \/ ~p");;

// tableaux.p020
// Pelletier #07
let p7 = time splittab (parse @"
    p \/ ~ ~ ~p");;

// tableaux.p021
// Pelletier #08
let p8 = time splittab (parse @"
    ((p ==> q) ==> p) ==> p");;

// tableaux.p022
// Pelletier #09
let p9 = time splittab (parse @"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

// tableaux.p023
// Pelletier #10
let p10 = time splittab (parse @"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

// tableaux.p024
// Pelletier #11
let p11 = time splittab (parse @"
    p <=> p");;

// tableaux.p025
// Pelletier #12
let p12 = time splittab (parse @"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

// tableaux.p026
// Pelletier #13
let p13 = time splittab (parse @"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

// tableaux.p027
// Pelletier #14
let p14 = time splittab (parse @"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

// tableaux.p028
// Pelletier #15
let p15 = time splittab (parse @"
    p ==> q <=> ~p \/ q");;

// tableaux.p029
// Pelletier #16
let p16 = time splittab (parse @"
    (p ==> q) \/ (q ==> p)");;

// tableaux.p030
// Pelletier #17
let p17 = time splittab (parse @"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// ------------------------------------------------------------------------- //
// Pelletier problems: monadic predicate logic.                              //
// ------------------------------------------------------------------------- //

// tableaux.p031
// Pelletier #18
let p18 = time splittab (parse @"
    exists y. forall x. P(y) ==> P(x)");;

// tableaux.p032
// Pelletier #19
let p19 = time splittab (parse @"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

// tableaux.p033
// Pelletier #20
let p20 = time splittab (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// tableaux.p034
// Pelletier #21
let p21 = time splittab (parse @"
    (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

// tableaux.p035
// Pelletier #22
let p22 = time splittab (parse @"
    (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

// tableaux.p036
// Pelletier #23
let p23 = time splittab (parse @"
    (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

// tableaux.p037
// Pelletier #24
let p24 = time splittab (parse @"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))");;

// tableaux.p038
// Pelletier #25
let p25 = time splittab (parse @"
    (exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

// tableaux.p039
// Pelletier #26
let p26 = time splittab (parse @"
    ((exists x. P(x)) <=> (exists x. Q(x))) /\
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
    ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))");;

let p27 = time splittab (parse @"
    (exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. V(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))");;

// tableaux.p041
// Pelletier #28

// TODO: Is this a conrrect translation from Pelletier #28 based on Errata? 
// Should (forall x. P(x) ==> (forall x. Q(x)))
// be     forall x. (P(x) ==> (forall x. Q(x)))

// S -> R
// F -> L
// G -> M

let p28 = time splittab (parse @"
    (forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))");;

// tableaux.p042
// Pelletier #29
let p29 = time splittab (parse @"
    (exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

// tableaux.p043
// Pelletier #30
let p30 = time splittab (parse @"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))");;

// tableaux.p044
// Pelletier #31
let p31 = time splittab (parse @"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))");;

// tableaux.p045
// Pelletier #32
let p32 = time splittab (parse @"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))");;

// tableaux.p046
// Pelletier #33
// TOOD: Is this a conrrect translation from Pelletier #33? i.e. where are the negations?
let p33 = time splittab (parse @"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

// tableaux.p047
// Pelletier #34
let p34 = time splittab (parse @"
    ((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))");;

// tableaux.p048
// Pelletier #35
let p35 = time splittab (parse @"
    exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// ------------------------------------------------------------------------- //
// Full predicate logic (without identity and functions).                    //
// ------------------------------------------------------------------------- //

// tableaux.p049
// Pelletier #36
let p36 = time splittab (parse @"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))");;

// tableaux.p050
// Pelletier #37
let p37 = time splittab (parse @"
    (forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))");;

// tableaux.p051
// Pelletier #38
let p38 = time splittab (parse @"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

// tableaux.p052
// Pelletier #39
let p39 = time splittab (parse @"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

// tableaux.p053
// Pelletier #40
let p40 = time splittab (parse @"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

// tableaux.p054
// Pelletier #41
let p41 = time splittab (parse @"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))");;

// tableaux.p055
// Pelletier #42
let p42 = time splittab (parse @"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// tableaux.p056
// Pelletier #43
let p43 = time splittab (parse @"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)");;

// tableaux.p057
// Pelletier #44
let p44 = time splittab (parse @"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))");;

// tableaux.p058
// Pelletier #45
let p45 = time splittab (parse @"
    (forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

// tableaux.p059
// Pelletier #46
let p46 = time splittab (parse @"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))");;

// ------------------------------------------------------------------------- //
// Well-known "Agatha" example; cf. Manthey and Bry, CADE-9.                 //
// ------------------------------------------------------------------------- //

// tableaux.p060
// Pelletier #55
let p55 = time splittab (parse @"
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

// tableaux.p061
// Pelletier #57
let p57 = time splittab (parse @"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))");;

// ------------------------------------------------------------------------- //
// See info-hol, circa 1500.                                                 //
// ------------------------------------------------------------------------- //

// tableaux.p062
// Pelletier #58 1
// TODO: Is this a conrrect translation from Pelletier #58?
let p58 = time splittab (parse @"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

// tableaux.p063
// Pelletier #59
let p59 = time splittab (parse @"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

// tableaux.p064
// Pelletier #60
let p60 = time splittab (parse @"
    forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// ------------------------------------------------------------------------- //
// From Gilmore's classic paper.                                             //
// ------------------------------------------------------------------------- //

// tableaux.p065
// Gilmore #1
//**** This is still too hard for us! Amazing...
// long running
let gilmore_1 =
    time runWithEnlargedStack (fun () ->
        splittab (parse @"
            exists x. forall y z. 
            ((F(y) ==> G(y)) <=> F(x)) /\ 
            ((F(y) ==> H(y)) <=> G(x)) /\ 
            (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
            => F(z) /\ G(z) /\ H(z)"));;

// tableaux.p066
// Gilmore #2
//** This is not valid, according to Gilmore
// long running
let gilmore_2 = 
    time runWithEnlargedStack (fun () ->
        splittab (parse @"
            exists x y. forall z. 
            (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
            ==> (F(x,y) <=> F(x,z))"));;

// tableaux.p067
// Gilmore #3
let gilmore_3 = time splittab (parse @"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

// tableaux.p068
// Gilmore #4
let gilmore_4 = time splittab (parse @"
    exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))");;

// tableaux.p069
// Gilmore #5
let gilmore_5 = time splittab (parse @"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

// tableaux.p070
// Gilmore #6
let gilmore_6 = time splittab (parse @"
    forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))");;

// tableaux.p071
// Gilmore #7
let gilmore_7 = time splittab (parse @"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)");;

// tableaux.p072
// Gilmore #8
let gilmore_8 = time splittab (parse @"
    exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)");;

// tableaux.p073
// Gilmore #9
let gilmore_9 = time splittab (parse @"
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

// tableaux.p074
// Davis Putnam #1
let davis_putnam_example = time splittab (parse @"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;
