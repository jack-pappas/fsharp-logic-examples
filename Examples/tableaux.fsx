// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand
open Reasoning.Automated.Harrison.Handbook.tableaux

fsi.AddPrinter sprint_fol_formula

// pg. 175
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

let p20p = prawitz (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p19c = compare (parse @"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

let p20c = compare (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) 
    ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p24c = compare (parse @"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) 
    ==> (exists x. P(x) /\ R(x))");;

let p39c = compare (parse @"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

let p42c = compare (parse @"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

let p43c = compare (parse @"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)");;

let p44c = compare (parse @"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) 
    ==> (exists x. J(x) /\ ~P(x))");;

let p59c = compare (parse @"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

let p60c = compare (parse @"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// pg. 178
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

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

// pg. 179
// ------------------------------------------------------------------------- //
// Another nice example from EWD 1602.                                       //
// ------------------------------------------------------------------------- //

let ewd1062 = time splittab (parse @"
    (forall x. x <= x) /\ 
    (forall x y z. x <= y /\ y <= z ==> x <= z) /\ 
    (forall x y. f(x) <= y <=> x <= g(y)) 
    ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ 
        (forall x y. x <= y ==> g(x) <= g(y))");;

// ------------------------------------------------------------------------- //
// Do all the equality-free Pelletier problems, and more, as examples.       //
// ------------------------------------------------------------------------- //

let p1 = time splittab (parse @"
	p ==> q <=> ~q ==> ~p");;

let p2 = time splittab (parse @"
	~ ~p <=> p");;

let p3 = time splittab (parse @"
	~(p ==> q) ==> q ==> p");;

let p4 = time splittab (parse @"
	~p ==> q <=> ~q ==> p");;

let p5 = time splittab (parse @"
	(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

let p6 = time splittab (parse @"
	p \/ ~p");;

let p7 = time splittab (parse @"
	p \/ ~ ~ ~p");;

let p8 = time splittab (parse @"
	((p ==> q) ==> p) ==> p");;

let p9 = time splittab (parse @"
	(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

let p10 = time splittab (parse @"
	(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

let p11 = time splittab (parse @"
	p <=> p");;

let p12 = time splittab (parse @"
	((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

let p13 = time splittab (parse @"
	p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

let p14 = time splittab (parse @"
	(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

let p15 = time splittab (parse @"
	p ==> q <=> ~p \/ q");;

let p16 = time splittab (parse @"
	(p ==> q) \/ (q ==> p)");;

let p17 = time splittab (parse @"
	p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// ------------------------------------------------------------------------- //
// Pelletier problems: monadic predicate logic.                              //
// ------------------------------------------------------------------------- //

let p18 = time splittab (parse @"
	exists y. forall x. P(y) ==> P(x)");;

let p19 = time splittab (parse @"
	exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

let p20 = time splittab (parse @"
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p21 = time splittab (parse @"
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

let p22 = time splittab (parse @"
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

let p23 = time splittab (parse @"
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

let p24 = time splittab (parse @"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))");;

let p25 = time splittab (parse @"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

let p26 = time splittab (parse @"
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

let p27 = time splittab (parse @"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))");;

let p28 = time splittab (parse @"
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))");;

let p29 = time splittab (parse @"
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

let p30 = time splittab (parse @"
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))");;

let p31 = time splittab (parse @"
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))");;

let p32 = time splittab (parse @"
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))");;

let p33 = time splittab (parse @"
	(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

let p34 = time splittab (parse @"
	((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))");;

let p35 = time splittab (parse @"
	exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// ------------------------------------------------------------------------- //
// Full predicate logic (without identity and functions).                    //
// ------------------------------------------------------------------------- //

let p36 = time splittab (parse @"
	(forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))");;

let p37 = time splittab (parse @"
	(forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))");;

let p38 = time splittab (parse @"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

let p39 = time splittab (parse @"
	~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

let p40 = time splittab (parse @"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

let p41 = time splittab (parse @"
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))");;

let p42 = time splittab (parse @"
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

let p43 = time splittab (parse @"
	(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)");;

let p44 = time splittab (parse @"
	(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))");;

let p45 = time splittab (parse @"
	(forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

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

let p57 = time splittab (parse @"
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))");;

// ------------------------------------------------------------------------- //
// See info-hol, circa 1500.                                                 //
// ------------------------------------------------------------------------- //

let p58 = time splittab (parse @"
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

let p59 = time splittab (parse @"
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

let p60 = time splittab (parse @"
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// ------------------------------------------------------------------------- //
// From Gilmore's classic paper.                                             //
// ------------------------------------------------------------------------- //

////**** This is still too hard for us! Amazing...
//let gilmore_1 = time splittab (parse @"
//	exists x. forall y z. 
//        ((F(y) ==> G(y)) <=> F(x)) /\ 
//        ((F(y) ==> H(y)) <=> G(x)) /\ 
//        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
//        ==> F(z) /\ G(z) /\ H(z)");;

////** This is not valid, according to Gilmore
// Takes a long time to run; > 10 minutes. Did not wait for result.
//let gilmore_2 = time splittab (parse @"
//    exists x y. forall z. 
//        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
//        ==> (F(x,y) <=> F(x,z))");;

let gilmore_3 = time splittab (parse @"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

let gilmore_4 = time splittab (parse @"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

let gilmore_5 = time splittab (parse @"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_6 = time splittab (parse @"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_7 = time splittab (parse @"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_8 = time splittab (parse @"
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

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

let davis_putnam_example = time splittab (parse @"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;
