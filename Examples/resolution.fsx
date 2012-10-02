// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.resolution

// pg. 181
// ------------------------------------------------------------------------- //
// Barber's paradox is an example of why we need factoring.                  //
// ------------------------------------------------------------------------- //

simpcnf(skolemize(Not barb));;

// pg. 185
// ------------------------------------------------------------------------- //
// Simple example that works well.                                           //
// ------------------------------------------------------------------------- //

let davis_putnam_example001 = resolution001 (parse "
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// pg. 192
// ------------------------------------------------------------------------- //
// This is now a lot quicker.                                                //
// ------------------------------------------------------------------------- //

let davis_putnam_example002 = resolution002 (parse "
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// pg. 198
// ------------------------------------------------------------------------- //
// Example: the (in)famous Los problem.                                      //
// ------------------------------------------------------------------------- //

let losp = time presolution (parse "
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))");;

// ------------------------------------------------------------------------- //
// The Pelletier examples again.                                             //
// ------------------------------------------------------------------------- //

let p1p = time presolution (parse "
	p ==> q <=> ~q ==> ~p");;

let p2p = time presolution (parse "
	~ ~p <=> p");;

let p3p = time presolution (parse "
	~(p ==> q) ==> q ==> p");;

let p4p = time presolution (parse "
	~p ==> q <=> ~q ==> p");;

let p5p = time presolution (parse "
	(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

let p6p = time presolution (parse "
	p \/ ~p");;

let p7p = time presolution (parse "
	p \/ ~ ~ ~p");;

let p8p = time presolution (parse "
	((p ==> q) ==> p) ==> p");;

let p9p = time presolution (parse "
	(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

let p10p = time presolution (parse "
	(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

let p11p = time presolution (parse "
	p <=> p");;

let p12p = time presolution (parse "
	((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

let p13p = time presolution (parse "
	p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

let p14p = time presolution (parse "
	(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

let p15p = time presolution (parse "
	p ==> q <=> ~p \/ q");;

let p16p = time presolution (parse "
	(p ==> q) \/ (q ==> p)");;

let p17p = time presolution (parse "
	p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// ------------------------------------------------------------------------- //
// Monadic Predicate Logic.                                                  //
// ------------------------------------------------------------------------- //

let p18p = time presolution (parse "
	exists y. forall x. P(y) ==> P(x)");;

let p19p = time presolution (parse "
	exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

let p20p = time presolution (parse "
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p21p = time presolution (parse "
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

let p22p = time presolution (parse "
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

let p23p = time presolution (parse "
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

let p24p = time presolution (parse "
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))");;

let p25p = time presolution (parse "
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

let p26p = time presolution (parse "
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

let p27p = time presolution (parse "
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))");;

let p28p = time presolution (parse "
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))");;

let p29p = time presolution (parse "
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

let p30p = time presolution (parse "
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))");;

let p31p = time presolution (parse "
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))");;

let p32p = time presolution (parse "
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))");;

let p33p = time presolution (parse "
	(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

let p34p = time presolution (parse "
	((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))");;

let p35p = time presolution (parse "
	exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// ------------------------------------------------------------------------- //
// Full predicate logic (without Identity and Functions)                     //
// ------------------------------------------------------------------------- //

let p36p = time presolution (parse "
	(forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))");;

let p37p = time presolution (parse "
	(forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))");;

// long running
//let p38p = time presolution (parse "
//    (forall x. 
//      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
//      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
//    (forall x. 
//      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
//      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
//      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

let p39p = time presolution (parse "
	~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

let p40p = time presolution (parse "
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

let p41p = time presolution (parse "
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))");;

let p42p = time presolution (parse "
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// long running
//let p43p = time presolution (parse "
//	(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
//    ==> forall x y. Q(x,y) <=> Q(y,x)");;

let p44p = time presolution (parse "
	(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))");;

let p45p = time presolution (parse "
	(forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

let p46p = time presolution (parse "
	(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))");;

// ------------------------------------------------------------------------- //
// Example from Manthey and Bry, CADE-9.                                     //
// ------------------------------------------------------------------------- //

let p55p = time presolution (parse "
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

let p57p = time presolution (parse "
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))");;

// ------------------------------------------------------------------------- //
// See info-hol, circa 1500.                                                 //
// ------------------------------------------------------------------------- //

let p58p = time presolution (parse "
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

let p59p = time presolution (parse "
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

let p60p = time presolution (parse "
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// ------------------------------------------------------------------------- //
// From Gilmore's classic paper.                                             //
// ------------------------------------------------------------------------- //

let gilmore_1p = time presolution (parse "
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)");;

// long running
//** This is not valid, according to Gilmore
//let gilmore_2p = time presolution (parse "
//    exists x y. forall z. 
//        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
//        ==> (F(x,y) <=> F(x,z))");;

let gilmore_3p = time presolution (parse "
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

let gilmore_4p = time presolution (parse "
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

let gilmore_5p = time presolution (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_6p = time presolution (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_7p = time presolution (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_8p = time presolution (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

// long running
//let gilmore_9p = time presolution (parse "
//    forall x. exists y. forall z. 
//        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
//          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
//          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
//        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
//          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
//          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
//              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))");;

// ------------------------------------------------------------------------- //
// Example from Davis-Putnam papers where Gilmore procedure is poor.         //
// ------------------------------------------------------------------------- //

let davis_putnam_examplep = time presolution (parse "
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// ------------------------------------------------------------------------- //
// Example                                                                   //
// ------------------------------------------------------------------------- //

let gilmore_1 = resolution003 (parse "
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)");;

// ------------------------------------------------------------------------- //
// Pelletiers yet again.                                                     //
// ------------------------------------------------------------------------- //

let p1r = time resolution003 (parse "
	p ==> q <=> ~q ==> ~p");;

let p2r = time resolution003 (parse "
	~ ~p <=> p");;

let p3r = time resolution003 (parse "
	~(p ==> q) ==> q ==> p");;

let p4r = time resolution003 (parse "
	~p ==> q <=> ~q ==> p");;

let p5r = time resolution003 (parse "
	(p \/ q ==> p \/ r) ==> p \/ (q ==> r)");;

let p6r = time resolution003 (parse "
	p \/ ~p");;

let p7r = time resolution003 (parse "
	p \/ ~ ~ ~p");;

let p8r = time resolution003 (parse "
	((p ==> q) ==> p) ==> p");;

let p9r = time resolution003 (parse "
	(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)");;

let p10r = time resolution003 (parse "
	(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)");;

let p11r = time resolution003 (parse "
	p <=> p");;

let p12r = time resolution003 (parse "
	((p <=> q) <=> r) <=> (p <=> (q <=> r))");;

let p13r = time resolution003 (parse "
	p \/ q /\ r <=> (p \/ q) /\ (p \/ r)");;

let p14r = time resolution003 (parse "
	(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)");;

let p15r = time resolution003 (parse "
	p ==> q <=> ~p \/ q");;

let p16r = time resolution003 (parse "
	(p ==> q) \/ (q ==> p)");;

let p17r = time resolution003 (parse "
	p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)");;

// ------------------------------------------------------------------------- //
// Monadic Predicate Logic.                                                  //
// ------------------------------------------------------------------------- //

let p18r = time resolution003 (parse "
	exists y. forall x. P(y) ==> P(x)");;

let p19r = time resolution003 (parse "
	exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)");;

let p20r = time resolution003 (parse "
	(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

let p21r = time resolution003 (parse "
	(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))");;

let p22r = time resolution003 (parse "
	(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))");;

let p23r = time resolution003 (parse "
	(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))");;

let p24r = time resolution003 (parse "
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))");;

let p25r = time resolution003 (parse "
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

let p26r = time resolution003 (parse "
	(exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))");;

let p27r = time resolution003 (parse "
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))");;

let p28r = time resolution003 (parse "
	(exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))");;

let p29r = time resolution003 (parse "
	(exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;

let p30r = time resolution003 (parse "
	(forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))");;

let p31r = time resolution003 (parse "
	~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))");;

let p32r = time resolution003 (parse "
	(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))");;

let p33r = time resolution003 (parse "
	(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))");;

let p34r = time resolution003 (parse "
	((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))");;

let p35r = time resolution003 (parse "
	exists x y. P(x,y) ==> (forall x y. P(x,y))");;

// ------------------------------------------------------------------------- //
// Full predicate logic (without Identity and Functions)                     //
// ------------------------------------------------------------------------- //

let p36r = time resolution003 (parse "
	(forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))");;

let p37r = time resolution003 (parse "
	(forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))");;

// long running
//let p38r = time resolution003 (parse "
//    (forall x. 
//      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
//      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
//    (forall x. 
//      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
//      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
//      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))");;

let p39r = time resolution003 (parse "
	~(exists x. forall y. P(y,x) <=> ~P(y,y))");;

let p40r = time resolution003 (parse "
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))");;

let p41r = time resolution003 (parse "
	(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))");;

let p42r = time resolution003 (parse "
	~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))");;

// long running
//let p43r = time resolution003 (parse "
//	(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
//    ==> forall x y. Q(x,y) <=> Q(y,x)");;

let p44r = time resolution003 (parse "
	(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))");;

let p45r = time resolution003 (parse "
	(forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

let p46r = time resolution003 (parse "
	(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))");;

// ------------------------------------------------------------------------- //
// Example from Manthey and Bry, CADE-9.                                     //
// ------------------------------------------------------------------------- //

let p55r = time resolution003 (parse "
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

let p57r = time resolution003 (parse "
	P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))");;

// ------------------------------------------------------------------------- //
// See info-hol, circa 1500.                                                 //
// ------------------------------------------------------------------------- //

let p58r = time resolution003 (parse "
	forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))");;

let p59r = time resolution003 (parse "
	(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))");;

let p60r = time resolution003 (parse "
	forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)");;

// ------------------------------------------------------------------------- //
// From Gilmore's classic paper.                                             //
// ------------------------------------------------------------------------- //

let gilmore_1r = time resolution003 (parse "
	exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)");;

// long running
//** This is not valid, according to Gilmore
//let gilmore_2r = time resolution003 (parse "
//    exists x y. forall z. 
//        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
//        ==> (F(x,y) <=> F(x,z))");;

let gilmore_3r = time resolution003 (parse "
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

let gilmore_4r = time resolution003 (parse "
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)");;

let gilmore_5r = time resolution003 (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_6r = time resolution003 (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_7r = time resolution003 (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

let gilmore_8r = time resolution003 (parse "
	(forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)");;

// long running
//let gilmore_9r = time resolution003 (parse "
//    forall x. exists y. forall z. 
//        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
//          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
//          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
//        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
//          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
//          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
//              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))");;

// ------------------------------------------------------------------------- //
// Example from Davis-Putnam papers where Gilmore procedure is poor.         //
// ------------------------------------------------------------------------- //

let davis_putnam_exampler = time resolution003 (parse "
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))");;

// ------------------------------------------------------------------------- //
// The (in)famous Los problem.                                               //
// ------------------------------------------------------------------------- //

let losr = time resolution003 (parse "
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))");;

