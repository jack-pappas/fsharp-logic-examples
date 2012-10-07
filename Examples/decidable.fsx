// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
//open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
//open Reasoning.Automated.Harrison.Handbook.paramodulation
open Reasoning.Automated.Harrison.Handbook.decidable

// pg. 309
// ------------------------------------------------------------------------- //
// Special procedures for decidable subsets of first order logic.            //
// ------------------------------------------------------------------------- //

//pg. 309
// Process is terminated due to StackOverflowException.
meson002 (parse @"forall x. p(x)")

// Process is terminated due to StackOverflowException.
tab (parse @"forall x. p(x)") 

// pg. 309
// ------------------------------------------------------------------------- //
// Resolution does actually terminate with failure in simple cases!          //
// ------------------------------------------------------------------------- //

// 0 used; 1 unused.
// System.Exception: No proof found
resolution001 (parse @"forall x. p(x)")

// pg. 309
// ------------------------------------------------------------------------- //
// The Los example; see how Skolemized form has no non-nullary functions.    //
// ------------------------------------------------------------------------- //

let los = (parse @"(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\  (forall x y. P(x,y) ==> P(y,x)) /\ (forall x y. P(x,y) \/ Q(x,y)) ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))")

// <<(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\ (forall x y. P(x,y) ==> P(y,x)) /\ (forall x y. P(x,y) \/ Q(x,y)) ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>
// val it : unit = ()
print_fol_formula los

skolemize(Not los)

// <<(((~P(x,y) \/ ~P(y,z)) \/ P(x,z)) /\ ((~Q(x,y) \/ ~Q(y,z)) \/ Q(x,z)) /\ (~P(x,y) \/ P(y,x)) /\ (P(x,y) \/ Q(x,y))) /\ ~P(c_x,c_y) /\ ~Q(c_x',c_y')>>
// val it : unit = ()
print_fol_formula (skolemize(Not los))

// pg. 310
// ------------------------------------------------------------------------- //
// The old DP procedure works.                                               //
// ------------------------------------------------------------------------- //

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 5 items in list
// 2 ground instances tried; 7 items in list
// 3 ground instances tried; 9 items in list
// 4 ground instances tried; 11 items in list
// 5 ground instances tried; 15 items in list
// 6 ground instances tried; 17 items in list
// 7 ground instances tried; 19 items in list
// 8 ground instances tried; 21 items in list
// 9 ground instances tried; 25 items in list
// 10 ground instances tried; 27 items in list
// 11 ground instances tried; 29 items in list
// 12 ground instances tried; 31 items in list
// 13 ground instances tried; 35 items in list
// 14 ground instances tried; 37 items in list
// 15 ground instances tried; 39 items in list
// 16 ground instances tried; 41 items in list
// 17 ground instances tried; 45 items in list
// 18 ground instances tried; 47 items in list
// 19 ground instances tried; 49 items in list
// 20 ground instances tried; 51 items in list
// 21 ground instances tried; 55 items in list
// 22 ground instances tried; 56 items in list
// 23 ground instances tried; 58 items in list
// 24 ground instances tried; 60 items in list
// 25 ground instances tried; 64 items in list
// 26 ground instances tried; 66 items in list
// 27 ground instances tried; 68 items in list
// 28 ground instances tried; 70 items in list
// 29 ground instances tried; 74 items in list
// 30 ground instances tried; 76 items in list
// 31 ground instances tried; 78 items in list
// 32 ground instances tried; 80 items in list
// 33 ground instances tried; 84 items in list
// 34 ground instances tried; 86 items in list
// 35 ground instances tried; 88 items in list
// 36 ground instances tried; 90 items in list
// 37 ground instances tried; 94 items in list
// 38 ground instances tried; 96 items in list
// 39 ground instances tried; 98 items in list
// 40 ground instances tried; 100 items in list
// 41 ground instances tried; 104 items in list
// 42 ground instances tried; 106 items in list
// 43 ground instances tried; 107 items in list
// 44 ground instances tried; 109 items in list
// val it : int = 45
davisputnam los

// pg. 310
// ------------------------------------------------------------------------- //
// In this case it's quicker.                                                //
// ------------------------------------------------------------------------- //

// val it : bool = true
aedecide los

// pg. 312
// ------------------------------------------------------------------------- //
// Show how we need to do PNF transformation with care.                      //
// ------------------------------------------------------------------------- //

let fm001 = (parse @"(forall x. p(x)) \/ (exists y. p(y))")

// <<(forall x. p(x)) \/ (exists y. p(y))>>
// val it : unit = ()
print_fol_formula fm001

pnf fm001

// <<forall x. exists y. p(x) \/ p(y)>>
// val it : unit = ()
print_fol_formula (pnf fm001)

// pg. 312
// ------------------------------------------------------------------------- //
// Also the group theory problem.                                            //
// ------------------------------------------------------------------------- //

// Process is terminated due to StackOverflowException.
aedecide (parse @"(forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\ (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) ==> forall a b c. P(a,b,c) ==> P(b,a,c)")

// Process is terminated due to StackOverflowException.
aedecide (parse @"(forall x. P(x,x,1)) /\ (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) ==> forall a b c. P(a,b,c) ==> P(b,a,c)")
   
// pg. 313
// ------------------------------------------------------------------------- //
// A bigger example.                                                         //
// ------------------------------------------------------------------------- //

// Use 10MB stackframe
// val it : bool = true
Initialization.runWithStackFrame 10000000 (fun () -> aedecide (parse @"(exists x. P(x)) /\ (exists x. G(x))
   ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))"))

// pg. 313
// ------------------------------------------------------------------------- //
// The following, however, doesn't work with aedecide.                       //
// ------------------------------------------------------------------------- //

// This is p18

// System.Exception: Not decidable
aedecide (parse @"exists y. forall x. P(y) ==> P(x)")

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 2 items in list
// 1 ground instances tried; 2 items in list
// val it : int = 2
davisputnam (parse @"exists y. forall x. P(y) ==> P(x)")

// pg. 315
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

miniscope(nnf (parse @"exists y. forall x. P(y) ==> P(x)"))

// <<(exists y. ~P(y)) \/ (forall x. P(x))>>
// val it : unit = ()
print_fol_formula (miniscope(nnf (parse @"exists y. forall x. P(y) ==> P(x)")))

let fm002 = miniscope(nnf (parse @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"))
   
// <<((exists x. P(x)) /\ (forall z. ~R(z)) /\ (exists w. ~U(w)) /\ (exists y. Q(y)) \/ (exists x. P(x)) /\ (forall z. ~R(z)) /\ (exists y. Q(y)) \/ (exists x. P(x)) /\ (exists w. ~U(w)) /\ (exists y. Q(y))) \/ ~((exists x. P(x)) /\ (exists y. Q(y))) \/ (exists z. R(z))>>
// val it : unit = ()
print_fol_formula (fm002)

pnf(nnf fm002)

// <<forall z z' x y. exists x' w y'. (P(x') /\ ~R(z) /\ ~U(w) /\ Q(y') \/ P(x') /\ ~R(z') /\ Q(w) \/ P(x') /\ ~U(w) /\ Q(y')) \/ (~P(x) \/ ~Q(y)) \/ R(x')>>
// val it : unit = ()
print_fol_formula (pnf(nnf fm002))

// pg. 316
// ------------------------------------------------------------------------- //
// It works well on simple monadic formulas.                                 //
// ------------------------------------------------------------------------- //

// val it : bool = true
wang
 (parse @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")
   
// pg. 316
// ------------------------------------------------------------------------- //
// But not on this one!                                                      //
// ------------------------------------------------------------------------- //

// Note: This works, but the output is huge.
let fm003 = pnf(nnf(miniscope(nnf (parse @"((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))"))))

// <<forall y y' y'' y''' y'''' y''''' y'''''' x y''''''' y'''''''' y''''''''' y'''''''''' y''''''''''' y'''''''''''' y''''''''''''' x' x''. exists x''' x'''' y'''''''''''''' x''''' y''''''''''''''' x'''''' x''''''' y'''''''''''''''' x'''''''' y'''''''''''''''''. (((P(x''') /\ ~P(x''')) /\ P(y) /\ (~P(y) \/ P(y)) \/ (P(x''') /\ ~P(x''')) /\ ~P(y') /\ (~P(y') \/ P(y')) \/ (P(x''') /\ ~P(x''')) /\ (~P(y'') \/ P(y'')) \/ P(x''') /\ P(y''') /\ ~P(y''') /\ (~P(y''') \/ P(y''')) \/ P(x''') /\ P(y'''') /\ (~P(y'''') \/ P(y'''')) \/ ~P(x''') /\ P(y''''') /\ ~P(y''''') /\ (~P(y''''') \/ P(y''''')) \/ ~P(x''') /\ ~P(y'''''') /\ (~P(y'''''') \/ P(y''''''))) /\ (Q(x'''') /\ Q(y) \/ ~Q(y') /\ ~Q(x'''')) \/ ((~P(x) \/ P(x)) /\ (~P(x) \/ ~P(x''')) /\ (P(x) \/ P(x'''')) /\ (~P(y'''''''''''''') \/ P(y''''''''''''''))) /\ (Q(x''''') /\ ~Q(y''''''''''''''') \/ ~Q(x) /\ Q(x))) /\ (((Q(x'''''') /\ ~Q(x'''''')) /\ Q(y) /\ (~Q(y) \/ Q(y)) \/ (Q(x'''''') /\ ~Q(x'''''')) /\ ~Q(y') /\ (~Q(y') \/ Q(y')) \/ (Q(x'''''') /\ ~Q(x'''''')) /\ (~Q(y'') \/ Q(y'')) \/ Q(x'''''') /\ Q(y''') /\ ~Q(y''') /\ (~Q(y''') \/ Q(y''')) \/ Q(x'''''') /\ Q(y'''') /\ (~Q(y'''') \/ Q(y'''')) \/ ~Q(x'''''') /\ Q(y''''') /\ ~Q(y''''') /\ (~Q(y''''') \/ Q(y''''')) \/ ~Q(x'''''') /\ ~Q(y'''''') /\ (~Q(y'''''') \/ Q(y''''''))) /\ (P(x''''''') /\ P(y) \/ ~P(y') /\ ~P(x''''''')) \/ ((~Q(x) \/ Q(x)) /\ (~Q(x) \/ ~Q(x'''''')) /\ (Q(x) \/ Q(x''''''')) /\ (~Q(y'''''''''''''''') \/ Q(y''''''''''''''''))) /\ (P(x'''''''') /\ ~P(y''''''''''''''''') \/ ~P(x) /\ P(x))) \/ (((P(x''') /\ ~P(x''')) /\ P(y''''''') /\ (~P(y''''''') \/ P(y''''''')) \/ (P(x''') /\ ~P(x''')) /\ ~P(y'''''''') /\ (~P(y'''''''') \/ P(y'''''''')) \/ (P(x''') /\ ~P(x''')) /\ (~P(y''''''''') \/ P(y''''''''')) \/ P(x''') /\ P(y'''''''''') /\ ~P(y'''''''''') /\ (~P(y'''''''''') \/ P(y'''''''''')) \/ P(x''') /\ P(y''''''''''') /\ (~P(y''''''''''') \/ P(y''''''''''')) \/ ~P(x''') /\ P(y'''''''''''') /\ ~P(y'''''''''''') /\ (~P(y'''''''''''') \/ P(y'''''''''''')) \/ ~P(x''') /\ ~P(y''''''''''''') /\ (~P(y''''''''''''') \/ P(y'''''''''''''))) /\ (Q(x'''') /\ ~Q(y'''''''''''''') \/ ~Q(y''''''') /\ Q(y''''''')) \/ ((~P(x') \/ P(x')) /\ (~P(x') \/ ~P(x''')) /\ (P(x') \/ P(x'''')) /\ (~P(y'''''''''''''') \/ P(y''''''''''''''))) /\ (Q(x''''') /\ Q(x') \/ ~Q(x'') /\ ~Q(x'''''))) /\ (((Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\ Q(y''''''') /\ (~Q(y''''''') \/ Q(y''''''')) \/ (Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\ ~Q(y'''''''') /\ (~Q(y'''''''') \/ Q(y'''''''')) \/ (Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\ (~Q(y''''''''') \/ Q(y''''''''')) \/ Q(y''''''''''''''') /\ Q(y'''''''''') /\ ~Q(y'''''''''') /\ (~Q(y'''''''''') \/ Q(y'''''''''')) \/ Q(y''''''''''''''') /\ Q(y''''''''''') /\ (~Q(y''''''''''') \/ Q(y''''''''''')) \/ ~Q(y''''''''''''''') /\ Q(y'''''''''''') /\ ~Q(y'''''''''''') /\ (~Q(y'''''''''''') \/ Q(y'''''''''''')) \/ ~Q(y''''''''''''''') /\ ~Q(y''''''''''''') /\ (~Q(y''''''''''''') \/ Q(y'''''''''''''))) /\ (P(x'''''') /\ ~P(x''''''') \/ ~P(y''''''') /\ P(y''''''')) \/ ((~Q(x') \/ Q(x')) /\ (~Q(x') \/ ~Q(y''''''''''''''')) /\ (Q(x') \/ Q(x'''''')) /\ (~Q(x''''''') \/ Q(x'''''''))) /\ (P(y'''''''''''''''') /\ P(x') \/ ~P(x'') /\ ~P(y'''''''''''''''')))>>
// val it : unit = ()
print_fol_formula fm003

// pg. 319
// ------------------------------------------------------------------------- //
// Checking classic Aristotelean syllogisms.                                 //
// ------------------------------------------------------------------------- //

let all_valid_syllogisms = List.filter aedecide all_possible_syllogisms

// <<(forall x. M(x) ==> P(x)) /\ (forall x. S(x) ==> M(x)) ==> (forall x. S(x) ==> P(x))>>
// <<(forall x. M(x) ==> P(x)) /\ (exists x. S(x) /\ M(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(forall x. M(x) ==> P(x)) /\ (exists x. M(x) /\ S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(forall x. P(x) ==> M(x)) /\ (forall x. S(x) ==> ~M(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(forall x. P(x) ==> M(x)) /\ (forall x. M(x) ==> ~S(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(forall x. P(x) ==> M(x)) /\ (exists x. S(x) /\ ~M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(forall x. M(x) ==> ~P(x)) /\ (forall x. S(x) ==> M(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(forall x. M(x) ==> ~P(x)) /\ (exists x. S(x) /\ M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(forall x. M(x) ==> ~P(x)) /\ (exists x. M(x) /\ S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(forall x. P(x) ==> ~M(x)) /\ (forall x. S(x) ==> M(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(forall x. P(x) ==> ~M(x)) /\ (exists x. S(x) /\ M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(forall x. P(x) ==> ~M(x)) /\ (exists x. M(x) /\ S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. M(x) /\ P(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x) /\ M(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. M(x) /\ ~P(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// val it : unit = ()
print_fol_formula_list all_valid_syllogisms

// val it : int = 15
List.length all_valid_syllogisms

// val it : string list =
//   ["If all M are P and all S are M, then all S are P";
//    "If all M are P and some S are M, then some S are P";
//    "If all M are P and some M are S, then some S are P";
//    "If all P are M and no S are M, then no S are P";
//    "If all P are M and no M are S, then no S are P";
//    "If all P are M and some S are not M, then some S are not P";
//    "If no M are P and all S are M, then no S are P";
//    "If no M are P and some S are M, then some S are not P";
//    "If no M are P and some M are S, then some S are not P";
//    "If no P are M and all S are M, then no S are P";
//    "If no P are M and some S are M, then some S are not P";
//    "If no P are M and some M are S, then some S are not P";
//    "If some M are P and all M are S, then some S are P";
//    "If some P are M and all M are S, then some S are P";
//    "If some M are not P and all M are S, then some S are not P"]
List.map anglicize_syllogism all_valid_syllogisms

// pg. 320
// ------------------------------------------------------------------------- //
// We can "fix" the traditional list by assuming nonemptiness.               //
// ------------------------------------------------------------------------- //

let all_valid_syllogisms' = List.filter aedecide all_possible_syllogisms'

// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> P(x)) /\ (forall x. S(x) ==> M(x)) ==> (forall x. S(x) ==> P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> P(x)) /\ (forall x. S(x) ==> M(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> P(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> P(x)) /\ (exists x. S(x) /\ M(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> P(x)) /\ (exists x. M(x) /\ S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> M(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> M(x)) /\ (forall x. S(x) ==> ~M(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> M(x)) /\ (forall x. S(x) ==> ~M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> M(x)) /\ (forall x. M(x) ==> ~S(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> M(x)) /\ (forall x. M(x) ==> ~S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> M(x)) /\ (exists x. S(x) /\ ~M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> ~P(x)) /\ (forall x. S(x) ==> M(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> ~P(x)) /\ (forall x. S(x) ==> M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> ~P(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> ~P(x)) /\ (exists x. S(x) /\ M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. M(x) ==> ~P(x)) /\ (exists x. M(x) /\ S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> ~M(x)) /\ (forall x. S(x) ==> M(x)) ==> (forall x. S(x) ==> ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> ~M(x)) /\ (forall x. S(x) ==> M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> ~M(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> ~M(x)) /\ (exists x. S(x) /\ M(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (forall x. P(x) ==> ~M(x)) /\ (exists x. M(x) /\ S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (exists x. M(x) /\ P(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (exists x. P(x) /\ M(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ P(x))>>
// <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x)) ==> (exists x. M(x) /\ ~P(x)) /\ (forall x. M(x) ==> S(x)) ==> (exists x. S(x) /\ ~P(x))>>
// val it : unit = ()
print_fol_formula_list all_valid_syllogisms'

// val it : int = 24
List.length all_valid_syllogisms'

//
List.map (anglicize_syllogism >>|> consequent) all_valid_syllogisms'

// pg. 323
// ------------------------------------------------------------------------- //
// Decision procedure in principle for formulas with finite model property.  //
// ------------------------------------------------------------------------- //

// val it : bool = true
decide_fmp
 (parse @"(forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)")

 // val it : bool = false
decide_fmp
 (parse @"(forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)")

//** This fails to terminate: has countermodels, but only infinite ones
// Process is terminated due to StackOverflowException.
decide_fmp (parse @"~((forall x. ~R(x,x)) /\ (forall x. exists z. R(x,z)) /\ (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))")

// pg. 325
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : bool = true
decide_monadic
 (parse @"((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
   ((exists x. P(x)) <=> (forall y. P(y))))")

// This is not feasible
// Process is terminated due to StackOverflowException.
decide_monadic
 (parse @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")

// pg. 326
// ------------------------------------------------------------------------- //
// Little auxiliary results for failure of finite model property.            //
// ------------------------------------------------------------------------- //

//** Our claimed equivalences are indeed correct **//

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 0
// Searching with depth limit 1
// val it : int list = [1; 3; 9; 1]
meson002 (parse @"(exists x y z. forall u. R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=> ~((forall x. ~R(x,x)) /\ (forall x. exists z. R(x,z)) /\ (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))")

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// val it : int list = [1; 6; 4]
meson002 (parse @"(exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=> ~((forall x. ~R(x,x)) /\  (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))")

//** The second formula implies the first **//

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// val it : int list = [1; 5]
meson002 (parse @"~((forall x. ~R(x,x)) /\ (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z))) ==> ~((forall x. ~R(x,x)) /\ (forall x. exists z. R(x,z)) /\ (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))")

