// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.dp
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.resolution
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.decidable

fsi.AddPrinter sprint_fol_formula

// pg. 309
// ------------------------------------------------------------------------- //
// Special procedures for decidable subsets of first order logic.            //
// ------------------------------------------------------------------------- //

//pg. 309
// Process is terminated due to StackOverflowException, even with 16MB stack
meson002 (parse @"forall x. p(x)")

// Process is terminated due to StackOverflowException, even with 16MB stack
tab (parse @"forall x. p(x)") 

// pg. 309
// ------------------------------------------------------------------------- //
// Resolution does actually terminate with failure in simple cases!          //
// ------------------------------------------------------------------------- //

// System.Exception: No proof found.
resolution001 (parse @"forall x. p(x)")

// pg. 309
// ------------------------------------------------------------------------- //
// The Los example; see how Skolemized form has no non-nullary functions.    //
// ------------------------------------------------------------------------- //

let los = 
    (parse @"
    (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. P(x,y) ==> P(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))")
print_fol_formula los

skolemize(Not los)
skolemize(Not los)

// pg. 310
// ------------------------------------------------------------------------- //
// The old DP procedure works.                                               //
// ------------------------------------------------------------------------- //

davisputnam los

// pg. 310
// ------------------------------------------------------------------------- //
// In this case it's quicker.                                                //
// ------------------------------------------------------------------------- //

aedecide los

// pg. 312
// ------------------------------------------------------------------------- //
// Show how we need to do PNF transformation with care.                      //
// ------------------------------------------------------------------------- //

let fm001 = (parse @"(forall x. p(x)) \/ (exists y. p(y))")
pnf fm001

// pg. 312
// ------------------------------------------------------------------------- //
// Also the group theory problem.                                            //
// ------------------------------------------------------------------------- //

// Real: 00:03:13.533, CPU: 00:05:45.906, GC gen0: 35, gen1: 20, gen2: 0
Initialization.runWith16MBStack (fun () ->
    aedecide (parse @"
    (forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\
    (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
    ==> forall a b c. P(a,b,c) ==> P(b,a,c)"))
  
// Real: 00:11:45.855, CPU: 00:11:43.421, GC gen0: 55, gen1: 19, gen2: 1
Initialization.runWith16MBStack (fun () ->
    aedecide (parse @"
    (forall x. P(x,x,1)) /\
    (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
    ==> forall a b c. P(a,b,c) ==> P(b,a,c)"))

// pg. 313
// ------------------------------------------------------------------------- //
// A bigger example.                                                         //
// ------------------------------------------------------------------------- //

Initialization.runWith16MBStack (fun () -> 
    aedecide (parse @"
    (exists x. P(x)) /\ (exists x. G(x))
    ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))"))

// pg. 313
// ------------------------------------------------------------------------- //
// The following, however, doesn't work with aedecide.                       //
// ------------------------------------------------------------------------- //

// This is p18

// System.Exception: Not decidable
aedecide (parse @"exists y. forall x. P(y) ==> P(x)")

davisputnam (parse @"exists y. forall x. P(y) ==> P(x)")

// pg. 315
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

miniscope(nnf (parse @"exists y. forall x. P(y) ==> P(x)"))

let fm002 =
    miniscope(nnf (parse @"(
    forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"))

nnf fm002

// pg. 316
// ------------------------------------------------------------------------- //
// It works well on simple monadic formulas.                                 //
// ------------------------------------------------------------------------- //

// val it : bool = true
wang
    (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")
   
// pg. 316
// ------------------------------------------------------------------------- //
// But not on this one!                                                      //
// ------------------------------------------------------------------------- //

// Note: This works, but the output is huge.
let fm003 = 
    pnf(nnf(miniscope(nnf (parse @"
    ((exists x. forall y. P(x) <=> P(y)) <=>
        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
        ((exists x. P(x)) <=> (forall y. P(y))))"))))

// pg. 319
// ------------------------------------------------------------------------- //
// Checking classic Aristotelean syllogisms.                                 //
// ------------------------------------------------------------------------- //

let all_valid_syllogisms = List.filter aedecide all_possible_syllogisms
List.length all_valid_syllogisms
List.map anglicize_syllogism all_valid_syllogisms

// pg. 320
// ------------------------------------------------------------------------- //
// We can "fix" the traditional list by assuming nonemptiness.               //
// ------------------------------------------------------------------------- //

// Note: This works, but the output is huge.
let all_valid_syllogisms' = List.filter aedecide all_possible_syllogisms'
List.length all_valid_syllogisms'
List.map (anglicize_syllogism << consequent) all_valid_syllogisms'

// pg. 323
// ------------------------------------------------------------------------- //
// Decision procedure in principle for formulas with finite model property.  //
// ------------------------------------------------------------------------- //

decide_fmp
    (parse @"
    (forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)")

decide_fmp
    (parse @"
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)")

//** This fails to terminate: has countermodels, but only infinite ones
// Process is terminated due to StackOverflowException, even with 16MB stack
Initialization.runWith16MBStack (fun () -> 
    decide_fmp (parse @"
    ~((forall x. ~R(x,x)) /\ 
    (forall x. exists z. R(x,z)) /\ 
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))"))

// pg. 325
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

decide_monadic
    (parse @"
    ((exists x. forall y. P(x) <=> P(y)) <=>
        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))")

// This is not feasible
// Process is terminated due to StackOverflowException.
//decide_monadic
//    (parse @"
//    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
//    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")

// pg. 326
// ------------------------------------------------------------------------- //
// Little auxiliary results for failure of finite model property.            //
// ------------------------------------------------------------------------- //

//** Our claimed equivalences are indeed correct **//

meson002 (parse @"
    (exists x y z. forall u.
        R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=>
    ~((forall x. ~R(x,x)) /\
        (forall x. exists z. R(x,z)) /\
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))")

meson002 
    (parse @"
    (exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=>
    ~((forall x. ~R(x,x)) /\
        (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))")

//** The second formula implies the first **//

meson002 (parse @"
    ~((forall x. ~R(x,x)) /\
        (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))
    ==> ~((forall x. ~R(x,x)) /\
        (forall x. exists z. R(x,z)) /\
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))")
