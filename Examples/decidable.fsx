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
open FSharpx.Books.AutomatedReasoning.dp
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.herbrand
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.resolution
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.decidable

fsi.AddPrinter sprint_fol_formula

// pg. 309
// ------------------------------------------------------------------------- //
// Special procedures for decidable subsets of first order logic.            //
// ------------------------------------------------------------------------- //


// decidable.p001
// Process is terminated due to StackOverflowException, even with 16MB stack
meson002 (parse @"forall x. p(x)")

// decidable.p002
// Process is terminated due to StackOverflowException, even with 16MB stack
tab (parse @"forall x. p(x)") 

// pg. 309
// ------------------------------------------------------------------------- //
// Resolution does actually terminate with failure in simple cases!          //
// ------------------------------------------------------------------------- //

// decidable.p003
// System.Exception: No proof found.
resolution001 (parse @"forall x. p(x)")

// pg. 309
// ------------------------------------------------------------------------- //
// The Los example; see how Skolemized form has no non-nullary functions.    //
// ------------------------------------------------------------------------- //

// Los #1
let los = 
    (parse @"
    (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. P(x,y) ==> P(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))")

// decidable.p004
skolemize(Not los)

// pg. 310
// ------------------------------------------------------------------------- //
// The old DP procedure works.                                               //
// ------------------------------------------------------------------------- //

// decidable.p005
davisputnam los

// pg. 310
// ------------------------------------------------------------------------- //
// In this case it's quicker.                                                //
// ------------------------------------------------------------------------- //

// decidable.p006
aedecide los

// pg. 312
// ------------------------------------------------------------------------- //
// Show how we need to do PNF transformation with care.                      //
// ------------------------------------------------------------------------- //

let fm001 = (parse @"(forall x. p(x)) \/ (exists y. p(y))")

// decidable.p007
pnf fm001

// pg. 312
// ------------------------------------------------------------------------- //
// Also the group theory problem.                                            //
// ------------------------------------------------------------------------- //

// decidable.p008
// Real: 00:03:13.533, CPU: 00:05:45.906, GC gen0: 35, gen1: 20, gen2: 0
runWithEnlargedStack (fun () ->
    aedecide (parse @"
    (forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\
    (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
    ==> forall a b c. P(a,b,c) ==> P(b,a,c)"))
  
// decidable.p009
// Real: 00:11:45.855, CPU: 00:11:43.421, GC gen0: 55, gen1: 19, gen2: 1
runWithEnlargedStack (fun () ->
    aedecide (parse @"
    (forall x. P(x,x,1)) /\
    (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
    ==> forall a b c. P(a,b,c) ==> P(b,a,c)"))

// pg. 313
// ------------------------------------------------------------------------- //
// A bigger example.                                                         //
// ------------------------------------------------------------------------- //

// decidable.p010
runWithEnlargedStack (fun () -> 
    aedecide (parse @"
    (exists x. P(x)) /\ (exists x. G(x))
    ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))"))

// pg. 313
// ------------------------------------------------------------------------- //
// The following, however, doesn't work with aedecide.                       //
// ------------------------------------------------------------------------- //

// This is p18

// decidable.p011
// System.Exception: Not decidable
// Pelletier #18
aedecide (parse @"exists y. forall x. P(y) ==> P(x)")

// decidable.p012
// Pelletier #18
davisputnam (parse @"exists y. forall x. P(y) ==> P(x)")

// pg. 315
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// decidable.p013
// Pelletier #18
miniscope(nnf (parse @"exists y. forall x. P(y) ==> P(x)"))

// decidable.p014
// Pelletier #20
let fm002 =
    miniscope(nnf (parse @"(
    forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"))

// decidable.p015
pnf (nnf fm002)

// pg. 316
// ------------------------------------------------------------------------- //
// It works well on simple monadic formulas.                                 //
// ------------------------------------------------------------------------- //

// decidable.p016
// Pelletier #20
wang
    (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")
   
// pg. 316
// ------------------------------------------------------------------------- //
// But not on this one!                                                      //
// ------------------------------------------------------------------------- //

// decidable.p017
// Note: This works, but the output is huge.
// Pelletier #34
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

// decidable.p018
let all_valid_syllogisms = List.filter aedecide all_possible_syllogisms

// decidable.p019
List.length all_valid_syllogisms

// decidable.p020
List.map anglicize_syllogism all_valid_syllogisms

// pg. 320
// ------------------------------------------------------------------------- //
// We can "fix" the traditional list by assuming nonemptiness.               //
// ------------------------------------------------------------------------- //

// decidable.p021
// Note: This works, but the output is huge.
let all_valid_syllogisms' = List.filter aedecide all_possible_syllogisms'

// decidable.p022
List.length all_valid_syllogisms'

// decidable.p023
List.map (anglicize_syllogism << consequent) all_valid_syllogisms'

// pg. 323
// ------------------------------------------------------------------------- //
// Decision procedure in principle for formulas with finite model property.  //
// ------------------------------------------------------------------------- //

// decidable.p024
decide_fmp
    (parse @"
    (forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)")

// decidable.p025
decide_fmp
    (parse @"
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)")

// decidable.p026
//** This fails to terminate: has countermodels, but only infinite ones
// Process is terminated due to StackOverflowException, even with 16MB stack
runWithEnlargedStack (fun () -> 
    decide_fmp (parse @"
    ~((forall x. ~R(x,x)) /\ 
    (forall x. exists z. R(x,z)) /\ 
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))"))

// pg. 325
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// decidable.p027
// Pelletier #34
decide_monadic
    (parse @"
    ((exists x. forall y. P(x) <=> P(y)) <=>
        ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))")

// decidable.p028
// This is not feasible
// Process is terminated due to StackOverflowException.
// Pelletier #20
//decide_monadic
//    (parse @"
//    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
//    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")

// pg. 326
// ------------------------------------------------------------------------- //
// Little auxiliary results for failure of finite model property.            //
// ------------------------------------------------------------------------- //

//** Our claimed equivalences are indeed correct **//

// decidable.p029
meson002 (parse @"
    (exists x y z. forall u.
        R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=>
    ~((forall x. ~R(x,x)) /\
        (forall x. exists z. R(x,z)) /\
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))")

// decidable.p030
meson002 
    (parse @"
    (exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=>
    ~((forall x. ~R(x,x)) /\
        (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))")

//** The second formula implies the first **//

// decidable.p031
meson002 (parse @"
    ~((forall x. ~R(x,x)) /\
        (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))
    ==> ~((forall x. ~R(x,x)) /\
        (forall x. exists z. R(x,z)) /\
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))")
