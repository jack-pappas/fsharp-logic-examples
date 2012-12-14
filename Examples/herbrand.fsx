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

fsi.AddPrinter sprint_fol_formula

// pg. 161
// ------------------------------------------------------------------------- //
// First example and a little tracing.                                       //
// ------------------------------------------------------------------------- //

// herbrand.p001
// Harrison #07
gilmore (parse @"exists x. forall y. P(x) ==> P(y)");;

// herbrand.p002
// Harrison #07
let sfm = skolemize(Not (parse @"exists x. forall y. P(x) ==> P(y)"));;

// pg. 161
// ------------------------------------------------------------------------- //
// Quick example.                                                            //
// ------------------------------------------------------------------------- //

// herbrand.p003
// Pelletier #24
let p24 = gilmore (parse @"
    ~(exists x. U(x) /\ Q(x)) 
    /\ (forall x. P(x) ==> Q(x) \/ R(x)) 
    /\ ~(exists x. P(x) ==> (exists x. Q(x))) 
    /\ (forall x. Q(x) 
    /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))");;

// pg. 162
// ------------------------------------------------------------------------- //
// Slightly less easy example.                                               //
// ------------------------------------------------------------------------- //

// herbrand.p004
// Pelletier #45
// Real: 00:00:27.907, CPU: 00:00:27.906, GC gen0: 7, gen1: 6, gen2: 1
let p45 = runWithEnlargedStack (fun () -> 
    gilmore (parse @"
        (forall x. P(x) 
        /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) 
        /\ ~(exists y. L(y) /\ R(y)) 
        /\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) 
        /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))"));;

// pg. 162
// ------------------------------------------------------------------------- //
// Apparently intractable example.                                           //
// ------------------------------------------------------------------------- //

// herbrand.p005
// Pelletier #20
//let p20 = gilmore (parse @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
//                           ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// pg. 163
// ------------------------------------------------------------------------- //
// Show how much better than the Gilmore procedure this can be.              //
// ------------------------------------------------------------------------- //

// herbrand.p006
// Pelletier #20
let p20dp = davisputnam (parse @"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// herbrand.p007
// Pelletier #36
let p36 = davisputnam' (parse @"
    (forall x. exists y. P(x,y)) 
    /\ (forall x. exists y. G(x,y)) 
    /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
    ==> (forall x. exists y. H(x,y))");;

// herbrand.p008

// Real: 00:01:50.847, CPU: 00:01:50.687, GC gen0: 382, gen1: 111, gen2: 1
// Pelletier #29
let p29 = davisputnam' (parse @"
    (exists x. P(x)) /\ (exists x. G(x)) ==>
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;
