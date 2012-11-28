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
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.eqelim

fsi.AddPrinter sprint_fol_formula

// pg. 287
// ------------------------------------------------------------------------- //
// The x^2 = 1 implies Abelian problem.                                      //
// ------------------------------------------------------------------------- //

// eqelim.p001
meson002 
    (parse @"
    (forall x. P(1,x,x)) /\ 
    (forall x. P(x,x,1)) /\ 
    (forall u v w x y z. P(x,y,u) /\  P(y,z,w) 
        ==> (P(x,w,v) <=> P(u,z,v)))
    ==> forall a b c. P(a,b,c) ==> P(b,a,c)");;

// pg. 288
// ------------------------------------------------------------------------- //
// Lemma for equivalence elimination.                                        //
// ------------------------------------------------------------------------- //

// eqelim.p002
meson002 
    (parse @"
    (forall x. R(x,x)) /\ 
    (forall x y. R(x,y) ==>  R(y,x)) /\ 
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
    <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z)))");;
   
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// eqelim.p003
// Wishnu #1
// Real: 00:02:25.021, CPU: 00:02:24.406, GC gen0: 2891, gen1: 1055, gen2: 2
time bmeson 
    (parse @"
    (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
    (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;          

// eqelim.p004
// Wishnu #1
// Real: 00:00:20.737, CPU: 00:00:20.625, GC gen0: 251, gen1: 2, gen2: 0                                                       
time emeson 
    (parse @"
    (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
    (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;        

// eqelim.p005
// Real: 00:18:19.207, CPU: 00:18:16.640, GC gen0: 19293, gen1: 110, gen2: 11                                                     
time bmeson 
    (parse @"
    (forall x y z. x * (y * z) = (x * y) * z) /\ 
    (forall x. e * x = x) /\ 
    (forall x. i(x) * x = e)                                
    ==> forall x. x * i(x) = e");;

// ------------------------------------------------------------------------- //
// Older stuff not now in the text.                                          //
// ------------------------------------------------------------------------- //

// Dijkstra 1266a
let ewd = 
    parse @"
    (forall x. f(x) ==> g(x)) /\ 
    (exists x. f(x)) /\ 
    (forall x y. g(x) /\ g(y) ==> x = y) 
    ==> forall y. g(y) ==> f(y)";;

// Wishnu #1
let wishnu = 
    (parse @"
    (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=> 
    (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;

let group1 =
    (parse @"
    (forall x y z. x * (y * z) = (x * y) * z) /\ 
    (forall x. e * x = x) /\ 
    (forall x. i(x) * x = e) 
    ==> forall x. x * e = x");;

let group2 =
    (parse @"
    (forall x y z. x * (y * z) = (x * y) * z) /\ 
    (forall x. e * x = x) /\ 
    (forall x. i(x) * x = e) 
    ==> forall x. x * i(x) = e");;

// eqelim.p006
time bmeson ewd;;

// eqelim.p007
time emeson ewd;;

// eqelim.p008
// Real: 00:02:36.719, CPU: 00:02:36.406, GC gen0: 2891, gen1: 17, gen2: 1
time bmeson wishnu;;

// eqelim.p009
// Real: 00:00:21.639, CPU: 00:00:21.625, GC gen0: 253, gen1: 4, gen2: 1
time emeson wishnu;;

// eqelim.p010
// Real: 00:06:01.715, CPU: 00:06:01.156, GC gen0: 6088, gen1: 37, gen2: 3
time bmeson group1;;

// eqelim.p011
// long running
time emeson group1;;

// eqelim.p012
// long running
time bmeson group2;;

// eqelim.p013
// long running
time emeson group2;;

// ------------------------------------------------------------------------- //
// Nice function composition exercise from "Conceptual Mathematics".         //
// ------------------------------------------------------------------------- //

let fm = 
    parse @"
    (forall x y z. x * (y * z) = (x * y) * z) /\ p * q * p = p 
    ==> exists q'. p * q' * p = p /\ q' * p * q' = q'";;

// eqelim.p014
// long running
time bmeson fm;;        //* Seems to take a bit longer than below version  *//

// eqelim.p015
// long running
time emeson fm;;        //* Works in 64275 seconds(!), depth 30, on laptop *//

//*** Some other predicate formulations no longer in the main text

// eqelim.p016
meson002 (parse @"
    (forall x. P(1,x,x)) /\ 
    (forall x. P(i(x),x,1)) /\ 
    (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
    ==> forall x. P(x,1,x)");;

// eqelim.p017
meson002 (parse @"
    (forall x. P(1,x,x)) /\ 
    (forall x. P(i(x),x,1)) /\ 
    (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
    ==> forall x. P(x,i(x),1)");;

// ------------------------------------------------------------------------- //
// See how efficiency drops when we assert completeness.                     //
// ------------------------------------------------------------------------- //

// eqelim.p018
// Real: 00:00:38.932, CPU: 00:00:38.890, GC gen0: 569, gen1: 4, gen2: 0
meson002 (parse @"
    (forall x. P(1,x,x)) /\ 
    (forall x. P(x,x,1)) /\ 
    (forall x y. exists z. P(x,y,z)) /\ 
    (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
    ==> forall a b c. P(a,b,c) ==> P(b,a,c)");;

//** More reductions, not now explicitly in the text.

// eqelim.p019
meson002 (parse @"
    (forall x. R(x,x)) /\ 
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) 
    <=> (forall x y. R(x,y) <=> (forall z. R(y,z) ==> R(x,z)))");;

// eqelim.p020
meson002 (parse @"
    (forall x y. R(x,y) ==>  R(y,x)) <=> 
    (forall x y. R(x,y) <=> R(x,y) /\ R(y,x))");;

// ------------------------------------------------------------------------- //
// Show how Equiv' reduces to triviality.                                    //
// ------------------------------------------------------------------------- //

// eqelim.p021
meson002 (parse @"
    (forall x. (forall w. R'(x,w) <=> R'(x,w))) /\ 
    (forall x y. (forall w. R'(x,w) <=> R'(y,w)) 
        ==> (forall w. R'(y,w) <=> R'(x,w))) /\ 
    (forall x y z. (forall w. R'(x,w) <=> R'(y,w)) /\ 
        (forall w. R'(y,w) <=> R'(z,w)) 
            ==> (forall w. R'(x,w) <=> R'(z,w)))");;

// ------------------------------------------------------------------------- //
// More auxiliary proofs for Brand's S and T modification.                   //
// ------------------------------------------------------------------------- //

// eqelim.p022
meson002 (parse @"
    (forall x y. R(x,y) <=> (forall z. R'(x,z) <=> R'(y,z))) /\ 
    (forall x. R'(x,x)) 
    ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;

// eqelim.p023
meson002 (parse @"
    (forall x y. R(x,y) <=> (forall z. R'(y,z) ==> R'(x,z))) /\ 
    (forall x. R'(x,x)) 
    ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;

// eqelim.p024
meson002 (parse @"
    (forall x y. R(x,y) <=> R'(x,y) /\ R'(y,x)) 
    ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;
