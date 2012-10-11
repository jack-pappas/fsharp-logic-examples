// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.eqelim

fsi.AddPrinter sprint_fol_formula

// pg. 287
// ------------------------------------------------------------------------- //
// The x^2 = 1 implies Abelian problem.                                      //
// ------------------------------------------------------------------------- //

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

meson002 
    (parse @"
    (forall x. R(x,x)) /\ 
    (forall x y. R(x,y) ==>  R(y,x)) /\ 
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
    <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z)))");;
   
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

time bmeson 
    (parse @"
    (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
    (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;          
                                                       
time emeson 
    (parse @"
    (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
    (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;        
                                                     
time bmeson 
    (parse @"
    (forall x y z. x * (y * z) = (x * y) * z) /\ 
    (forall x. e * x = x) /\ 
    (forall x. i(x) * x = e)                                
    ==> forall x. x * i(x) = e");;

// ------------------------------------------------------------------------- //
// Older stuff not now in the text.                                          //
// ------------------------------------------------------------------------- //

let ewd = 
    parse @"
    (forall x. f(x) ==> g(x)) /\ 
    (exists x. f(x)) /\ 
    (forall x y. g(x) /\ g(y) ==> x = y) 
    ==> forall y. g(y) ==> f(y)";;

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

time bmeson ewd;;
time emeson ewd;;

time bmeson wishnu;;
time emeson wishnu;;

time bmeson group1;;
// long running
//time emeson group1;;

// long running
//time bmeson group2;;
// long running
//time emeson group2;;

// ------------------------------------------------------------------------- //
// Nice function composition exercise from "Conceptual Mathematics".         //
// ------------------------------------------------------------------------- //

let fm = 
    parse @"
    (forall x y z. x * (y * z) = (x * y) * z) /\ p * q * p = p 
    ==> exists q'. p * q' * p = p /\ q' * p * q' = q'";;

// long running
//time bmeson fm;;        //* Seems to take a bit longer than below version  *//

// long running
//time emeson fm;;        //* Works in 64275 seconds(!), depth 30, on laptop *//

//*** Some other predicate formulations no longer in the main text

meson002 (parse @"
    (forall x. P(1,x,x)) /\ 
    (forall x. P(i(x),x,1)) /\ 
    (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
    ==> forall x. P(x,1,x)");;

meson002 (parse @"
    (forall x. P(1,x,x)) /\ 
    (forall x. P(i(x),x,1)) /\ 
    (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
    ==> forall x. P(x,i(x),1)");;

// ------------------------------------------------------------------------- //
// See how efficiency drops when we assert completeness.                     //
// ------------------------------------------------------------------------- //

meson002 (parse @"
    (forall x. P(1,x,x)) /\ 
    (forall x. P(x,x,1)) /\ 
    (forall x y. exists z. P(x,y,z)) /\ 
    (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v))) 
    ==> forall a b c. P(a,b,c) ==> P(b,a,c)");;

//** More reductions, not now explicitly in the text.

meson002 (parse @"
    (forall x. R(x,x)) /\ 
    (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) 
    <=> (forall x y. R(x,y) <=> (forall z. R(y,z) ==> R(x,z)))");;

meson002 (parse @"
    (forall x y. R(x,y) ==>  R(y,x)) <=> 
    (forall x y. R(x,y) <=> R(x,y) /\ R(y,x))");;

// ------------------------------------------------------------------------- //
// Show how Equiv' reduces to triviality.                                    //
// ------------------------------------------------------------------------- //

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

meson002 (parse @"
    (forall x y. R(x,y) <=> (forall z. R'(x,z) <=> R'(y,z))) /\ 
    (forall x. R'(x,x)) 
    ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;

meson002 (parse @"
    (forall x y. R(x,y) <=> (forall z. R'(y,z) ==> R'(x,z))) /\ 
    (forall x. R'(x,x)) 
    ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;

meson002 (parse @"
    (forall x y. R(x,y) <=> R'(x,y) /\ R'(y,x)) 
    ==> forall x y. ~R'(x,y) ==> ~R(x,y)");;