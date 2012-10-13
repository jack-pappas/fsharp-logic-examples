// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal

fsi.AddPrinter sprint_fol_formula

//
// pg. 239
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

function_congruence ("f", 3);;

function_congruence ("+", 2);;

// pg. 241
// ------------------------------------------------------------------------- //
// A simple example (see EWD1266a and the application to Morley's theorem).  //
// ------------------------------------------------------------------------- //

let ewd = 
    equalitize (parse @"
    (forall x. f(x) ==> g(x)) /\ 
    (exists x. f(x)) /\ 
    (forall x y. g(x) /\ g(y) ==> x = y) 
    ==> forall y. g(y) ==> f(y)");;

meson002 ewd;;

// pg. 241
// ------------------------------------------------------------------------- //
// Wishnu Prasetya's example (even nicer with an "exists unique" primitive). //
// ------------------------------------------------------------------------- //

let wishnu =
    equalitize (parse @"
        (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
        (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;

// Real: 00:00:22.030, CPU: 00:00:21.968, GC gen0: 253, gen1: 252, gen2: 1
time meson002 wishnu;;

// pg. 248
// ------------------------------------------------------------------------- //
// More challenging equational problems. (Size 18, 61814 seconds.)           //
// ------------------------------------------------------------------------- //

// long running
//(meson002 << equalitize) 
//    (parse @"
//    (forall x y z. x * (y * z) = (x * y) * z) /\ 
//    (forall x. 1 * x = x) /\ 
//    (forall x. i(x) * x = 1) 
//    ==> forall x. x * i(x) = 1");;

// ------------------------------------------------------------------------- //
// Other variants not mentioned in book.                                     //
// ------------------------------------------------------------------------- //

// long running
//(meson002 << equalitize)
//    (parse @"
//    (forall x y z. x * (y * z) = (x * y) * z) /\ 
//    (forall x. 1 * x = x) /\ 
//    (forall x. x * 1 = x) /\ 
//    (forall x. x * x = 1) 
//    ==> forall x y. x * y  = y * x");;

// ------------------------------------------------------------------------- //
// With symmetry at leaves and one-sided congruences (Size = 16, 54659 s).   //
// ------------------------------------------------------------------------- //

// long running
//let fm001 =
//    (parse @"
//    (forall x. x = x) /\ 
//    (forall x y z. x * (y * z) = (x * y) * z) /\ 
//    (forall x y z. =((x * y) * z,x * (y * z))) /\ 
//    (forall x. 1 * x = x) /\ 
//    (forall x. x = 1 * x) /\ 
//    (forall x. i(x) * x = 1) /\ 
//    (forall x. 1 = i(x) * x) /\ 
//    (forall x y. x = y ==> i(x) = i(y)) /\ 
//    (forall x y z. x = y ==> x * z = y * z) /\ 
//    (forall x y z. x = y ==> z * x = z * y) /\ 
//    (forall x y z. x = y /\ y = z ==> x = z) 
//    ==> forall x. x * i(x) = 1");;
//
//time meson002 fm001;;

// ------------------------------------------------------------------------- //
// Newer version of stratified equalities.                                   //
// ------------------------------------------------------------------------- //

// long running
//let fm002 =
//    (parse @"
//    (forall x y z. axiom(x * (y * z),(x * y) * z)) /\ 
//    (forall x y z. axiom((x * y) * z,x * (y * z)) /\ 
//    (forall x. axiom(1 * x,x)) /\ 
//    (forall x. axiom(x,1 * x)) /\ 
//    (forall x. axiom(i(x) * x,1)) /\ 
//    (forall x. axiom(1,i(x) * x)) /\ 
//    (forall x x'. x = x' ==> cchain(i(x),i(x'))) /\ 
//    (forall x x' y y'. x = x' /\ y = y' ==> cchain(x * y,x' * y'))) /\ 
//    (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
//    (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
//    (forall x x' u. x = x' /\ achain(i(x'),u) ==> cchain(i(x),u)) /\ 
//    (forall x x' y y' u. 
//        x = x' /\ y = y' /\ achain(x' * y',u) ==> cchain(x * y,u)) /\ 
//    (forall s t. cchain(s,t) ==> s = t) /\ 
//    (forall s t. achain(s,t) ==> s = t) /\ 
//    (forall t. t = t) 
//    ==> forall x. x * i(x) = 1");;
//
//time meson002 fm002;;

// long running
//let fm003 =
//    (parse @"
//    (forall x y z. axiom(x * (y * z),(x * y) * z)) /\ 
//    (forall x y z. axiom((x * y) * z,x * (y * z)) /\ 
//    (forall x. axiom(1 * x,x)) /\ 
//    (forall x. axiom(x,1 * x)) /\ 
//    (forall x. axiom(i(x) * x,1)) /\ 
//    (forall x. axiom(1,i(x) * x)) /\ 
//    (forall x x'. x = x' ==> cong(i(x),i(x'))) /\ 
//    (forall x x' y y'. x = x' /\ y = y' ==> cong(x * y,x' * y'))) /\ 
//    (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
//    (forall s t. cong(s,t) ==> cchain(s,t)) /\ 
//    (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
//    (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\ 
//    (forall s t. cchain(s,t) ==> s = t) /\ 
//    (forall s t. achain(s,t) ==> s = t) /\ 
//    (forall t. t = t) 
//    ==> forall x. x * i(x) = 1");;
//
//time meson002 fm003;;

// ------------------------------------------------------------------------- //
// Showing congruence closure.                                               //
// ------------------------------------------------------------------------- //

let fm004 =
    equalitize (parse @"
    forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c");;

time meson002 fm004;;

let fm005 =
    (parse @"
    axiom(f(f(f(f(f(c))))),c) /\ 
    axiom(c,f(f(f(f(f(c)))))) /\ 
    axiom(f(f(f(c))),c) /\ 
    axiom(c,f(f(f(c)))) /\ 
    (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
    (forall s t. cong(s,t) ==> cchain(s,t)) /\ 
    (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
    (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\ 
    (forall s t. cchain(s,t) ==> s = t) /\ 
    (forall s t. achain(s,t) ==> s = t) /\ 
    (forall t. t = t) /\ 
    (forall x y. x = y ==> cong(f(x),f(y))) 
    ==> f(c) = c");;

time meson002 fm005;;

// ------------------------------------------------------------------------- //
// With stratified equalities.                                               //
// ------------------------------------------------------------------------- //

// long running
//let fm006 =
//    (parse @"
//    (forall x y z. eqA (x * (y * z),(x * y) * z)) /\ 
//    (forall x y z. eqA ((x * y) * z)) /\ 
//    (forall x. eqA (1 * x,x)) /\ 
//    (forall x. eqA (x,1 * x)) /\ 
//    (forall x. eqA (i(x) * x,1)) /\ 
//    (forall x. eqA (1,i(x) * x)) /\ 
//    (forall x. eqA (x,x)) /\ 
//    (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\ 
//    (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\ 
//    (forall x y. eqT (x,y) ==> eqC (i(x),i(y))) /\ 
//    (forall w x y z. eqA (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqA (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqA (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqC (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqC (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqC (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqT (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqT (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall w x y z. eqT (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\ 
//    (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z)) 
//    ==> forall x. eqT (x * i(x),1)");;
//
//time meson002 fm006;;

// ------------------------------------------------------------------------- //
// With transitivity chains...                                               //
// ------------------------------------------------------------------------- //

// long running
//let fm007 =
//    (parse @"
//    (forall x y z. eqA (x * (y * z),(x * y) * z)) /\ 
//    (forall x y z. eqA ((x * y) * z)) /\ 
//    (forall x. eqA (1 * x,x)) /\ 
//    (forall x. eqA (x,1 * x)) /\ 
//    (forall x. eqA (i(x) * x,1)) /\ 
//    (forall x. eqA (1,i(x) * x)) /\ 
//    (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\ 
//    (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\ 
//    (forall w x y. eqA (w,x) ==> eqC (w * y,x * y)) /\ 
//    (forall w x y. eqC (w,x) ==> eqC (w * y,x * y)) /\ 
//    (forall x y z. eqA (y,z) ==> eqC (x * y,x * z)) /\ 
//    (forall x y z. eqC (y,z) ==> eqC (x * y,x * z)) /\ 
//    (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqC (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\ 
//    (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z)) 
//    ==> forall x. eqT (x * i(x),1) \/ eqC (x * i(x),1)");;
//
//time meson002 fm007;;

// ------------------------------------------------------------------------- //
// Enforce canonicity (proof size = 20).                                     //
// ------------------------------------------------------------------------- //

// long running
//let fm008 =
// (parse @"
//    (forall x y z. eq1(x * (y * z),(x * y) * z)) /\ 
//    (forall x y z. eq1((x * y) * z,x * (y * z))) /\ 
//    (forall x. eq1(1 * x,x)) /\ 
//    (forall x. eq1(x,1 * x)) /\ 
//    (forall x. eq1(i(x) * x,1)) /\ 
//    (forall x. eq1(1,i(x) * x)) /\ 
//    (forall x y z. eq1(x,y) ==> eq1(x * z,y * z)) /\ 
//    (forall x y z. eq1(x,y) ==> eq1(z * x,z * y)) /\ 
//    (forall x y z. eq1(x,y) /\ eq2(y,z) ==> eq2(x,z)) /\ 
//    (forall x y. eq1(x,y) ==> eq2(x,y)) 
//    ==> forall x. eq2(x,i(x))");;
//
//time meson002 fm008;;
