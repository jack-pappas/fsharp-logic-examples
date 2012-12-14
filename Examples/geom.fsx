// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.initialization
open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.cooper
open FSharpx.Books.AutomatedReasoning.complex
open FSharpx.Books.AutomatedReasoning.real
open FSharpx.Books.AutomatedReasoning.grobner
open FSharpx.Books.AutomatedReasoning.geom

fsi.AddPrinter sprint_fol_formula

// pg. 415
//  ------------------------------------------------------------------------- // 
//  Trivial example.                                                          // 
//  ------------------------------------------------------------------------- // 

// geom.p001
coordinate (parse @"collinear(a,b,c) ==> collinear(b,a,c)");;

// geom.p002        
List.forall (grobner_decide << invariant_under_translation) coordinations;;

// geom.p003
List.forall (grobner_decide << invariant_under_rotation) coordinations;;
    
// pg. 416
//  ------------------------------------------------------------------------- // 
//  And show we can always invent such a transformation to zero a y:          // 
//  ------------------------------------------------------------------------- // 

// geom.p004
// Real: 00:00:23.087, CPU: 00:00:23.046, GC gen0: 653, gen1: 148, gen2: 1
runWithEnlargedStack (fun () -> real_qelim (parse @"
    forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0"));;

// geom.p005
List.forall (grobner_decide << invariant_under_scaling) coordinations;;

// geom.p006
List.partition (grobner_decide << invariant_under_shearing) coordinations;;
    
// pg. 418
//  ------------------------------------------------------------------------- // 
//  One from "Algorithms for Computer Algebra"                                // 
//  ------------------------------------------------------------------------- // 

// geom.p007
(grobner_decide << originate) (parse 
    @"is_midpoint(m,a,c) /\ perpendicular(a,c,m,b) 
    ==> lengths_eq(a,b,b,c)");;
       
// pg. 418
//  ------------------------------------------------------------------------- // 
//  Parallelogram theorem (Chou's expository example at the start).           // 
//  ------------------------------------------------------------------------- // 

// geom.p008
(grobner_decide << originate) (parse
    @"parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
    is_intersection(e,a,c,b,d)
    ==> lengths_eq(a,e,e,c)");;

// geom.p009
(grobner_decide << originate) (parse
    @"parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
    is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
    ==> lengths_eq(a,e,e,c)");;
        
// pg. 421
//  ------------------------------------------------------------------------- // 
//  Simson's theorem.                                                         // 
//  ------------------------------------------------------------------------- // 

let simson = 
    (parse 
        @"lengths_eq(o,a,o,b) /\ 
        lengths_eq(o,a,o,c) /\ 
        lengths_eq(o,a,o,d) /\ 
        collinear(e,b,c) /\ 
        collinear(f,a,c) /\ 
        collinear(g,a,b) /\ 
        perpendicular(b,c,d,e) /\ 
        perpendicular(a,c,d,f) /\ 
        perpendicular(a,b,d,g) 
        ==> collinear(e,f,g)");;

let vars001 = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";  "b_y"; "b_x"; "o_x"];;

let zeros001 = ["a_x"; "a_y"; "o_y"];;

// geom.p010
wu simson vars001 zeros001;;
    
// pg. 423
//  ------------------------------------------------------------------------- // 
//  Try without special coordinates.                                          // 
//  ------------------------------------------------------------------------- // 

// geom.p011
wu simson (vars001 @ zeros001) [];;
    
let pappus = 
    (parse
        @"collinear(a1,b2,d) /\
        collinear(a2,b1,d) /\
        collinear(a2,b3,e) /\
        collinear(a3,b2,e) /\
        collinear(a1,b3,f) /\
        collinear(a3,b1,f) 
        ==> collinear(d,e,f)");;

let vars002 = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"];;

let zeros002 = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"];;

// geom.p012
wu pappus vars002 zeros002;;

//  ------------------------------------------------------------------------- // 
//  The Butterfly (figure 9).                                                 // 
//  ------------------------------------------------------------------------- // 

let butterfly = 
    (parse 
        @"lengths_eq(b,o,a,o) /\ lengths_eq(c,o,a,o) /\ lengths_eq(d,o,a,o) /\ 
        collinear(a,e,c) /\ collinear(d,e,b) /\ 
        perpendicular(e,f,o,e) /\ 
        collinear(a,f,d) /\ collinear(f,e,g) /\ collinear(b,c,g) 
        ==> is_midpoint(e,f,g)");;

let vars003 = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "c_y"; "b_y"; "d_x"; "c_x"; "b_x"; "a_x"]

let zeros003 = ["a_y"; "o_x"; "o_y"];;

// This one is costly (too big for laptop, but doable in about 300M)
// However, it gives exactly the same degenerate conditions as Chou

// geom.p013
// Real: 00:03:50.788, CPU: 00:03:50.046, GC gen0: 5552, gen1: 3167, gen2: 66
wu butterfly vars003 zeros003;;

// ** Other examples removed from text

//  ------------------------------------------------------------------------- // 
//  Centroid (Chou, example 142).                                             // 
//  ------------------------------------------------------------------------- // 

// geom.p014
(grobner_decide << originate) 
    (parse 
        @"is_midpoint(d,b,c) /\ is_midpoint(e,a,c) /\
        is_midpoint(f,a,b) /\ is_intersection(m,b,e,a,d) 
        ==> collinear(c,f,m)");;
