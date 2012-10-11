// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Compatibility.OCaml

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
open Reasoning.Automated.Harrison.Handbook.folderived
open Reasoning.Automated.Harrison.Handbook.tactics
open Reasoning.Automated.Harrison.Handbook.limitations

fsi.AddPrinter sprint_thm

// pg. 534
// ------------------------------------------------------------------------- //
// One explicit example.                                                     //
// ------------------------------------------------------------------------- //

gform (parse @"~(x = 0)");;

// pg. 534
// ------------------------------------------------------------------------- //
// Some more examples of things in or not in the set of true formulas.       //
// ------------------------------------------------------------------------- //

gform (parse @"x = x");;
gform (parse @"0 < 0");;

// pg. 538
diag001("p(x)");;
diag001("This string is diag(x)");;
    
// pg. 538
// ------------------------------------------------------------------------- //
// Analogous construct in natural language.                                  //
// ------------------------------------------------------------------------- //

diag001("The result of substituting the quotation of x for `x' in x \ has property P");;
            
// pg. 549
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

let prime_form p = subst("p" |=> numeral p) (parse @"S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)");;

dholds undefined (prime_form (Num.Int 100));;
dholds undefined (prime_form (Num.Int 101));;
            
// pg. 551
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

classify Sigma 1 (parse @"forall x. x < 2 ==> exists y z. forall w. w < x + 2 ==> w + x + y + z = 42");;

// pg. 552
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

sigma_bound (parse @"exists p x. p < x /\ (S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)) /\ ~(x = 0) /\ forall z. z <= x ==> (exists w. w <= x /\ x = z * w) ==> z = S(0) \/ exists x. x <= z /\ z = p * x");;
            
// pg. 561
// ------------------------------------------------------------------------- //
// Example program (successor).                                              //
// ------------------------------------------------------------------------- //

let prog_suc = List.foldBack (fun m -> m) [(1,Blank) |-> (Blank,Right,2);  (2,One) |-> (One,Right,2);  (2,Blank) |-> (One,Right,3); (3,Blank) |-> (Blank,Left,4); (3,One) |-> (Blank,Left,4); (4,One) |-> (One,Left,4); (4,Blank) |-> (Blank,Stay,0)]  undefined;;

exec prog_suc [0];;

exec prog_suc [1];;

exec prog_suc [19];;

// pg. 566
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

robeval (parset @"S(0) + (S(S(0)) * ((S(0) + S(S(0)) + S(0))))");;
        
// pg. 570
rob_ne (parset @"S(0) + S(0) + S(0)") (parset @"S(S(0)) * S(S(0))");;
rob_ne (parset @"0 + 0 * S(0)") (parset @"S(S(0)) + 0");;
rob_ne (parset @"S(S(0)) + 0") (parset @"0 + 0 + 0 * 0");;

// pg. 573
// ------------------------------------------------------------------------- //
// Example in the text.                                                      //
// ------------------------------------------------------------------------- //

sigma_prove (parse @"exists p. S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)") ;;
    
// pg. 576
// ------------------------------------------------------------------------- //
// The essence of Goedel's first theorem.                                    //
// ------------------------------------------------------------------------- //

meson002 (parse @"(True(G) <=> ~(|--(G))) /\ Pi(G) /\ (forall p. Sigma(p) ==> (|--(p) <=> True(p))) /\ (forall p. True(Not(p)) <=> ~True(p)) /\  (forall p. Pi(p) ==> Sigma(Not(p))) ==> (|--(Not(G)) <=> |--(G))");;
    
// pg. 577
// ------------------------------------------------------------------------- //
// Godel's second theorem.                                                   //
// ------------------------------------------------------------------------- //

let godel_2 = 
    prove (parse @"(forall p. |--(p) ==> |--(Pr(p))) /\ (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\ (forall p. |--(imp(Pr(p),Pr(Pr(p))))) ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\ (forall p q. |--(imp(q,imp(p,q)))) /\ (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r))))) ==> |--(imp(G,imp(Pr(G),F))) /\ |--(imp(imp(Pr(G),F),G)) ==> |--(imp(Pr(F),F)) ==> |--(F)") 
        [assume
            ["lob1",(parse @"forall p. |--(p) ==> |--(Pr(p))"); 
             "lob2",(parse @"forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))");
             "lob3",(parse @"forall p. |--(imp(Pr(p),Pr(Pr(p))))")]; 
         assume ["logic",(parse @"(forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\ (forall p q. |--(imp(q,imp(p,q)))) /\  (forall p q r. |--(imp(imp(p,imp(q,r)), imp(imp(p,q),imp(p,r)))))")];
         assume ["fix1",(parse @"|--(imp(G,imp(Pr(G),F)))"); 
                 "fix2",(parse @"|--(imp(imp(Pr(G),F),G))")]; 
         assume ["consistency",(parse @"|--(imp(Pr(F),F))")]; 
         have (parse @"|--(Pr(imp(G,imp(Pr(G),F))))") by ["lob1"; "fix1"];
         so have (parse @"|--(imp(Pr(G),Pr(imp(Pr(G),F))))") by ["lob2"; "logic"];
         so have (parse @"|--(imp(Pr(G),imp(Pr(Pr(G)),Pr(F))))") by ["lob2"; "logic"];
         so have (parse @"|--(imp(Pr(G),Pr(F)))") by ["lob3"; "logic"]; 
         so note ("L", (parse @"|--(imp(Pr(G),F))") ) by ["consistency"; "logic"]; 
         so have (parse @"|--(G)") by ["fix2"; "logic"]; 
         so have (parse @"|--(Pr(G))") by ["lob1"; "logic"]; 
         so conclude (parse @"|--(F)") by ["L"; "logic"]; 
         qed];;


