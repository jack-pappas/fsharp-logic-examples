// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.limitations

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
open Reasoning.Automated.Harrison.Handbook.folderived
open Reasoning.Automated.Harrison.Handbook.tactics
open Reasoning.Automated.Harrison.Handbook.limitations
open FSharpx.Compatibility.OCaml
open NUnit.Framework
open FsUnit

// pg. 534
// ------------------------------------------------------------------------- //
// One explicit example.                                                     //
// ------------------------------------------------------------------------- //
[<Test>]
let ``test gform 1``() = 
    gform (parse "~(x = 0)")
    |> should equal (Num.Big_int 2116574771128325487937994357299494I)

// pg. 534
// ------------------------------------------------------------------------- //
// Some more examples of things in or not in the set of true formulas.       //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test gform 2``() = 
    gform (parse "x = x")
    |> should equal (Num.Big_int 735421674029290002I)

[<Test>]
let ``test gform 3``() = 
    gform (parse "0 < 0")
    |> should equal (Num.Big_int 1767I)

// pg. 538
[<Test>]
let ``test diag001 1``() = 
    diag001("p(x)")
    |> should equal "p(`p(x)')"

[<Test>]
let ``test diag001 2``() = 
    diag001("This string is diag(x)")
    |> should equal "This string is diag(`This string is diag(x)')"
    
// pg. 538
// ------------------------------------------------------------------------- //
// Analogous construct in natural language.                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test diag001 3``() = 
    diag001("The result of substituting the quotation of x for `x' in x \ has property P")
    |> should equal "The result of substituting the quotation of `The result of substituting the quotation of x for `x' in x \ has property P' for `x' in `The result of substituting the quotation of x for `x' in x \ has property P' \ has property P"

// pg. 549
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

let prime_form p = subst("p" |=> numeral p) (parse "S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)")

[<Test>]
let ``test dholds 1``() = 
    dholds undefined (prime_form (Num.Int 100))
    |> should be False

[<Test>]
let ``test dholds 2``() = 
    dholds undefined (prime_form (Num.Int 101))
    |> should be True
            
// pg. 551
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test classify``() = 
    classify Sigma 1 (parse "forall x. x < 2 ==> exists y z. forall w. w < x + 2 ==> w + x + y + z = 42")
    |> should be True

// pg. 552
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test sigma_bound``() = 
    sigma_bound (parse "exists p x. p < x /\ (S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)) /\ ~(x = 0) /\ forall z. z <= x ==> (exists w. w <= x /\ x = z * w) ==> z = S(0) \/ exists x. x <= z /\ z = p * x")
    |> should equal (Num.Int 4)
            
// pg. 561
// ------------------------------------------------------------------------- //
// Example program (successor).                                              //
// ------------------------------------------------------------------------- //

let prog_suc = List.foldBack (fun m -> m) [(1,Blank) |-> (Blank,Right,2);  (2,One) |-> (One,Right,2);  (2,Blank) |-> (One,Right,3); (3,Blank) |-> (Blank,Left,4); (3,One) |-> (Blank,Left,4); (4,One) |-> (One,Left,4); (4,Blank) |-> (Blank,Stay,0)]  undefined

[<Test>]
let ``test prog_suc 1``() = 
    exec prog_suc [0]
    |> should equal 1

[<Test>]
let ``test prog_suc 2``() = 
    exec prog_suc [1]
    |> should equal 2

[<Test>]
let ``test prog_suc 3``() = 
    exec prog_suc [19]
    |> should equal 20

// pg. 566
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test robeval``() =
    robeval (parset "S(0) + (S(S(0)) * ((S(0) + S(S(0)) + S(0))))") 
    |> sprint_thm
    |> should equal "|- (forall m n. S(m) =S(n) ==> m =n) /\ (forall n. ~n =0 <=> (exists m. n =S(m))) /\ (forall n. 0 +n =n) /\ (forall m n. S(m) +n =S(m +n)) /\ (forall n. 0 *n =0) /\ (forall m n. S(m) *n =n +m *n) /\ (forall m n. m <=n <=> (exists d. m +d =n)) /\ (forall m n. m <n <=> S(m) <=n) ==> S(0) +S(S(0)) *(S(0) +S(S(0)) +S(0)) =S(S(S(S(S(S(S(S(S(0)))))))))"
        
// pg. 570
[<Test>]
let ``test rob_ne 1``() =
    rob_ne (parset "S(0) + S(0) + S(0)") (parset "S(S(0)) * S(S(0))") 
    |> sprint_thm
    |> should equal "|- (forall m n. S(m) =S(n) ==> m =n) /\ (forall n. ~n =0 <=> (exists m. n =S(m))) /\ (forall n. 0 +n =n) /\ (forall m n. S(m) +n =S(m +n)) /\ (forall n. 0 *n =0) /\ (forall m n. S(m) *n =n +m *n) /\ (forall m n. m <=n <=> (exists d. m +d =n)) /\ (forall m n. m <n <=> S(m) <=n) ==> S(0) +S(0) +S(0) =S(S(0)) *S(S(0)) ==> false"

[<Test>]
let ``test rob_ne 2``() =
    rob_ne (parset "0 + 0 * S(0)") (parset "S(S(0)) + 0") 
    |> sprint_thm
    |> should equal "|- (forall m n. S(m) =S(n) ==> m =n) /\ (forall n. ~n =0 <=> (exists m. n =S(m))) /\ (forall n. 0 +n =n) /\ (forall m n. S(m) +n =S(m +n)) /\ (forall n. 0 *n =0) /\ (forall m n. S(m) *n =n +m *n) /\ (forall m n. m <=n <=> (exists d. m +d =n)) /\ (forall m n. m <n <=> S(m) <=n) ==> 0 +0 *S(0) =S(S(0)) +0 ==> false"

[<Test>]
let ``test rob_ne 3``() =
    rob_ne (parset "S(S(0)) + 0") (parset "0 + 0 + 0 * 0") 
    |> sprint_thm
    |> should equal "|- (forall m n. S(m) =S(n) ==> m =n) /\ (forall n. ~n =0 <=> (exists m. n =S(m))) /\ (forall n. 0 +n =n) /\ (forall m n. S(m) +n =S(m +n)) /\ (forall n. 0 *n =0) /\ (forall m n. S(m) *n =n +m *n) /\ (forall m n. m <=n <=> (exists d. m +d =n)) /\ (forall m n. m <n <=> S(m) <=n) ==> S(S(0)) +0 =0 +0 +0 *0 ==> false"

// pg. 573
// ------------------------------------------------------------------------- //
// Example in the text.                                                      //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test sigma_prove``() =
    sigma_prove (parse "exists p. S(S(0)) <= p /\ forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)") 
    |> sprint_thm
    |> should equal "|- (forall m n. S(m) =S(n) ==> m =n) /\ (forall n. ~n =0 <=> (exists m. n =S(m))) /\ (forall n. 0 +n =n) /\ (forall m n. S(m) +n =S(m +n)) /\ (forall n. 0 *n =0) /\ (forall m n. S(m) *n =n +m *n) /\ (forall m n. m <=n <=> (exists d. m +d =n)) /\ (forall m n. m <n <=> S(m) <=n) ==> (exists p. S(S(0)) <=p /\ (forall n. n <p ==> (exists x. x <=p /\ p =n *x) ==> n =S(0)))"
    
// pg. 576
// ------------------------------------------------------------------------- //
// The essence of Goedel's first theorem.                                    //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test meson002``() =
    meson002 (parse "(True(G) <=> ~(|--(G))) /\ Pi(G) /\ (forall p. Sigma(p) ==> (|--(p) <=> True(p))) /\ (forall p. True(Not(p)) <=> ~True(p)) /\  (forall p. Pi(p) ==> Sigma(Not(p))) ==> (|--(Not(G)) <=> |--(G))")
    |> should equal [5; 5]
// pg. 577
// ------------------------------------------------------------------------- //
// Godel's second theorem.                                                   //
// ------------------------------------------------------------------------- //

[<Test>]
let ``test Godel theorem``() =
    prove (parse "(forall p. |--(p) ==> |--(Pr(p))) /\ (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\ (forall p. |--(imp(Pr(p),Pr(Pr(p))))) ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\ (forall p q. |--(imp(q,imp(p,q)))) /\ (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r))))) ==> |--(imp(G,imp(Pr(G),F))) /\ |--(imp(imp(Pr(G),F),G)) ==> |--(imp(Pr(F),F)) ==> |--(F)") 
        [assume
            ["lob1",(parse "forall p. |--(p) ==> |--(Pr(p))"); "lob2",(parse "forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))");
            "lob3",(parse "forall p. |--(imp(Pr(p),Pr(Pr(p))))")]; 
         assume ["logic",(parse "(forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\ (forall p q. |--(imp(q,imp(p,q)))) /\  (forall p q r. |--(imp(imp(p,imp(q,r)), imp(imp(p,q),imp(p,r)))))")];
         assume ["fix1",(parse "--(imp(G,imp(Pr(G),F)))"); "fix2",(parse "--(imp(imp(Pr(G),F),G))")]; 
         assume ["consistency",(parse "--(imp(Pr(F),F))")]; 
         have (parse "--(Pr(imp(G,imp(Pr(G),F))))") by ["lob1"; "fix1"];
         so have (parse "--(imp(Pr(G),Pr(imp(Pr(G),F))))") by ["lob2"; "logic"];
         so have (parse "--(imp(Pr(G),imp(Pr(Pr(G)),Pr(F))))") by ["lob2"; "logic"];
         so have (parse "--(imp(Pr(G),Pr(F)))") by ["lob3"; "logic"]; 
         so note ("L", (parse "--(imp(Pr(G),F))") ) by ["consistency"; "logic"]; 
         so have (parse "--(G)") by ["fix2"; "logic"]; 
         so have (parse "--(Pr(G))") by ["lob1"; "logic"]; 
         so conclude (parse "--(F)") by ["L"; "logic"]; 
         qed] 
     |> sprint_thm
     |> should equal "|-
(forall p. |--(p) ==> |--(Pr(p))) /\
(forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\
(forall p. |--(imp(Pr(p),Pr(Pr(p))))) ==>
(forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
(forall p q. |--(imp(q,imp(p,q)))) /\
(forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r))))) ==> |--(imp(G,imp(Pr(G),F))) /\ |--(imp(imp(Pr(G),F),G)) ==> |--(imp(Pr(F),F)) ==> |--(F)"
