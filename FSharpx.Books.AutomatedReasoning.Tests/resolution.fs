// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.resolution

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.unif
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.resolution

open NUnit.Framework
open FsUnit

// pg. 181
// ------------------------------------------------------------------------- //
// Barber's paradox is an example of why we need factoring.                  //
// ------------------------------------------------------------------------- //

// resolution.p001
// Barber's paradox
[<Test>]
let ``Barber's paradox``() = 
    simpcnf(skolemize(Not barb)) 
    |> should equal [[Atom (R ("shaves",[Var "x"; Var "x"])); Atom (R ("shaves",[Fn ("c_b",[]); Var "x"]))]; [Not (Atom (R ("shaves",[Var "x"; Var "x"]))); Not (Atom (R ("shaves",[Fn ("c_b",[]); Var "x"])))]] ;;

// pg. 185
// ------------------------------------------------------------------------- //
// Simple example that works well.                                           //
// ------------------------------------------------------------------------- //

// resolution.p002
// Davis Putnam #1
[<TestCase(@"
        exists x. exists y. forall z. 
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
    Result = [|true|], TestName = "Davis Putnam #1")>]

let ``1 Basic Resolution`` f =
    parse f
    |> resolution001
    |> List.toArray

// pg. 192
// ------------------------------------------------------------------------- //
// This is now a lot quicker.                                                //
// ------------------------------------------------------------------------- //

// resolution.p003
// Davis Putnam #1
[<TestCase(@"
        exists x. exists y. forall z. 
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
    Result = [|true|], TestName = "Davis Putnam #1")>]

let ``2 Resolution with subsumption and tautology deletion`` f =
    parse f
    |> resolution002
    |> List.toArray

// resolution.p004
// Los #1
[<TestCase(@"
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
    Result = [|true|], TestName = "Los #1")>]
    
// resolution.p005
// Pelletier #01
[<TestCase(@"
    p ==> q <=> ~q ==> ~p",
    Result = [||], TestName = "Pelletier #01")>]

// resolution.p006
// Pelletier #02
[<TestCase(@"
    ~ ~p <=> p",
    Result = [||], TestName = "Pelletier #02")>]

// resolution.p007
// Pelletier #03
[<TestCase(@"
    ~(p ==> q) ==> q ==> p",
    Result = [||], TestName = "Pelletier #03")>]

// resolution.p008
// Pelletier #04
[<TestCase(@"
    ~p ==> q <=> ~q ==> p",
    Result = [||], TestName = "Pelletier #04")>]

// resolution.p009
// Pelletier #05
[<TestCase(@"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)",
    Result = [||], TestName = "Pelletier #05")>]

// resolution.p010
// Pelletier #06
[<TestCase(@"
    p \/ ~p",
    Result = [||], TestName = "Pelletier #06")>]

// resolution.p011
// Pelletier #07
[<TestCase(@"
    p \/ ~ ~ ~p",
    Result = [||], TestName = "Pelletier #07")>]

// resolution.p012
// Pelletier #08
[<TestCase(@"
    ((p ==> q) ==> p) ==> p",
    Result = [||], TestName = "Pelletier #08")>]

// resolution.p013
// Pelletier #09
[<TestCase(@"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)",
    Result = [||], TestName = "Pelletier #09")>]

// resolution.p014
// Pelletier #10
[<TestCase(@"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)",
    Result = [||], TestName = "Pelletier #10")>]

// resolution.p015
// Pelletier #11
[<TestCase(@"
    p <=> p",
    Result = [||], TestName = "Pelletier #11")>]

// resolution.p016
// Pelletier #12
[<TestCase(@"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))",
    Result = [||], TestName = "Pelletier #12")>]

// resolution.p017
// Pelletier #13
[<TestCase(@"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)",
    Result = [||], TestName = "Pelletier #13")>]

// resolution.p018
// Pelletier #14
[<TestCase(@"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)",
    Result = [||], TestName = "Pelletier #14")>]

// resolution.p019
// Pelletier #15
[<TestCase(@"
    p ==> q <=> ~p \/ q",
    Result = [||], TestName = "Pelletier #15")>]

// resolution.p020
// Pelletier #16
[<TestCase(@"
    (p ==> q) \/ (q ==> p)",
    Result = [||], TestName = "Pelletier #16")>]

// resolution.p021
// Pelletier #17
[<TestCase(@"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)",
    Result = [||], TestName = "Pelletier #17")>]

// resolution.p022
// Pelletier #18
[<TestCase(@"
    exists y. forall x. P(y) ==> P(x)",
    Result = [|true|], TestName = "Pelletier #18")>]

// resolution.p023
// Pelletier #19
[<TestCase(@"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)",
    Result = [|true|], TestName = "Pelletier #19")>]

// resolution.p024
// Pelletier #20
[<TestCase(@"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
    Result = [|true|], TestName = "Pelletier #20")>]

// resolution.p025
// Pelletier #21
[<TestCase(@"
    (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))",
    Result = [|true; true; true|], TestName = "Pelletier #21")>]

// resolution.p026
// Pelletier #22
[<TestCase(@"
    (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))",
    Result = [|true; true|], TestName = "Pelletier #22")>]

// resolution.p027
// Pelletier #23
[<TestCase(@"
    (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))",
    Result = [|true; true|], TestName = "Pelletier #23")>]

// resolution.p028
// Pelletier #24
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))",
    Result = [| true |], TestName = "Pelletier #24")>]

// resolution.p029
// Pelletier #25
[<TestCase(@"
    (exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))",
    Result = [|true; true|], TestName = "Pelletier #25")>]

// resolution.p030
// Pelletier #26
[<TestCase(@"
    ((exists x. P(x)) <=> (exists x. Q(x))) /\
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
    ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))",
    Result = [|true; true; true; true|], TestName = "Pelletier #26")>]

// resolution.p031
// Pelletier #27
[<TestCase(@"
    (exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))",
    Result = [| true |], TestName = "Pelletier #27")>]

// resolution.p032
// Pelletier #28
[<TestCase(@"
    (forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))",
        Result = [| true; true; true; true |], TestName = "Pelletier #28")>]

// resolution.p033
// Pelletier #29
[<TestCase(@"
    (exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
    Result = [|true; true; true; true|], TestName = "Pelletier #29")>]

// resolution.p034
// Pelletier #30
[<TestCase(@"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))",
    Result = [| true |], TestName = "Pelletier #30")>]

// resolution.p035
// Pelletier #31
[<TestCase(@"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))",
    Result = [| true |], TestName = "Pelletier #31")>]

// resolution.p036
// Pelletier #32
[<TestCase(@"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))",
    Result = [| true |], TestName = "Pelletier #32")>]

// resolution.p037
// Pelletier #33
[<TestCase(@"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))",
    Result = [|true; true; true|], TestName = "Pelletier #33")>]

// resolution.p038
// Pelletier #34
[<TestCase(@"
    ((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))",
    Result = [|true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true|], TestName = "Pelletier #34")>]

// resolution.p039
// Pelletier #35
[<TestCase(@"
    exists x y. P(x,y) ==> (forall x y. P(x,y))",
    Result = [|true|], TestName = "Pelletier #35")>]

// resolution.p040
// Pelletier #36
[<TestCase(@"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))",
    Result = [|true|], TestName = "Pelletier #36")>]

// resolution.p041
// Pelletier #37
[<TestCase(@"
    (forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))", Result = [|true; true|], TestName = "Pelletier #37")>]

// resolution.p042
// Pelletier #38
[<TestCase(@"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))",
    Result = [| 3; 3; 3; 4 |], Category = "LongRunning", TestName = "Pelletier #38")>]

// resolution.p043
// Pelletier #39
[<TestCase(@"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))",
    Result = [|true|], TestName = "Pelletier #39")>]

// resolution.p044
// Pelletier #40
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))",
    Result = [|true|], TestName = "Pelletier #40")>]

// resolution.p045
// Pelletier #41
[<TestCase(@"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))",
    Result = [|true|], TestName = "Pelletier #41")>]

// resolution.p046
// Pelletier #42
[<TestCase(@"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))",
    Result = [|true|], TestName = "Pelletier #42")>]

// resolution.p047
// Pelletier #43
[<TestCase(@"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)",
    Result = [| 5; 5 |], Category = "LongRunning", TestName = "Pelletier #43")>]

// resolution.p048
// Pelletier #44
[<TestCase(@"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))",
    Result = [|true|], TestName = "Pelletier #44")>]

// resolution.p049
// Pelletier #45
[<TestCase(@"
    (forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))",
    Result = [|true|], TestName = "Pelletier #45")>]

// resolution.p050
// Pelletier #46
[<TestCase(@"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))",
    Result = [|true; true|], TestName = "Pelletier #46")>]

// resolution.p051
// Pelletier #55
[<TestCase(@"
    lives(agatha) /\ lives(butler) /\ lives(charles) /\ 
    (killed(agatha,agatha) \/ killed(butler,agatha) \/ 
     killed(charles,agatha)) /\ 
    (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\ 
    (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\ 
    (hates(agatha,agatha) /\ hates(agatha,charles)) /\ 
    (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\ 
    (forall x. hates(agatha,x) ==> hates(butler,x)) /\ 
    (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) 
    ==> killed(agatha,agatha) /\ 
        ~killed(butler,agatha) /\ 
        ~killed(charles,agatha)",
    Result = [|true; true|], TestName = "Pelletier #55")>]

// resolution.p05052
// Pelletier #57
[<TestCase(@"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))",
    Result = [|true|] , TestName = "Pelletier #57")>]

// resolution.p053
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
[<TestCase(@"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
    Result = [|true|] , TestName = "Pelletier #58")>]

// resolution.p054
// Pelletier #59
[<TestCase(@"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))",
    Result = [|true|] , TestName = "Pelletier #59")>]

// resolution.p055
// Pelletier #60
[<TestCase(@"
    forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)",
    Result = [|true; true|], TestName = "Pelletier #60")>]

// resolution.p056
// Gilmore #1
[<TestCase(@"
    exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)",
    Result = [|true|], Category = "LongRunning", TestName = "Gilmore #1")>]

// resolution.p057
// Gilmore #2
[<TestCase(@"
    exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))",
    Result = [|false|], Category = "LongRunning", TestName = "Gilmore #2")>]

// resolution.p058
// Gilmore #3
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)",
    Result = [|true|], TestName = "Gilmore #3")>]

// resolution.p059
// Gilmore #4
[<TestCase(@"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))",
        Result = [|true|], TestName = "Gilmore #4")>]

// resolution.p060
// Gilmore #5
[<TestCase(@"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)",
    Result = [|true|], TestName = "Gilmore #5")>]

// resolution.p061
// Gilmore #6
[<TestCase(@"
    forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))",
    Result = [|true|], TestName = "Gilmore #6")>]

// resolution.p062
// Gilmore #7
[<TestCase(@"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)",
    Result = [| true |], TestName = "Gilmore #7")>]

// resolution.p063
// Gilmore #8
[<TestCase(@"
    exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)",
    Result = [| true |], TestName = "Gilmore #8")>]

// resolution.p064
// Gilmore #9
[<TestCase(@"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))",
    Result = [| true |], Category = "LongRunning", TestName = "Gilmore #9")>]

let ``3 Pure Resolution`` f =
    parse f
    |> presolution
    |> List.toArray

// resolution.p065 is same as resolution.p127

// resolution.p066 is same as resolution.p118

// resolution.p067
// Pelletier #01
[<TestCase(@"
    p ==> q <=> ~q ==> ~p",
    Result = [||], TestName = "Pelletier #01")>]

// resolution.p068
// Pelletier #02
[<TestCase(@"
    ~ ~p <=> p",
    Result = [||], TestName = "Pelletier #02")>]

// resolution.p069
// Pelletier #03
[<TestCase(@"
    ~(p ==> q) ==> q ==> p",
    Result = [||], TestName = "Pelletier #03")>]

// resolution.p070
// Pelletier #04
[<TestCase(@"
    ~p ==> q <=> ~q ==> p",
    Result = [||], TestName = "Pelletier #04")>]

// resolution.p071
// Pelletier #05
[<TestCase(@"
    (p \/ q ==> p \/ r) ==> p \/ (q ==> r)",
    Result = [||], TestName = "Pelletier #05")>]

// resolution.p072
// Pelletier #06
[<TestCase(@"
    p \/ ~p",
    Result = [||], TestName = "Pelletier #06")>]

// resolution.p073
// Pelletier #07
[<TestCase(@"
    p \/ ~ ~ ~p",
    Result = [||], TestName = "Pelletier #07")>]

// resolution.p074
// Pelletier #08
[<TestCase(@"
    ((p ==> q) ==> p) ==> p",
    Result = [||], TestName = "Pelletier #08")>]

// resolution.p075
// Pelletier #09
[<TestCase(@"
    (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)",
    Result = [||], TestName = "Pelletier #09")>]

// resolution.p076
// Pelletier #10
[<TestCase(@"
    (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)",
    Result = [||], TestName = "Pelletier #10")>]

// resolution.p077
// Pelletier #11
[<TestCase(@"
    p <=> p",
    Result = [||], TestName = "Pelletier #11")>]

// resolution.p078
// Pelletier #12
[<TestCase(@"
    ((p <=> q) <=> r) <=> (p <=> (q <=> r))",
    Result = [||], TestName = "Pelletier #12")>]

// resolution.p079
// Pelletier #13
[<TestCase(@"
    p \/ q /\ r <=> (p \/ q) /\ (p \/ r)",
    Result = [||], TestName = "Pelletier #13")>]

// resolution.p080
// Pelletier #14
[<TestCase(@"
    (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)",
    Result = [||], TestName = "Pelletier #14")>]

// resolution.p081
// Pelletier #15
[<TestCase(@"
    p ==> q <=> ~p \/ q",
    Result = [||], TestName = "Pelletier #15")>]

// resolution.p082
// Pelletier #16
[<TestCase(@"
    (p ==> q) \/ (q ==> p)",
    Result = [||], TestName = "Pelletier #16")>]

// resolution.p083
// Pelletier #17
[<TestCase(@"
    p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)",
    Result = [||], TestName = "Pelletier #17")>]

// resolution.p084
// Pelletier #18
[<TestCase(@"
    exists y. forall x. P(y) ==> P(x)",
    Result = [| true |], TestName = "Pelletier #18")>]

// resolution.p085
// Pelletier #19
[<TestCase(@"
    exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)",
    Result = [| true |], TestName = "Pelletier #19")>]

// resolution.p086
// Pelletier #20
[<TestCase(@"
    (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
    ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
    Result = [| true |], TestName = "Pelletier #20")>]

// resolution.p087
// Pelletier #21
[<TestCase(@"
    (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))",
    Result = [| true; true; true |], TestName = "Pelletier #21")>]

// resolution.p088
// Pelletier #22
[<TestCase(@"
    (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))",
    Result = [| true; true |], TestName = "Pelletier #22")>]

// resolution.p089
// Pelletier #23
[<TestCase(@"
    (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))",
    Result = [| true; true |], TestName = "Pelletier #23")>]

// resolution.p090
// Pelletier #24
[<TestCase(@"
    ~(exists x. U(x) /\ Q(x)) /\ 
    (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
    ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
    (forall x. Q(x) /\ R(x) ==> U(x)) ==> 
    (exists x. P(x) /\ R(x))",
    Result = [| true |], TestName = "Pelletier #24")>]

// resolution.p091
// Pelletier #25
[<TestCase(@"
    (exists x. P(x)) /\ 
    (forall x. U(x) ==> ~G(x) /\ R(x)) /\ 
    (forall x. P(x) ==> G(x) /\ U(x)) /\ 
    ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) 
    ==> (exists x. Q(x) /\ P(x))",
    Result = [| true; true |], TestName = "Pelletier #25")>]

// resolution.p092
// Pelletier #26
[<TestCase(@"
    ((exists x. P(x)) <=> (exists x. Q(x))) /\
    (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
    ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))",
    Result = [| true; true; true; true |], TestName = "Pelletier #26")>]

// resolution.p093
// Pelletier #27
[<TestCase(@"
    (exists x. P(x) /\ ~Q(x)) /\ 
    (forall x. P(x) ==> R(x)) /\ 
    (forall x. U(x) /\ V(x) ==> P(x)) /\ 
    (exists x. R(x) /\ ~Q(x)) 
    ==> (forall x. U(x) ==> ~R(x)) 
        ==> (forall x. U(x) ==> ~V(x))",
    Result = [| true |], TestName = "Pelletier #27")>]

// resolution.p094
// Pelletier #28
[<TestCase(@"
    (forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))",
    Result = [| true; true; true; true |], TestName = "Pelletier #28")>]

// resolution.p095
// Pelletier #29
[<TestCase(@"
    (exists x. P(x)) /\ (exists x. G(x)) ==> 
    ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> 
     (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
     Result = [|true; true; true; true|], TestName = "Pelletier #29")>]

// resolution.p096
// Pelletier #30
[<TestCase(@"
    (forall x. P(x) \/ G(x) ==> ~H(x)) /\ 
    (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) 
    ==> (forall x. U(x))",
    Result = [|true|], TestName = "Pelletier #30")>]

// resolution.p097
// Pelletier #31
[<TestCase(@"
    ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ 
    (exists x. Q(x) /\ P(x)) /\ 
    (forall x. ~H(x) ==> J(x)) 
    ==> (exists x. Q(x) /\ J(x))",
    Result = [|true|], TestName = "Pelletier #31")>]

// resolution.p098
// Pelletier #32
[<TestCase(@"
    (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
    (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
    (forall x. R(x) ==> H(x)) 
    ==> (forall x. P(x) /\ R(x) ==> J(x))",
    Result = [|true|], TestName = "Pelletier #32")>]

// resolution.p099
// Pelletier #33
[<TestCase(@"
    (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> 
    (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))",
    Result = [|true; true; true|], TestName = "Pelletier #33")>]

// resolution.p100
// Pelletier #34
[<TestCase(@"
    ((exists x. forall y. P(x) <=> P(y)) <=>
     ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
     ((exists x. P(x)) <=> (forall y. P(y))))",
    Result = [|true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true|], TestName = "Pelletier #34")>]

// resolution.p0101
// Pelletier #35
[<TestCase(@"
    exists x y. P(x,y) ==> (forall x y. P(x,y))",
    Result = [|true|], TestName = "Pelletier #35")>]

// resolution.p102
// Pelletier #36
[<TestCase(@"
    (forall x. exists y. P(x,y)) /\ 
    (forall x. exists y. G(x,y)) /\ 
    (forall x y. P(x,y) \/ G(x,y) 
    ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) 
        ==> (forall x. exists y. H(x,y))",
    Result = [|true|], TestName = "Pelletier #36")>]

// resolution.p103
// Pelletier #37
[<TestCase(@"
    (forall z. 
      exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ 
      (P(y,w) ==> (exists u. Q(u,w)))) /\ 
    (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ 
    ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> 
    (forall x. exists y. R(x,y))",
    Result = [| true; true |], TestName = "Pelletier #37")>]

// resolution.p104
// Pelletier #38
[<TestCase(@"
    (forall x. 
      P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
    (forall x. 
      (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
      (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
      (exists z w. P(z) /\ R(x,w) /\ R(w,z))))",
    Result = [| 3; 3; 3; 4 |], Category = "LongRunning", TestName = "Pelletier #38")>]

// resolution.p105
// Pelletier #39
[<TestCase(@"
    ~(exists x. forall y. P(y,x) <=> ~P(y,y))",
    Result = [|true|], TestName = "Pelletier #39")>]

// resolution.p106
// Pelletier #40
[<TestCase(@"
    (exists y. forall x. P(x,y) <=> P(x,x))
    ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))",
    Result = [|true|], TestName = "Pelletier #40")>]

// resolution.p107
// Pelletier #41
[<TestCase(@"
    (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
    ==> ~(exists z. forall x. P(x,z))",
    Result = [|true|], TestName = "Pelletier #41")>]

// resolution.p108
// Pelletier #42
[<TestCase(@"
    ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))",
    Result = [|true|], TestName = "Pelletier #43")>]
    
// resolution.p109
// Pelletier #43
[<TestCase(@"
    (forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) 
    ==> forall x y. Q(x,y) <=> Q(y,x)",
    Result = [| 5; 5 |], Category = "LongRunning", TestName = "Pelletier #43")>]

// resolution.p110
// Pelletier #44
[<TestCase(@"
    (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
    (exists y. G(y) /\ ~H(x,y))) /\ 
    (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> 
    (exists x. J(x) /\ ~P(x))",
    Result = [|true|], TestName = "Pelletier #44")>]

// resolution.p11
// Pelletier #45
[<TestCase(@"
    (forall x. 
      P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> 
        (forall y. G(y) /\ H(x,y) ==> R(y))) /\ 
    ~(exists y. L(y) /\ R(y)) /\ 
    (exists x. P(x) /\ (forall y. H(x,y) ==> 
      L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> 
    (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))",
    Result = [|true|], TestName = "Pelletier #45")>]

// resolution.p112
// Pelletier #46
[<TestCase(@"
    (forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\ 
    ((exists x. P(x) /\ ~G(x)) ==> 
     (exists x. P(x) /\ ~G(x) /\ 
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\ 
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==> 
    (forall x. P(x) ==> G(x))",
    Result = [| true; true |], TestName = "Pelletier #46")>]

// resolution.p113
// Pelletier #55
[<TestCase(@"
    lives(agatha) /\ lives(butler) /\ lives(charles) /\ 
    (killed(agatha,agatha) \/ killed(butler,agatha) \/ 
     killed(charles,agatha)) /\ 
    (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\ 
    (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\ 
    (hates(agatha,agatha) /\ hates(agatha,charles)) /\ 
    (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\ 
    (forall x. hates(agatha,x) ==> hates(butler,x)) /\ 
    (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) 
    ==> killed(agatha,agatha) /\ 
        ~killed(butler,agatha) /\ 
        ~killed(charles,agatha)",
    Result = [| true; true |], TestName = "Pelletier #55")>]

// resolution.p114
// Pelletier #57
[<TestCase(@"
    P(f((a),b),f(b,c)) /\ 
    P(f(b,c),f(a,c)) /\ 
    (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z)) 
    ==> P(f(a,b),f(a,c))",
    Result = [| true |], TestName = "Pelletier #57")>]

// resolution.p115
// Pelletier #58
// TODO: Is this a conrrect translation from Pelletier #58?
[<TestCase(@"
    forall P Q R. forall x. exists v. exists w. forall y. forall z. 
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
    Result = [| true |], TestName = "Pelletier #58")>]

// resolution.p116
// Pelletier #59
[<TestCase(@"
    (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))",
    Result = [| true |], TestName = "Pelletier #59")>]

// resolution.p117
// Pelletier #60
[<TestCase(@"
    forall x. P(x,f(x)) <=> 
              exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)",
    Result = [| true; true |], TestName = "Pelletier #60")>]

// resolution.p118
// Gilmore #1
[<TestCase(@"
    exists x. forall y z. 
        ((F(y) ==> G(y)) <=> F(x)) /\ 
        ((F(y) ==> H(y)) <=> G(x)) /\ 
        (((F(y) ==> G(y)) ==> H(y)) <=> H(x)) 
        ==> F(z) /\ G(z) /\ H(z)",
    Result = [|true|], Category = "LongRunning", TestName = "Gilmore #1")>]

// resolution.p119
// Gilmore #2
[<TestCase(@"
    exists x y. forall z. 
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x)) 
        ==> (F(x,y) <=> F(x,z))",
    Result = [|false|], Category = "LongRunning", TestName = "Gilmore #2")>]

// resolution.p120
// Gilmore #3
[<TestCase(@"
    exists x. forall y z. 
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\ 
        ((F(z,x) ==> G(x)) ==> H(z)) /\ 
        F(x,y) 
        ==> F(z,z)",
     Result = [| true |], TestName = "Gilmore #3")>]

// resolution.p121
// Gilmore #4
[<TestCase(@"
    exists x y. forall z. 
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\ 
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))",
    Result = [| true |], TestName = "Gilmore #4")>]
// resolution.p122
// Gilmore #5
[<TestCase(@"
    (forall x. exists y. F(x,y) \/ F(y,x)) /\ 
    (forall x y. F(y,x) ==> F(y,y)) 
    ==> exists z. F(z,z)",
    Result = [| true |], TestName = "Gilmore #5")>]

// resolution.p123
// Gilmore #6
[<TestCase(@"
    forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))",
    Result = [| true |], TestName = "Gilmore #6")>]

// resolution.p124
// Gilmore #7
[<TestCase(@"
    (forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
    (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
    ==> exists v w. K(v) /\ L(w) /\ G(v,w)",
    Result = [| true |], TestName = "Gilmore #7")>]

// resolution.p125
// Gilmore #8
[<TestCase(@"
    exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)",
    Result = [| true |], TestName = "Gilmore #8")>]

// resolution.p126
// Gilmore #9
[<TestCase(@"
    forall x. exists y. forall z. 
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ 
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) 
          ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) 
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ 
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))",
    Result = [| true |], Category = "LongRunning", TestName = "Gilmore #9")>]

// resolution.p127
// Davis Putnam #1
[<TestCase(@"
    exists x. exists y. forall z. 
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
    Result = [| true |], TestName = "Davis Putnam #1")>]

// resolution.p128
// Los #1
[<TestCase(@"
    (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
    (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
    (forall x y. Q(x,y) ==> Q(y,x)) /\ 
    (forall x y. P(x,y) \/ Q(x,y)) 
    ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
    Result = [|true|], TestName = "Los #1")>]

let ``4 Positive Resolution`` f =
    parse f
    |> resolution003
    |> List.toArray
