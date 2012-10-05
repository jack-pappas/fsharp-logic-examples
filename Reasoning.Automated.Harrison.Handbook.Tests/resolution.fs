// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook.Tests

module resolution =
    open Reasoning.Automated.Harrison.Handbook.lib
    open Reasoning.Automated.Harrison.Handbook.formulas
    open Reasoning.Automated.Harrison.Handbook.prop
    open Reasoning.Automated.Harrison.Handbook.folMod
    open Reasoning.Automated.Harrison.Handbook.skolem
    open Reasoning.Automated.Harrison.Handbook.unif
    open Reasoning.Automated.Harrison.Handbook.tableaux
    open Reasoning.Automated.Harrison.Handbook.resolution

    open NUnit.Framework
    open FsUnit

    // pg. 185
    // ------------------------------------------------------------------------- //
    // Simple example that works well.                                           //
    // ------------------------------------------------------------------------- //

    [<Test>]
    let ``test resolution001``() =
        resolution001 (parse "
            exists x. exists y. forall z. 
                (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
                ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))")
        |> should equal [true]

    // pg. 192
    // ------------------------------------------------------------------------- //
    // This is now a lot quicker.                                                //
    // ------------------------------------------------------------------------- //

    [<Test>]
    let ``test resolution002``() =
        resolution002 (parse "
            exists x. exists y. forall z. 
                (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
                ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))")
        |> should equal [true]

    // pg. 198
    // ------------------------------------------------------------------------- //
    // Example: the (in)famous Los problem.                                      //
    // ------------------------------------------------------------------------- //

    [<Test>]
    let ``test presolution``() =
        presolution (parse "
        (forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\ 
        (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\ 
        (forall x y. Q(x,y) ==> Q(y,x)) /\ 
        (forall x y. P(x,y) \/ Q(x,y)) 
        ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))")
        |> should equal [true]

    // ------------------------------------------------------------------------- //
    // The Pelletier examples again.                                             //
    // ------------------------------------------------------------------------- //

    [<TestCase("p ==> q <=> ~q ==> ~p")>]    
    [<TestCase("~ ~p <=> p")>]
    [<TestCase("~(p ==> q) ==> q ==> p")>]
    [<TestCase("~p ==> q <=> ~q ==> p")>]
    [<TestCase("(p \/ q ==> p \/ r) ==> p \/ (q ==> r)")>]
    [<TestCase("p \/ ~p")>]
    [<TestCase("p \/ ~ ~ ~p")>]
    [<TestCase("((p ==> q) ==> p) ==> p")>]    
    [<TestCase("(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)")>]
    [<TestCase("(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)")>]
    [<TestCase("p <=> p")>]
    [<TestCase("((p <=> q) <=> r) <=> (p <=> (q <=> r))")>]
    [<TestCase("p \/ q /\ r <=> (p \/ q) /\ (p \/ r)")>]
    [<TestCase("(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)")>]
    [<TestCase("p ==> q <=> ~p \/ q")>]
    [<TestCase("(p ==> q) \/ (q ==> p)")>]
    [<TestCase("p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)")>]
    let ``test presolution returns empty`` f =
        presolution (parse f)
        |> should equal []

    [<Test>]
    let ``test resolution003``() =
        resolution003 (parse "
            exists x. exists y. forall z. 
                (F(x,y) ==> (F(y,z) /\ F(z,z))) /\ 
                ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))")
        |> should equal [true]

    [<TestCase("p ==> q <=> ~q ==> ~p")>]    
    [<TestCase("~ ~p <=> p")>]
    [<TestCase("~(p ==> q) ==> q ==> p")>]
    [<TestCase("~p ==> q <=> ~q ==> p")>]
    [<TestCase("(p \/ q ==> p \/ r) ==> p \/ (q ==> r)")>]
    [<TestCase("p \/ ~p")>]
    [<TestCase("p \/ ~ ~ ~p")>]
    [<TestCase("((p ==> q) ==> p) ==> p")>]    
    [<TestCase("(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)")>]
    [<TestCase("(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)")>]
    [<TestCase("p <=> p")>]
    [<TestCase("((p <=> q) <=> r) <=> (p <=> (q <=> r))")>]
    [<TestCase("p \/ q /\ r <=> (p \/ q) /\ (p \/ r)")>]
    [<TestCase("(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)")>]
    [<TestCase("p ==> q <=> ~p \/ q")>]
    [<TestCase("(p ==> q) \/ (q ==> p)")>]
    [<TestCase("p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)")>]
    let ``test resolution003 returns empty`` f =
        resolution003 (parse f)
        |> should equal []