// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook.Tests

module tableaux =
    open Reasoning.Automated.Harrison.Handbook.lib
    open Reasoning.Automated.Harrison.Handbook.formulas
    open Reasoning.Automated.Harrison.Handbook.prop
    open Reasoning.Automated.Harrison.Handbook.folMod
    open Reasoning.Automated.Harrison.Handbook.skolem
    open Reasoning.Automated.Harrison.Handbook.herbrand
    open Reasoning.Automated.Harrison.Handbook.tableaux

    open NUnit.Framework
    open FsUnit

    // pg. 175
    // ------------------------------------------------------------------------- //
    // Examples.                                                                 //
    // ------------------------------------------------------------------------- //

    [<Test>]
    let ``test prawitz``() =
        prawitz (parse "
            (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) 
            ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))")
        |> should equal 2

    [<TestCase("exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)", 3, 3)>]
    [<TestCase("(forall x y. exists z. forall w. P(x) /\ Q(y) 
                ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))", 2, 19)>]
    [<TestCase("~(exists x. U(x) /\ Q(x)) /\ 
                (forall x. P(x) ==> Q(x) \/ R(x)) /\ 
                ~(exists x. P(x) ==> (exists x. Q(x))) /\ 
                (forall x. Q(x) /\ R(x) ==> U(x)) 
                ==> (exists x. P(x) /\ R(x))", 1, 1)>]
    [<TestCase("~(exists x. forall y. P(y,x) <=> ~P(y,y))", 1, 1)>]
    [<TestCase("~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))", 2, 3)>]
    [<TestCase("(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)", 2, 26)>]
    [<TestCase("(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ 
                (exists y. G(y) /\ ~H(x,y))) /\ 
                (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) 
                ==> (exists x. J(x) /\ ~P(x))", 2, 3)>]
    [<TestCase("(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))", 2, 2)>]
    [<TestCase("forall x. P(x,f(x)) <=> 
                  exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)", 1, 13)>]
    let ``test compare`` (f, x, y) =
        compare (parse f)
        |> should equal (x, y)

    // pg. 178
    // ------------------------------------------------------------------------- //
    // Example.                                                                  //
    // ------------------------------------------------------------------------- //

    [<Test>]
    let ``test tab``() =
        tab (parse "
	        (forall x. 
              P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> 
              (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> 
            (forall x. 
              (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ 
              (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ 
              (exists z w. P(z) /\ R(x,w) /\ R(w,z))))")
        |> should equal 4

    // pg. 178
    // ------------------------------------------------------------------------- //
    // Example: the Andrews challenge.                                           //
    // ------------------------------------------------------------------------- //

    [<Test>]
    let ``test splittab 1``() =
        splittab (parse "
	        ((exists x. forall y. P(x) <=> P(y)) <=> 
             ((exists x. Q(x)) <=> (forall y. Q(y)))) <=> 
            ((exists x. forall y. Q(x) <=> Q(y)) <=> 
             ((exists x. P(x)) <=> (forall y. P(y))))")
        |> should equal [5; 4; 5; 3; 3; 3; 2; 4; 6; 2; 3; 3; 4; 3; 3; 3; 3; 2; 2; 3; 6; 3; 2; 4; 3; 3; 3; 3; 3; 4; 4; 4]

    // pg. 179
    // ------------------------------------------------------------------------- //
    // Another nice example from EWD 1602.                                       //
    // ------------------------------------------------------------------------- //

    [<Test>]
    let ``test splittab 2``() =
        splittab (parse "
        (forall x. x <= x) /\ 
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\ 
        (forall x y. f(x) <= y <=> x <= g(y)) 
        ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ 
            (forall x y. x <= y ==> g(x) <= g(y))")
        |> should equal [9; 9]