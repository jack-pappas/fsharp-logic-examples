// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook.Tests

module qelim =
    open NUnit.Framework
    open FsUnit

    open Reasoning.Automated.Harrison.Handbook.lib
    open Reasoning.Automated.Harrison.Handbook.formulas
    open Reasoning.Automated.Harrison.Handbook.prop
    open Reasoning.Automated.Harrison.Handbook.folMod
    open Reasoning.Automated.Harrison.Handbook.skolem
    open Reasoning.Automated.Harrison.Handbook.equal
    open Reasoning.Automated.Harrison.Handbook.decidable
    open Reasoning.Automated.Harrison.Handbook.qelim

    // pg. 335
    //  ------------------------------------------------------------------------- // 
    //  Examples.                                                                 // 
    //  ------------------------------------------------------------------------- // 

    let results = [| 
                    True;
                    True;
                    Atom (R ("<",[Var "x"; Var "y"]));
                    Not ((Or (Atom (R ("<",[Var "b"; Var "a"])),Atom (R ("<",[Var "b"; Var "a"])))));
                    True;
                    True;
                    False;
                    |]
    
    // Manually mapping results by indices
    [<TestCase("forall x y. exists z. z < x /\ z < y", 0)>]
    [<TestCase("exists z. z < x /\ z < y", 1)>]
    [<TestCase("exists z. x < z /\ z < y", 2)>]
    [<TestCase( "(forall x. x < a ==> x < b)", 3)>]
    [<TestCase("forall a b. (forall x. x < a ==> x < b) <=> a <= b", 4)>]
    [<TestCase("forall a b. (forall x. x < a <=> x < b) <=> a = b", 5)>]
    [<TestCase("exists x y z. forall u.
                        x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)", 6)>]
    let ``test quelim_dlo`` (f, idx) =
        quelim_dlo (parse f)
        |> should equal results.[idx]

