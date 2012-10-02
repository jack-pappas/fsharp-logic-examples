// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook.Tests

// Below tests take a few seconds to complete
module propexamples =
    open NUnit.Framework
    open FsUnit

    open Reasoning.Automated.Harrison.Handbook.lib
    open Reasoning.Automated.Harrison.Handbook.formulas
    open Reasoning.Automated.Harrison.Handbook.prop
    open Reasoning.Automated.Harrison.Handbook.propexamples

    // pg. 63
    // ------------------------------------------------------------------------- //
    // Some currently tractable examples.                                        //
    // ------------------------------------------------------------------------- //

    [<TestCase(3, 3, 5, Result=false)>]
    [<TestCase(3, 3, 6, Result=true)>]
    let ``test ramsey``(s, t, n) =
        tautology(ramsey s t n)

    // pg. 72
    // ------------------------------------------------------------------------- //
    // Examples.                                                                 //
    // ------------------------------------------------------------------------- //

    [<TestCase(7, Result=true)>]
    [<TestCase(9, Result=false)>]
    [<TestCase(11, Result=true)>]
    let ``test prime`` p =
        tautology(prime p)