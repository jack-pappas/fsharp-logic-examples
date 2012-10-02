// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook.Tests

module lib =
    open NUnit.Framework
    open FsUnit

    open Reasoning.Automated.Harrison.Handbook.lib

    // pg. 621
    let smallsqs = fpf [1;2;3] [1;4;9]

    [<Test>]
    let ``test finite partial function``() =
        graph smallsqs        
        |> should equal [(1, 1); (2, 4); (3, 9)]

    [<Test>]
    let ``test finite partial function with undefine``() =
        graph (undefine 2 smallsqs)
        |> should equal [(1, 1); (3, 9)]

    [<Test>]
    let ``test update finite partial function``() =
        graph ((3 |-> 0) smallsqs)        
        |> should equal [(1, 1); (2, 4); (3, 0)]

    [<Test>]
    let ``test apply finite partial function``() =
        apply smallsqs 3
        |> should equal 9
