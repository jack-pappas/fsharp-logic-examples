// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.lib

open Reasoning.Automated.Harrison.Handbook.lib
open NUnit.Framework
open FsUnit

// Tests for library functions derived from
// the results shown on Pg. 619-621.

[<Test>]
let ``butlast``() =
    butlast [1; 2; 3; 4]
    |> should equal [1; 2; 3]

[<Test>]
let ``chop_list``() =
    chop_list 3 [1; 2; 3; 4; 5]
    |> should equal ([1; 2; 3], [4; 5])

[<Test>]
let ``explode``() =
    explode "hello"
    |> should equal ["h"; "e"; "l"; "l"; "o"]

[<Test>]
let ``implode``() =
    implode ["w"; "x"; "y"; "z"]
    |> should equal "wxyz"

[<Test>]
let ``insertat``() =
    insertat 3 9 [0; 1; 2; 3; 4; 5]
    |> should equal [0; 1; 2; 9; 3; 4; 5]

[<Test>]
let ``last``() =
    last [1; 2; 3; 4]
    |> should equal 4

[<Test>]
let ``sort all``() =
    sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5]
    |> should equal [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9]

[<Test>]
let ``sort by increasing length``() =
    sort (increasing List.length) [[1]; [1;2;3]; []; [3; 4]]
    |> should equal [[]; [1]; [3; 4]; [1; 2; 3]]

[<Test>]
let ``unions``() =
    unions [[1; 2; 3]; [4; 8; 12]; [3; 6; 9; 12]; [1]]
    |> should equal [1; 2; 3; 4; 6; 8; 9; 12]

[<Test>]
let ``image``() =
    image (fun x -> x % 2) [1; 2; 3; 4; 5]
    |> should equal [0; 1]    

[<Test>]
let ``allsubsets``() =
    allsubsets [1; 2; 3]
    |> should equal [[]; [1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]

[<Test>]
let ``allnonemptysubsets``() =
    allnonemptysubsets [1; 2; 3]
    |> should equal [[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]

[<Test>]
let ``allsets``() =
    allsets 2 [1; 2; 3]
    |> should equal [[1; 2]; [1; 3]; [2; 3]]

[<Test>]
let ``allpairs``() =
    allpairs (fun x y -> x * y) [2; 3; 5] [7; 11]
    |> should equal [14; 22; 21; 33; 35; 55]

[<Test>]
let ``distinctpairs``() =
    distinctpairs [1; 2; 3; 4]
    |> should equal [(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (3, 4)]

[<Test>]
let ``assoc``() =
    assoc 3 [1,2; 2,4; 3,9; 4,16]
    |> should equal 9

// pg. 621
let smallsqs = fpf [1; 2; 3] [1; 4; 9]

[<Test>]
let ``finite partial function``() =
    graph smallsqs        
    |> should equal [(1, 1); (2, 4); (3, 9)]

[<Test>]
let ``finite partial function with undefine``() =
    graph (undefine 2 smallsqs)
    |> should equal [(1, 1); (3, 9)]

[<Test>]
let ``update finite partial function``() =
    graph ((3 |-> 0) smallsqs)        
    |> should equal [(1, 1); (2, 4); (3, 0)]

[<Test>]
let ``apply finite partial function``() =
    apply smallsqs 3
    |> should equal 9

// Some additional tests (not in the book)
[<Test>]
let ``dom finite partial function``() =
    dom smallsqs
    |> should equal [1; 2; 3]

[<Test>]
let ``ran finite partial function``() =
    ran smallsqs
    |> should equal [1; 4; 9]

