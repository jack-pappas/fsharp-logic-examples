// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.lib

open FSharpx.Books.AutomatedReasoning.lib
open FSharp.Compatibility.OCaml.Num 

open NUnit.Framework
open FsUnit

// Tests for library functions derived from
// the results shown on Pg. 619-621.

// lib.p001
[<Test>]
let ``List butlast`` () =
    butlast [1; 2; 3; 4]
    |> should equal [1; 2; 3]

// lib.p002
[<Test>]
let ``List chop_list`` () =
    chop_list 3 [1; 2; 3; 4; 5]
    |> should equal ([1; 2; 3], [4; 5])

// lib.p003
// Note: Since List.iter returns unit, need to use function with side effect
// i.e. sb.Append to create something to test.
[<Test>]
let ``List iter`` () =
    let l = ["See "; "the "; "dog"]
    let sb = System.Text.StringBuilder ()
    l |> List.iter (fun (s : string) ->
        sb.Append s
        |> ignore)
    sb.ToString ()
    |> should equal @"See the dog"
    
// lib.p004
[<Test>]
let ``List nth`` () =
    List.nth [0; 1; 2; 3] 2
    |> should equal 2
    
// lib.p005
[<Test>]
let ``List end_itlist`` () =
    end_itlist (fun x y -> x * y) [1; 2; 3; 4]
    |> should equal 24
    
// lib.p006
[<Test>]
let ``List exists`` () =
    List.exists (fun x -> x % 2 = 0) [1; 2; 3]
    |> should equal true

// lib.p007
[<Test>]
let ``String explode`` () =
    explode "hello"
    |> should equal ["h"; "e"; "l"; "l"; "o"]

// lib.p008
[<Test>]
let ``List forall`` () =
    List.forall (fun x -> (x < 5)) [1; 2; 3]
    |> should equal true

// lib.p009
[<Test>]
let ``List forall2`` () =
    List.forall2 (fun x y -> (x < y)) [1; 2; 3; 4] [3; 4; 5; 6]
    |> should equal true

// lib.p010
[<Test>]
let ``List head`` () =
    List.head [1; 2; 3]
    |> should equal 1

// lib.p011
[<Test>]
let ``String implode`` () =
    implode ["w"; "x"; "y"; "z"]
    |> should equal "wxyz"

// lib.p012
[<Test>]
let ``List insertat`` () =
    insertat 3 9 [0; 1; 2; 3; 4; 5]
    |> should equal [0; 1; 2; 9; 3; 4; 5]

// lib.p013
[<Test>]
let ``List foldBack`` () =
    List.foldBack (fun x y -> x + y) [1; 2; 3] 5
    |> should equal 11

// lib.p014
[<Test>]
let ``List foldBack2`` () =
    List.foldBack2 (fun a x y -> a + x + y) ["a"; "b"; "c"] ["1"; "2"; "3"] " Hello"
    |> should equal "a1b2c3 Hello"

// lib.p015
[<Test>]
let ``List last`` () =
    last [1; 2; 3; 4]
    |> should equal 4

// lib.p016
[<Test>]
let ``List map`` () =
    List.map (fun x -> x + 5) [1; 2; 3]
    |> should equal [6; 7; 8]

// lib.p017
[<Test>]
let ``List map2`` () =
    List.map2 (fun x y -> x + y) [1; 2; 3] [10; 11; 12]
    |> should equal [11; 13; 15]

// lib.p018
[<Test>]
let ``List mapfilter`` () =
    mapfilter (fun x -> x % 2 = 0) [1; 2; 3; 4]
    |> should equal [false; true; false; true]

// lib.p019
[<Test>]
let ``List replicate`` () =
    List.replicate 4 9
    |> should equal [9; 9; 9; 9]

// lib.p020
[<Test>]
let ``List rev`` () =
    List.rev [1; 2; 3; 4]
    |> should equal [4; 3; 2; 1]

// lib.p021
[<Test>]
let ``List tail`` () =
    List.tail [1; 2; 3; 4]
    |> should equal [2; 3; 4]

// lib.p022
[<Test>]
let ``List unzip`` () =
    List.unzip [(1,"a"); (2,"b"); (3,"c")]
    |> should equal ([1; 2; 3], ["a"; "b"; "c"])

// lib.p023
[<Test>]
let ``List zip`` () =
    List.zip [1; 2; 3] ["a"; "b"; "c"]
    |> should equal [(1, "a"); (2, "b"); (3, "c")]

// lib.p024
[<Test>]
let ``sort all`` () =
    sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5]
    |> should equal [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9]

// lib.p025
[<Test>]
let ``sort uniq`` () =
    uniq (sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5])
    |> should equal [1; 2; 3; 4; 5; 6; 9]

// lib.p026
[<Test>]
let ``sort by increasing length`` () =
    sort (increasing List.length) [[1]; [1;2;3]; []; [3; 4]]
    |> should equal [[]; [1]; [3; 4]; [1; 2; 3]]

// lib.p027
[<Test>]
let ``unions`` () =
    unions [[1; 2; 3]; [4; 8; 12]; [3; 6; 9; 12]; [1]]
    |> should equal [1; 2; 3; 4; 6; 8; 9; 12]

// lib.p028
[<Test>]
let ``image`` () =
    image (fun x -> x % 2) [1; 2; 3; 4; 5]
    |> should equal [0; 1]    

// lib.p029
[<Test>]
let ``allsubsets`` () =
    allsubsets [1; 2; 3]
    |> should equal [[]; [1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]

// lib.p030
[<Test>]
let ``allnonemptysubsets`` () =
    allnonemptysubsets [1; 2; 3]
    |> should equal [[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]

// lib.p031
[<Test>]
let ``allsets`` () =
    allsets 2 [1; 2; 3]
    |> should equal [[1; 2]; [1; 3]; [2; 3]]

// lib.p032
[<Test>]
let ``allpairs`` () =
    allpairs (fun x y -> x * y) [2; 3; 5] [7; 11]
    |> should equal [14; 22; 21; 33; 35; 55]

// lib.p033
[<Test>]
let ``distinctpairs`` () =
    distinctpairs [1; 2; 3; 4]
    |> should equal [(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (3, 4)]

// lib.p034
[<Test>]
let ``assoc`` () =
    assoc 3 [1,2; 2,4; 3,9; 4,16]
    |> should equal 9

// pg. 621
let smallsqs = fpf [1; 2; 3] [1; 4; 9]

// lib.p035
[<Test>]
let ``finite partial function`` () =
    graph smallsqs        
    |> should equal [(1, 1); (2, 4); (3, 9)]

// lib.p036
[<Test>]
let ``finite partial function with undefine`` () =
    graph (undefine 2 smallsqs)
    |> should equal [(1, 1); (3, 9)]

// lib.p037
[<Test>]
let ``finite partial function update`` () =
    graph ((3 |-> 0) smallsqs)        
    |> should equal [(1, 1); (2, 4); (3, 0)]

// lib.p038
[<Test>]
let ``finite partial function apply`` () =
    apply smallsqs 3
    |> should equal 9

// Some additional tests (not in the book)

// NOTE: The ( ** ) operator has been replaced with the equivalent built-in F# operator ( << ).
let addFive x = x + 5
let timesFour x = x * 4

// lib.p039
// (2 * 4) + 5 = 13
[<Test>]
let ``backward composition operator`` () =
    (addFive << timesFour) 2
    |> should equal 13

// lib.p040
// (2 + 5) * 4 = 28
[<Test>]
let ``forward composition operator`` () =
    (addFive >> timesFour) 2
    |> should equal 28

// lib.p041
[<Test>]
let ``gcd test`` () =
    gcd_num (num_of_int 12) (num_of_int 15)
    |> should equal (num_of_int 3)

// lib.p042
[<Test>]
let ``lcm test`` () =
    lcm_num (num_of_int 12) (num_of_int 15)
    |> should equal (num_of_int 60)

// lib.p043
[<Test>]
let ``non test`` () =
    non (fun x -> x % 2 = 0) 5
    |> should equal true

// lib.p044
[<Test>]
let ``funpow test`` () =
    funpow 10 (fun x -> x + x) 1
    |> should equal 1024

let divideBy x =
    match x with
    | 0 -> failwith "zero"
    | _ -> true

// lib.p045
[<Test>]
let ``can test`` () =
    can divideBy 0
    |> should equal false

// lib.p046
[<Test>]
let ``list creation span`` () =
    3--5
    |> should equal [3; 4; 5]

// lib.p047
[<Test>]
let ``list creation span num`` () =
    (num_of_int 3)---(num_of_int 5)
    |> should equal [(num_of_int 3); (num_of_int 4); (num_of_int 5)]

// lib.p048
[<Test>]
let ``List partition`` () =
    List.partition (fun x -> x % 2 = 0) [0; 1; 2; 3; 4]
    |> should equal ([0; 2; 4], [1; 3])

// lib.p049
[<Test>]
let ``List filter`` () =
    List.filter (fun x -> x % 2 = 0) [0; 1; 2; 3; 4]
    |> should equal [0; 2; 4]

// lib.p050
[<Test>]
let ``List length`` () =
    List.length [1; 2; 3]
    |> should equal 3

// lib.p051
[<Test>]
let ``List find`` () =
    List.find (fun x -> x % 2 = 0) [1; 2; 3; 4]
    |> should equal 2

// lib.p052
[<Test>]
let ``List index`` () =
    index 1 [1; 2; 3; 1]
    |> should equal 0

// lib.p053
[<Test>]
let ``List earlier`` () =
    earlier [1; 2; 3] 3 2
    |> should equal false

// lib.p054
[<Test>]
let ``List merge 1`` () =
    merge (<) [3] [1]
    |> should equal [1; 3]

// lib.p055
[<Test>]
let ``List merge 2`` () =
    merge (>) [1] [3]
    |> should equal [3; 1]

// lib.p056
[<Test>]
let ``List mergepairs 1`` () =
    mergepairs (<) [[1;10]; [3;7]; [5;8]] [[2;11]; [4;12]; [6;9]]
    |> should equal [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]

// lib.p057
[<Test>]
let ``List mergepairs 2`` () =
    mergepairs (>) [[10;1]; [7;3]; [8;5]] [[11;2]; [12;4]; [9;6]]
    |> should equal [12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1]

// lib.p058
[<Test>]
let ``List length increasing`` () =
    increasing List.length [1] [1;2;3]
    |> should equal true

// lib.p059
[<Test>]
let ``List length decreasing`` () =
    decreasing List.length [1] [1;2;3]
    |> should equal false

let list1 = [1; 2; 3;]
let list2 = [1; 3; 5;]
// Crate a function that returns failure
let containsEven x =
    match x with
    | _ when  x % 2 = 0 -> true
    | _ -> failwith "not even"

// lib.p060
[<Test>]
let ``tryfind 1`` () =
    try
        tryfind containsEven list1
    with
        | Failure _ -> false
        | _ -> true 
    |> should equal true

// lib.p061
[<Test>]
let ``tryfind 2`` () =
    try
        tryfind containsEven list2
    with
        | Failure _ -> false
        | _ -> true  
    |> should equal false

// lib.p062
[<Test>]
let ``List mapfilter 2`` () =
    mapfilter (fun x -> 
        match x with
        | _ when x % 2 = 0 -> x
        | _ -> failwith "invalid")
        [1; 2; 3; 4]
    |> should equal [2; 4]

// lib.p063
[<Test>]
let ``List maximize`` () =
    maximize (fun x -> x * x) [-4; 1; 2]
    |> should equal -4

// lib.p064
[<Test>]
let ``List minimize`` () =
    minimize (fun x -> x * x) [-4; 1; 2]
    |> should equal 1

// lib.p065
[<Test>]
let ``List setify`` () =
    setify [1; 5; 2; 1; 3; 6; 4; 5]
    |> should equal [1; 2; 3; 4; 5; 6]

// lib.p066
[<Test>]
let ``List union`` () =
    union [1; 2; 3; 5; 6] [2; 4; 5]
    |> should equal [1; 2; 3; 4; 5; 6]

// lib.p067
[<Test>]
let ``List intersect`` () =
    intersect [1; 2; 3; 5; 6] [2; 4; 5]
    |> should equal [2; 5]

// lib.p068
[<Test>]
let ``List substract`` () =
    subtract [1; 2; 3; 5; 6] [2; 4; 5]
    |> should equal [1; 3; 6]

// lib.p069
[<Test>]
let ``List subset 1`` () =
    subset [1; 2; 3; 5; 6] [2; 4; 5]
    |> should equal false

// lib.p070
[<Test>]
let ``List subset 2`` () =
    subset [1; 2; 3; 5; 6] [1; 2; 3; 5; 6]
    |> should equal true

// lib.p071
[<Test>]
let ``List subset 3`` () =
    subset [2; 5] [1; 2; 3; 5; 6]
    |> should equal true

// lib.p072
[<Test>]
let ``List psubset 1`` () =
    psubset [1; 2; 3; 5; 6] [2; 4; 5]
    |> should equal false

// lib.p073
[<Test>]
let ``List psubset 2`` () =
    psubset [1; 2; 3; 5; 6] [1; 2; 3; 5; 6]
    |> should equal false

// lib.p074
[<Test>]
let ``List psubset 3`` () =
    psubset [2; 5] [1; 2; 3; 5; 6]
    |> should equal true

// lib.p075
[<Test>]
let ``List set eq 1`` () =
    set_eq [1; 2; 3; 5; 6] [2; 4; 5]
    |> should equal false

// lib.p076
[<Test>]
let ``List set eq 2`` () =
    set_eq [1; 2; 3; 6; 5] [1; 2; 3; 5; 6]
    |> should equal true

// lib.p077
[<Test>]
let ``List set eq 3`` () =
    set_eq [] []
    |> should equal true

// lib.p078
[<Test>]
let ``List insert`` () =
    insert 3 [1; 2; 4]
    |> should equal [1; 2; 3; 4]

// lib.p079
[<Test>]
let ``List mem 1`` () =
    mem 3 [1; 2; 4]
    |> should equal false

// lib.p080
[<Test>]
let ``List mem 2`` () =
    mem 2 [1; 2; 4]
    |> should equal true

// lib.p081
[<Test>]
let ``Patricia tree empty`` () =
    let patricia_tree_empty = (fpf [] [])
    is_undefined patricia_tree_empty
    |> should equal true

// lib.p082
[<Test>]
let ``Patricia tree one leaf`` () =
    let patricia_tree = (fpf [1] [1])
    patricia_tree
    |> should equal (Leaf (1, [(1,1)]))

// lib.p083
[<Test>]
let ``Patricia tree one branch`` () =
    let patricia_tree = (fpf [1;2] [1;4])
    patricia_tree
    |> should equal (
        Branch (0,1, 
            (Leaf (2, [(2, 4)])),
            (Leaf (1, [(1, 1)])) 
        ))

// lib.p084
[<Test>]
let ``Patricia tree branch with single leaf`` () =
    let patricia_tree = (fpf [1;2;3] [1;4;9])
    patricia_tree
    |> should equal (
        Branch (0,1, 
            (Leaf (2, [(2, 4)])), 
            (Branch (1,2, 
                (Leaf (1, [(1, 1)])), 
                (Leaf (3, [(3, 9)])) 
            ))
        ))
        
// lib.p085
[<Test>]
let ``Patricia tree two branches with two leaves`` () =
    let patricia_tree = (fpf [1;2;3;4] [1;4;9;16])
    patricia_tree
    |> should equal (
        Branch (0,1,
            (Branch (0,2,
                (Leaf (4, [(4, 16)])),
                (Leaf (2, [(2, 4)]))
            )),
            (Branch (1,2,
                (Leaf (1, [(1, 1)])),
                (Leaf (3, [(3, 9)]))
            ))
        ))

// lib.p086
[<Test>]
let ``finite partial function mapf`` () =
    mapf (fun x -> x + 5) smallsqs
    |> should equal (
        Branch (0,1,
            (Leaf (2, [(2, 9)])),
            (Branch (1,2,
                (Leaf (1,[(1, 6)])),
                (Leaf (3,[(3, 14)]))
            ))
        ))

// lib.p087
[<Test>]
let ``finite partial function domain`` () =
    dom smallsqs
    |> should equal [1; 2; 3]

// lib.p088
[<Test>]
let ``finite partial function range`` () =
    ran smallsqs
    |> should equal [1; 4; 9]

// lib.p089
[<Test>]
[<ExpectedException("System.Exception",ExpectedMessage="apply")>]
let ``finite partial function apply exception`` () =
    apply smallsqs 9
    |> should equal ()

// lib.p090
[<Test>]
let ``finite partial function tryapplyd default value`` () =
    tryapplyd smallsqs 9 -1
    |> should equal -1

// lib.p091
[<Test>]
let ``finite partial function tryapplyd`` () =
    tryapplyd smallsqs 3 -1
    |> should equal 9

let words = fpf [1;2;3] [ ["a"]; ["i";"t"]; ["d";"o";"g"] ];;

// lib.p092
[<Test>]
let ``finite partial function tryapplyl 1`` () =
    tryapplyl words 1
    |> should equal ["a"]

// lib.p093
[<Test>]
let ``finite partial function tryapplyl 2`` () =
    tryapplyl words 3
    |> should equal ["d";"o";"g"]

// lib.p094
[<Test>]
let ``finite partial function defined failure`` () =
    defined smallsqs 9
    |> should equal false

// lib.p095
[<Test>]
let ``finite partial function defined success`` () =
    defined smallsqs 3
    |> should equal true

// lib.p096
[<Test>]
let ``finite partial function undefine failure`` () =
    let smallsqs = fpf [1;2;3] [1;4;9]
    undefine 9 smallsqs
    |> should equal (
        Branch (0,1,
            (Leaf (2,[(2, 4)])),
            (Branch (1,2,
                (Leaf (1,[(1, 1)])),
                (Leaf (3,[(3, 9)]))
            ))
        ))

// lib.p097
[<Test>]
let ``finite partial function undefine success`` () =
    let smallsqs = fpf [1;2;3] [1;4;9]
    undefine 3 smallsqs
    |> should equal (
        Branch (0,1,
            (Leaf (2,[(2, 4)])),
            (Leaf (1,[(1, 1)]))
        ))

// lib.p098
[<Test>]
let ``finite partial function update operator`` () =
    let pt = 10 |=> 100
    pt
    |> should equal (Leaf (10 ,[(10, 100)]))

// lib.p099
[<Test>]
let ``finite partial function modifier value`` () =
    valmod 0 1 (fun z -> z + 5) 0
    |> should equal 1

// lib.p100
[<Test>]
let ``finite partial function modifier function`` () =
    valmod 0 1 (fun z -> z + 5) -1
    |> should equal 4

// lib.p101
[<Test>]
[<ExpectedException("System.Exception",ExpectedMessage="undefined function")>]
let ``finite partial function undefined function`` () =
    let y = fun x -> undef x
    printfn "y: %A" (y 1)
    |> should equal ()

let ptn =
    let ptn1 = equate (1,2) unequal
    let ptn2 = equate (1,3) ptn1
    let ptn3 = equate (2,4) ptn2
    let ptn4 = equate (5,6) ptn3
    let ptn5 = equate (5,7) ptn4
    let ptn6 = equate (5,8) ptn5
    let ptn7 = equate (5,9) ptn6
    let ptn8 = equate (10,10) ptn7
    let ptn9 = equate (11,12) ptn8
    let ptn10 = equate (11,13) ptn9
    let ptn11 = equate (11,14) ptn10
    let ptn12 = equate (15,17) ptn11
    ptn12;;

// lib.p102
[<Test>]
let ``Partition canonize`` () =
    List.map (fun x -> canonize ptn x) [-1;0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19]
    |> should equal [-1; 0; 2; 2; 2; 2; 6; 6; 6; 6; 6; 10; 12; 12; 12; 12; 17; 16; 17; 18; 19]

// lib.p103
[<Test>]
let ``Partition equivalent`` () =
    let testValues = 
        seq { 
            for x in -1 .. 18 do
                for y in -1 .. 18 do
                    yield (x,y)
        }
    let mapEq items =
        let (x,y) = items
        let eq = equivalent ptn x y
        (x,y,eq)
    let filterEq items =
        let (x,y,eq) = items
        eq
    let simplifyEq items =
        let (x,y,eq) = items
        (x,y)
    List.map mapEq (Seq.toList testValues)
    |> List.filter filterEq
    |> List.map simplifyEq
    |> should equal [
        (-1, -1); (0, 0); (1, 1); (1, 2); (1, 3); (1, 4); (2, 1); (2, 2);
        (2, 3); (2, 4); (3, 1); (3, 2); (3, 3); (3, 4); (4, 1); (4, 2);
        (4, 3); (4, 4); (5, 5); (5, 6); (5, 7); (5, 8); (5, 9); (6, 5);
        (6, 6); (6, 7); (6, 8); (6, 9); (7, 5); (7, 6); (7, 7); (7, 8);
        (7, 9); (8, 5); (8, 6); (8, 7); (8, 8); (8, 9); (9, 5); (9, 6);
        (9, 7); (9, 8); (9, 9); (10, 10); (11, 11); (11, 12); (11, 13);
        (11, 14); (12, 11); (12, 12); (12, 13); (12, 14); (13, 11); (13, 12);
        (13, 13); (13, 14); (14, 11); (14, 12); (14, 13); (14, 14); (15, 15);
        (15, 17); (16, 16); (17, 15); (17, 17); (18, 18)]

// lib.p103
[<Test>]
let ``Partition equated`` () =
    equated ptn
    |> should equal [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 17]
