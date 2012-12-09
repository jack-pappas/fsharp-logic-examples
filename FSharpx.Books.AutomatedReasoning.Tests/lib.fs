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

// NOTE: In the optimzed version the 
// following lib functions are replaced with
// equivalent F# functions or operators.
// 
// To add evidence that the replacements are sound,
// the original results are tested against the
// F# replacement results. If the results are different
// the test will fail.
//
//  OCaml        F#
//  insert       Set.add
//  intersect    Set.intersect
//  image        Set.map
//  mem          Set.contains
//  psubset      Set.isProperSubset
//  set_eq       =
//  subset       Set.isSubset
//  subtract     Set.diference
//  union        Set.union
//  unions       Set.unionMany

// ===========================================================================

// NOTE: In porting the OCaml to F#, if there was a corresponding built-in F# routine
// that was functionally equivelent, then the F# equivelent was used.

// Following is the list of F# equivelent routines.

// OCaml         F#
// do_list       List.iter
// end_itlist    List.reduceBack
// el            List.nth
// exists        List.exists
// filter        List.filter
// find          List.find
// forall        List.forall
// forall2       List.forall2
// hd            List.head
// index         List.findIndex
// itlist        List.foldBack
// itlist2       List.foldBack2
// length        List.length
// map           List.map
// map2          List.map2
// minimize      List.minBy
// maximize      List.maxBy
// partition     List.partition
// replicate     List.replicate    not replaced. See below.
// rev           List.rev
// tl            List.tail
// unzip         List.unzip
// zip           List.zip
//
// To ensure that each F# routine it equivelent, 
// both the OCaml and F# routine are run against the 
// same test cases and test results in the same test.
// If the results are equivelent, then the F# equivelent 
// is used in the code.
//
// The noteable difference which still allowed the use
// of an F# routine are:
// 1. Different exception type and/or message.
// 2. Different index result when multiple valid answers. i.e. minBy and maxBy
//
// The once case where the differences were signifigant 
// is F# List.replicate.
// When the replicate count is negative
// F# List.replicate will return exception and
// OCaml replicate will return [].
//
// NOTE: replicate is not used in code, so no need to replace replicate with List.replicate.
// replicate is in the original OCaml code but not used. It was ported with the lib module;
// upon further investigation it was found to be dead code.
//
// In order to be able to test against the OCaml version of the code
// that was replaced by an F# equivelent, the F# port of the code 
// is placed here for access by the test functions.

let rec do_list f l =
    match l with
    | []   -> ()
    | h::t -> f(h); do_list f t

let rec end_itlist f l =
    match l with
    | []     -> failwith "end_itlist"
    | [x]    -> x
    | (h::t) -> f h (end_itlist f t)

let rec el n l =
    if n = 0 then List.head l 
    else el (n - 1) (List.tail l)

let rec exists p l =
    match l with
    | [] -> false
    | h::t -> p(h) || exists p t

let rec find p l =
    match l with
    | [] -> failwith "find"
    | (h::t) -> if p(h) then h else find p t

let rec forall p l =
    match l with
    | []   -> true
    | h::t -> p(h) && forall p t

let rec forall2 p l1 l2 =
    match (l1,l2) with
    | [],[] -> true
    | (h1::t1,h2::t2) -> p h1 h2 && forall2 p t1 t2
    | _ -> false

let hd l =
    match l with
    | h::t -> h
    | _ -> failwith "hd"

let index_orig x =
    let rec ind n l =
        match l with
        | []     -> failwith "index"
        | (h::t) -> 
            if compare x h = 0 then n 
            else ind (n + 1) t
    ind 0

let rec itlist f l b =
    match l with
    | []     -> b
    | (h::t) -> f h (itlist f t b)

let rec itlist2 f l1 l2 b =
    match (l1,l2) with
    | ([],[])         -> b
    | (h1::t1,h2::t2) -> f h1 h2 (itlist2 f t1 t2 b)
    | _               -> failwith "itlist2"

let length =
    let rec len k l =
        if l = [] then k else len (k + 1) (List.tail l)
    fun l -> len 0 l

let map f =
    let rec mapf l =
        match l with
        | []     -> []
        | (x::t) -> let y = f x in y::(mapf t)
    mapf

let rec map2 f l1 l2 =
    match (l1,l2) with
    | [],[] -> []
    | (h1::t1),(h2::t2) -> let h = f h1 h2 in h::(map2 f t1 t2)
    | _ -> failwith "map2: length mismatch"

let partition p l =
    itlist (fun a (yes,no) -> if p a then a::yes,no else yes,a::no) l ([],[])
    
let replicate n a = List.map (fun x -> a) (1--n)

let rev =
    let rec rev_append acc l =
        match l with
        | [] -> acc
        | h::t -> rev_append (h::acc) t
    fun l -> rev_append [] l

let tl l =
    match l with
    | h::t -> t
    | _ -> failwith "tl"

let rec unzip l =
    match l with
    | [] -> [],[]
    | (x,y)::t ->
        let xs,ys = unzip t in x::xs,y::ys

let rec zip l1 l2 =
    match (l1,l2) with
    | ([],[])         -> []
    | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
    | _               -> failwith "zip"

let filter p l = fst(partition p l)

// ===========================================================================

// Tests for library functions derived from
// the results shown on Pg. 619-621.

let private butLastValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.butLast.01
        // System.Exception - butlast
        [],
        [] // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.butLast.02
        [1],
        []
    );
    (
        // idx 2
        // lib.butLast.03
        [1; 2],
        [1]
    );
    (
        // idx 3
        // lib.butLast.04
        [1; 2; 3],
        [1; 2]
    );
    |]

[<TestCase(0, TestName = "lib.butLast.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="butlast")>]
[<TestCase(1, TestName = "lib.butLast.02")>]
[<TestCase(2, TestName = "lib.butLast.03")>]
[<TestCase(3, TestName = "lib.butLast.04")>]

[<Test>]
let ``List butlast`` idx = 
    let (list, _) = butLastValues.[idx]
    let (_, result) = butLastValues.[idx]
    butlast list
    |> should equal result

let private chopListValues : (int * int list * (int list * int list))[] = [| 
    (
        // idx 0
        // lib.chopList.01
        0, [],
        ( [], [] )
    );
    (
        // idx 1
        // lib.chopList.02
        // System.Exception - chop_list
        1, [],
        ( [], [] ) // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.chopList.03
        0, [1],
        ( [], [1] )
    );
    (
        // idx 3
        // lib.chopList.04
        1, [1],
        ( [1], [] )
    );
    (
        // idx 4
        // lib.chopList.05
        // System.Exception - chop_list
        2, [1],
        ( [], [] ) // Dummy value used as place holder
    );
    (
        // idx 5
        // lib.chopList.06
        0, [1; 2],
        ( [], [1; 2] )
    );
    (
        // idx 6
        // lib.chopList.07
        1, [1; 2],
        ( [1], [2] )
    );
    (
        // idx 7
        // lib.chopList.08
        2, [1; 2],
        ( [1; 2], [] )
    );
    (
        // idx 8
        // lib.chopList.09
        // System.Exception - chop_list
        3, [1; 2],
        ( [], [] ) // Dummy value used as place holder
    );
    (
        // idx 9
        // lib.chopList.10
        0, [1; 2; 3],
        ( [], [1; 2; 3] )
    );
    (
        // idx 10
        // lib.chopList.11
        1, [1; 2; 3],
        ( [1], [2; 3] )
    );
    (
        // idx 11
        // lib.chopList.12
        2, [1; 2; 3],
        ( [1; 2], [3] )
    );
    (
        // idx 12
        // lib.chopList.13
        3, [1; 2; 3],
        ( [1; 2; 3], [] )
    );
    (
        // idx 13
        // lib.chopList.14
        // System.Exception - chop_list
        4, [1; 2; 3],
        ( [], [] ) // Dummy value used as place holder
    );
    (
        // idx 14
        // lib.chopList.15
        // System.Exception - chop_list
        -1, [],
        ( [], [] ) // Dummy value used as place holder
    );
    (
        // idx 15
        // lib.chopList.16
        // System.Exception - chop_list
        -1, [1],
        ( [], [] ) // Dummy value used as place holder
    );
    (
        // idx 16
        // lib.chopList.17
        // System.Exception - chop_list
        -1, [1; 2],
        ( [], [] ) // Dummy value used as place holder
    );
    |]

[<TestCase(0, TestName = "lib.chopList.01")>]
[<TestCase(1, TestName = "lib.chopList.02", ExpectedException=typeof<System.Exception>, ExpectedMessage="chop_list")>]
[<TestCase(2, TestName = "lib.chopList.03")>]
[<TestCase(3, TestName = "lib.chopList.04")>]
[<TestCase(4, TestName = "lib.chopList.05", ExpectedException=typeof<System.Exception>, ExpectedMessage="chop_list")>]
[<TestCase(5, TestName = "lib.chopList.06")>]
[<TestCase(6, TestName = "lib.chopList.07")>]
[<TestCase(7, TestName = "lib.chopList.08")>]
[<TestCase(8, TestName = "lib.chopList.09", ExpectedException=typeof<System.Exception>, ExpectedMessage="chop_list")>]
[<TestCase(9, TestName = "lib.chopList.10")>]
[<TestCase(10, TestName = "lib.chopList.11")>]
[<TestCase(11, TestName = "lib.chopList.12")>]
[<TestCase(12, TestName = "lib.chopList.13")>]
[<TestCase(13, TestName = "lib.chopList.14", ExpectedException=typeof<System.Exception>, ExpectedMessage="chop_list")>]
[<TestCase(14, TestName = "lib.chopList.15", ExpectedException=typeof<System.Exception>, ExpectedMessage="chop_list")>]
[<TestCase(15, TestName = "lib.chopList.16", ExpectedException=typeof<System.Exception>, ExpectedMessage="chop_list")>]
[<TestCase(16, TestName = "lib.chopList.17", ExpectedException=typeof<System.Exception>, ExpectedMessage="chop_list")>]

[<Test>]
let ``List chop_list`` idx = 
    let (n, _, _) = chopListValues.[idx]
    let (_, list, _) = chopListValues.[idx]
    let (_, _, result) = chopListValues.[idx]
    chop_list n list
    |> should equal result

let private distinctpairsValues : (int list * (int * int) list )[] = [| 
    (
        // idx 0
        // lib.distinctpairs.01
        [],
        []
    );
    (
        // idx 1
        // lib.distinctpairs.02
        [1],
        []
    );
    (
        // idx 2
        // lib.distinctpairs.03
        [1; 2],
        [(1, 2)]
    );
    (
        // idx 3
        // lib.distinctpairs.04
        [1; 2; 3],
        [(1, 2); (1, 3); (2, 3); ]
    );
    (
        // idx 4
        // lib.distinctpairs.05
        [1; 2; 3; 4],
        [(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (3, 4)]
    );
    |]

[<TestCase(0, TestName = "lib.distinctpairs.01")>]
[<TestCase(1, TestName = "lib.distinctpairs.02")>]
[<TestCase(2, TestName = "lib.distinctpairs.03")>]
[<TestCase(3, TestName = "lib.distinctpairs.04")>]
[<TestCase(4, TestName = "lib.distinctpairs.05")>]

[<Test>]
let ``List distinctpairs`` idx = 
    let (list, _) = distinctpairsValues.[idx]
    let (_, result) = distinctpairsValues.[idx]
    distinctpairs list
    |> should equal result

let private earlierValues : (int list * int * int * bool)[] = [| 
    (
        // idx 0
        // lib.earlier.001
        [], -1, -1, 
        false
    );
    (
        // idx 1
        // lib.earlier.002
        [], -1, 0,
        false
    );
    (
        // idx 2
        // lib.earlier.003
        [], -1, 1, 
        false
    );
    (
        // idx 3
        // lib.earlier.004
        [], 0, -1, 
        false
    );
    (
        // idx 4
        // lib.earlier.005
        [], 0, 0,
        false
    );
    (
        // idx 5
        // lib.earlier.006
        [], 0, 1, 
        false
    );
    (
        // idx 6
        // lib.earlier.007
        [], 1, -1, 
        false
    );
    (
        // idx 7
        // lib.earlier.008
        [], 1, 0,
        false
    );
    (
        // idx 8
        // lib.earlier.009
        [], 1, 1, 
        false
    );
    (
        // idx 9
        // lib.earlier.010
        [1], -1, -1, 
        false
    );
    (
        // idx 10
        // lib.earlier.011
        [1], -1, 0,
        false
    );
    (
        // idx 11
        // lib.earlier.012
        [1], -1, 1, 
        false
    );
    (
        // idx 12
        // lib.earlier.013
        [1], 0, -1, 
        false
    );
    (
        // idx 13
        // lib.earlier.014
        [1], 0, 0,
        false
    );
    (
        // idx 14
        // lib.earlier.015
        [1], 0, 1, 
        false
    );
    (
        // idx 15
        // lib.earlier.016
        [1], 1, -1, 
        true
    );
    (
        // idx 16
        // lib.earlier.017
        [1], 1, 0,
        true
    );
    (
        // idx 17
        // lib.earlier.018
        [1], 1, 1, 
        false
    );
    (
        // idx 18
        // lib.earlier.019
        [1; 2], -1, -1, 
        false
    );
    (
        // idx 19
        // lib.earlier.020
        [1; 2], -1, 0,
        false
    );
    (
        // idx 20
        // lib.earlier.021
        [1; 2], -1, 1, 
        false
    );
    (
        // idx 21
        // lib.earlier.022
        [1; 2], -1, 2, 
        false
    );
    (
        // idx 22
        // lib.earlier.023
        [1; 2], -1, 3, 
        false
    );
    (
        // idx 23
        // lib.earlier.024
        [1; 2], 0, -1, 
        false
    );
    (
        // idx 24
        // lib.earlier.025
        [1; 2], 0, 0,
        false
    );
    (
        // idx 25
        // lib.earlier.026
        [1; 2], 0, 1, 
        false
    );
    (
        // idx 26
        // lib.earlier.027
        [1; 2], 0, 2, 
        false
    );
    (
        // idx 27
        // lib.earlier.028
        [1; 2], 0, 3, 
        false
    );
    (
        // idx 28
        // lib.earlier.029
        [1; 2], 1, -1, 
        true
    );
    (
        // idx 29
        // lib.earlier.030
        [1; 2], 1, 0,
        true
    );
    (
        // idx 30
        // lib.earlier.031
        [1; 2], 1, 1, 
        false
    );
    (
        // idx 31
        // lib.earlier.032
        [1; 2], 1, 2, 
        true
    );
    (
        // idx 32
        // lib.earlier.033
        [1; 2], 1, 3, 
        true
    );
    (
        // idx 33
        // lib.earlier.034
        [1; 2], 2, -1, 
        true
    );
    (
        // idx 34
        // lib.earlier.035
        [1; 2], 2, 0,
        true
    );
    (
        // idx 35
        // lib.earlier.036
        [1; 2], 2, 1, 
        false
    );
    (
        // idx 36
        // lib.earlier.037
        [1; 2], 2, 2, 
        false
    );
    (
        // idx 37
        // lib.earlier.038
        [1; 2], 2, 3, 
        true
    );
    (
        // idx 38
        // lib.earlier.039
        [1; 2], 3, -1, 
        false
    );
    (
        // idx 39
        // lib.earlier.040
        [1; 2], 3, 0,
        false
    );
    (
        // idx 40
        // lib.earlier.041
        [1; 2], 3, 1, 
        false
    );
    (
        // idx 41
        // lib.earlier.042
        [1; 2], 3, 2, 
        false
    );
    (
        // idx 42
        // lib.earlier.043
        [1; 2], 3, 3, 
        false
    );

    
    (
        // idx 43
        // lib.earlier.044
        [1; 2; 3], -1, -1,
        false
    );
    (
        // idx 44
        // lib.earlier.045
        [1; 2; 3], -1, 0,
        false
    );
    (
        // idx 45
        // lib.earlier.046
        [1; 2; 3], -1, 1,
        false
    );
    (
        // idx 46
        // lib.earlier.047
        [1; 2; 3], -1, 2,
        false
    );
    (
        // idx 47
        // lib.earlier.048
        [1; 2; 3], -1, 3,
        false
    );
    (
        // idx 48
        // lib.earlier.049
        [1; 2; 3], 0, -1,
        false
    );
    (
        // idx 49
        // lib.earlier.050
        [1; 2; 3], 0, 0,
        false
    );
    (
        // idx 50
        // lib.earlier.051
        [1; 2; 3], 0, 1,
        false
    );
    (
        // idx 51
        // lib.earlier.052
        [1; 2; 3], 0, 2,
        false
    );
    (
        // idx 52
        // lib.earlier.053
        [1; 2; 3], 0, 3,
        false
    );
    (
        // idx 53
        // lib.earlier.054
        [1; 2; 3], 1, -1,
        true
    );
    (
        // idx 54
        // lib.earlier.055
        [1; 2; 3], 1, 0,
        true
    );
    (
        // idx 55
        // lib.earlier.056
        [1; 2; 3], 1, 1,
        false
    );
    (
        // idx 56
        // lib.earlier.057
        [1; 2; 3], 1, 2,
        true
    );
    (
        // idx 57
        // lib.earlier.058
        [1; 2; 3], 1, 3,
        true
    );
    (
        // idx 58
        // lib.earlier.059
        [1; 2; 3], 2, -1,
        true
    );
    (
        // idx 59
        // lib.earlier.060
        [1; 2; 3], 2, 0,
        true
    );
    (
        // idx 60
        // lib.earlier.061
        [1; 2; 3], 2, 1,
        false
    );
    (
        // idx 61
        // lib.earlier.062
        [1; 2; 3], 2, 2,
        false
    );
    (
        // idx 62
        // lib.earlier.063
        [1; 2; 3], 2, 3,
        true
    );
    (
        // idx 63
        // lib.earlier.064
        [1; 2; 3], 3, -1,
        true
    );
    (
        // idx 64
        // lib.earlier.065
        [1; 2; 3], 3, 0,
        true
    );
    (
        // idx 65
        // lib.earlier.066
        [1; 2; 3], 3, 1,
        false
    );
    (
        // idx 66
        // lib.earlier.067
        [1; 2; 3], 3, 2,
        false
    );
    (
        // idx 67
        // lib.earlier.068
        [1; 2; 3], 3, 3,
        false
    );
    (
        // idx 68
        // lib.earlier.069
        [1; 2; 3; 4], -1, -1,
        false
    );
    (
        // idx 69
        // lib.earlier.070
        [1; 2; 3; 4], -1, 0,
        false
    );
    (
        // idx 70
        // lib.earlier.071
        [1; 2; 3; 4], -1, 1,
        false
    );
    (
        // idx 71
        // lib.earlier.072
        [1; 2; 3; 4], -1, 2,
        false
    );
    (
        // idx 72
        // lib.earlier.073
        [1; 2; 3; 4], -1, 3,
        false
    );
    (
        // idx 73
        // lib.earlier.074
        [1; 2; 3; 4], -1, 4,
        false
    );
    (
        // idx 74
        // lib.earlier.075
        [1; 2; 3; 4], 0, -1,
        false
    );
    (
        // idx 75
        // lib.earlier.076
        [1; 2; 3; 4], 0, 0,
        false
    );
    (
        // idx 76
        // lib.earlier.077
        [1; 2; 3; 4], 0, 1,
        false
    );
    (
        // idx 77
        // lib.earlier.078
        [1; 2; 3; 4], 0, 2,
        false
    );
    (
        // idx 78
        // lib.earlier.079
        [1; 2; 3; 4], 0, 3,
        false
    );
    (
        // idx 79
        // lib.earlier.080
        [1; 2; 3; 4], 0, 4,
        false
    );
    (
        // idx 80
        // lib.earlier.081
        [1; 2; 3; 4], 1, -1,
        true
    );
    (
        // idx 81
        // lib.earlier.082
        [1; 2; 3; 4], 1, 0,
        true
    );
    (
        // idx 82
        // lib.earlier.083
        [1; 2; 3; 4], 1, 1,
        false
    );
    (
        // idx 83
        // lib.earlier.084
        [1; 2; 3; 4], 1, 2,
        true
    );
    (
        // idx 84
        // lib.earlier.085
        [1; 2; 3; 4], 1, 3,
        true
    );
    (
        // idx 85
        // lib.earlier.086
        [1; 2; 3; 4], 1, 4,
        true
    );
    (
        // idx 86
        // lib.earlier.087
        [1; 2; 3; 4], 2, -1,
        true
    );
    (
        // idx 87
        // lib.earlier.088
        [1; 2; 3; 4], 2, 0,
        true
    );
    (
        // idx 88
        // lib.earlier.089
        [1; 2; 3; 4], 2, 1,
        false
    );
    (
        // idx 89
        // lib.earlier.090
        [1; 2; 3; 4], 2, 2,
        false
    );
    (
        // idx 90
        // lib.earlier.091
        [1; 2; 3; 4], 2, 3,
        true
    );
    (
        // idx 91
        // lib.earlier.092
        [1; 2; 3; 4], 2, 4,
        true
    );
    (
        // idx 92
        // lib.earlier.093
        [1; 2; 3; 4], 3, -1,
        true
    );
    (
        // idx 93
        // lib.earlier.094
        [1; 2; 3; 4], 3, 0,
        true
    );
    (
        // idx 94
        // lib.earlier.095
        [1; 2; 3; 4], 3, 1,
        false
    );
    (
        // idx 95
        // lib.earlier.096
        [1; 2; 3; 4], 3, 2,
        false
    );
    (
        // idx 96
        // lib.earlier.097
        [1; 2; 3; 4], 3, 3,
        false
    );
    (
        // idx 97
        // lib.earlier.098
        [1; 2; 3; 4], 3, 4,
        true
    );
    (
        // idx 98
        // lib.earlier.099
        [1; 2; 3; 4], 4, -1,
        true
    );
    (
        // idx 99
        // lib.earlier.100
        [1; 2; 3; 4], 4, 0,
        true
    );
    (
        // idx 100
        // lib.earlier.101
        [1; 2; 3; 4], 4, 1,
        false
    );
    (
        // idx 101
        // lib.earlier.102
        [1; 2; 3; 4], 4, 2,
        false
    );
    (
        // idx 102
        // lib.earlier.103
        [1; 2; 3; 4], 4, 3,
        false
    );
    (
        // idx 103
        // lib.earlier.104
        [1; 2; 3; 4], 4, 4,
        false
    );
    |]

[<TestCase(0, TestName = "lib.earlier.001")>]
[<TestCase(1, TestName = "lib.earlier.002")>]
[<TestCase(2, TestName = "lib.earlier.003")>]
[<TestCase(3, TestName = "lib.earlier.004")>]
[<TestCase(4, TestName = "lib.earlier.005")>]
[<TestCase(5, TestName = "lib.earlier.006")>]
[<TestCase(6, TestName = "lib.earlier.007")>]
[<TestCase(7, TestName = "lib.earlier.008")>]
[<TestCase(8, TestName = "lib.earlier.009")>]
[<TestCase(9, TestName = "lib.earlier.010")>]
[<TestCase(10, TestName = "lib.earlier.011")>]
[<TestCase(11, TestName = "lib.earlier.012")>]
[<TestCase(12, TestName = "lib.earlier.013")>]
[<TestCase(13, TestName = "lib.earlier.014")>]
[<TestCase(14, TestName = "lib.earlier.015")>]
[<TestCase(15, TestName = "lib.earlier.016")>]
[<TestCase(16, TestName = "lib.earlier.017")>]
[<TestCase(17, TestName = "lib.earlier.018")>]
[<TestCase(18, TestName = "lib.earlier.019")>]
[<TestCase(19, TestName = "lib.earlier.020")>]
[<TestCase(20, TestName = "lib.earlier.021")>]
[<TestCase(21, TestName = "lib.earlier.022")>]
[<TestCase(22, TestName = "lib.earlier.023")>]
[<TestCase(23, TestName = "lib.earlier.024")>]
[<TestCase(24, TestName = "lib.earlier.025")>]
[<TestCase(25, TestName = "lib.earlier.026")>]
[<TestCase(26, TestName = "lib.earlier.027")>]
[<TestCase(27, TestName = "lib.earlier.028")>]
[<TestCase(28, TestName = "lib.earlier.029")>]
[<TestCase(29, TestName = "lib.earlier.030")>]
[<TestCase(30, TestName = "lib.earlier.031")>]
[<TestCase(31, TestName = "lib.earlier.032")>]
[<TestCase(32, TestName = "lib.earlier.033")>]
[<TestCase(33, TestName = "lib.earlier.034")>]
[<TestCase(34, TestName = "lib.earlier.035")>]
[<TestCase(35, TestName = "lib.earlier.036")>]
[<TestCase(36, TestName = "lib.earlier.037")>]
[<TestCase(37, TestName = "lib.earlier.038")>]
[<TestCase(38, TestName = "lib.earlier.039")>]
[<TestCase(39, TestName = "lib.earlier.040")>]
[<TestCase(40, TestName = "lib.earlier.041")>]
[<TestCase(41, TestName = "lib.earlier.042")>]
[<TestCase(42, TestName = "lib.earlier.043")>]
[<TestCase(43, TestName = "lib.earlier.044")>]
[<TestCase(44, TestName = "lib.earlier.045")>]
[<TestCase(45, TestName = "lib.earlier.046")>]
[<TestCase(46, TestName = "lib.earlier.047")>]
[<TestCase(47, TestName = "lib.earlier.048")>]
[<TestCase(48, TestName = "lib.earlier.049")>]
[<TestCase(49, TestName = "lib.earlier.050")>]
[<TestCase(50, TestName = "lib.earlier.051")>]
[<TestCase(51, TestName = "lib.earlier.052")>]
[<TestCase(52, TestName = "lib.earlier.053")>]
[<TestCase(53, TestName = "lib.earlier.054")>]
[<TestCase(54, TestName = "lib.earlier.055")>]
[<TestCase(55, TestName = "lib.earlier.056")>]
[<TestCase(56, TestName = "lib.earlier.057")>]
[<TestCase(57, TestName = "lib.earlier.058")>]
[<TestCase(58, TestName = "lib.earlier.059")>]
[<TestCase(59, TestName = "lib.earlier.060")>]
[<TestCase(60, TestName = "lib.earlier.061")>]
[<TestCase(61, TestName = "lib.earlier.062")>]
[<TestCase(62, TestName = "lib.earlier.063")>]
[<TestCase(63, TestName = "lib.earlier.064")>]
[<TestCase(64, TestName = "lib.earlier.065")>]
[<TestCase(65, TestName = "lib.earlier.066")>]
[<TestCase(66, TestName = "lib.earlier.067")>]
[<TestCase(67, TestName = "lib.earlier.068")>]
[<TestCase(68, TestName = "lib.earlier.069")>]
[<TestCase(69, TestName = "lib.earlier.070")>]
[<TestCase(70, TestName = "lib.earlier.071")>]
[<TestCase(71, TestName = "lib.earlier.072")>]
[<TestCase(72, TestName = "lib.earlier.073")>]
[<TestCase(73, TestName = "lib.earlier.074")>]
[<TestCase(74, TestName = "lib.earlier.075")>]
[<TestCase(75, TestName = "lib.earlier.076")>]
[<TestCase(76, TestName = "lib.earlier.077")>]
[<TestCase(77, TestName = "lib.earlier.078")>]
[<TestCase(78, TestName = "lib.earlier.079")>]
[<TestCase(79, TestName = "lib.earlier.080")>]
[<TestCase(80, TestName = "lib.earlier.081")>]
[<TestCase(81, TestName = "lib.earlier.082")>]
[<TestCase(82, TestName = "lib.earlier.083")>]
[<TestCase(83, TestName = "lib.earlier.084")>]
[<TestCase(84, TestName = "lib.earlier.085")>]
[<TestCase(85, TestName = "lib.earlier.086")>]
[<TestCase(86, TestName = "lib.earlier.087")>]
[<TestCase(87, TestName = "lib.earlier.088")>]
[<TestCase(88, TestName = "lib.earlier.089")>]
[<TestCase(89, TestName = "lib.earlier.090")>]
[<TestCase(90, TestName = "lib.earlier.091")>]
[<TestCase(91, TestName = "lib.earlier.092")>]
[<TestCase(92, TestName = "lib.earlier.093")>]
[<TestCase(93, TestName = "lib.earlier.094")>]
[<TestCase(94, TestName = "lib.earlier.095")>]
[<TestCase(95, TestName = "lib.earlier.096")>]
[<TestCase(96, TestName = "lib.earlier.097")>]
[<TestCase(97, TestName = "lib.earlier.098")>]
[<TestCase(98, TestName = "lib.earlier.099")>]
[<TestCase(99, TestName = "lib.earlier.100")>]
[<TestCase(100, TestName = "lib.earlier.101")>]
[<TestCase(101, TestName = "lib.earlier.102")>]
[<TestCase(102, TestName = "lib.earlier.103")>]
[<TestCase(103, TestName = "lib.earlier.104")>]

[<Test>]
let ``List earlier`` idx = 
    let (list, _, _, _) = earlierValues.[idx]
    let (_, x, _, _) = earlierValues.[idx]
    let (_, _, y, _) = earlierValues.[idx]
    let (_, _, _, result) = earlierValues.[idx]
    earlier list x y
    |> should equal result

let private existsValues : (int list * bool)[] = [| 
    (
        // idx 0
        // lib.exists.001
        [],
        false
    ); 
    (
        // idx 1
        // lib.exists.002
        [-2],
        true
    );
    (
        // idx 2
        // lib.exists.003
        [-1],
        false
    );
    (
        // idx 3
        // lib.exists.004
        [0],
        true
    );
    (
        // idx 4
        // lib.exists.005
        [1],
        false
    );
    (
        // idx 5
        // lib.exists.006
        [1; 2],
        true
    );
    (
        // idx 6
        // lib.exists.007
        [1; 3],
        false
    );
    (
        // idx 7
        // lib.exists.008
        [2; 3],
        true
    );
    (
        // idx 8
        // lib.exists.009
        [1; 2; 3],
        true
    );
    (
        // idx 9
        // lib.exists.010
        [2; 3; 4],
        true
    );
    |]

[<TestCase(0, TestName = "lib.exists.01")>]
[<TestCase(1, TestName = "lib.exists.02")>]
[<TestCase(2, TestName = "lib.exists.03")>]
[<TestCase(3, TestName = "lib.exists.04")>]
[<TestCase(4, TestName = "lib.exists.05")>]
[<TestCase(5, TestName = "lib.exists.06")>]
[<TestCase(6, TestName = "lib.exists.07")>]
[<TestCase(7, TestName = "lib.exists.08")>]
[<TestCase(8, TestName = "lib.exists.09")>]
[<TestCase(9, TestName = "lib.exists.10")>]

[<Test>]
let ``List exists`` idx = 
    let (list, _) = existsValues.[idx]
    let (_, result) = existsValues.[idx]
    List.exists (fun x -> x % 2 = 0) list 
    |> should equal result
    exists (fun x -> x % 2 = 0) list 
    |> should equal result

let private filterValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.filter.001
        [],
        []
    ); 
    (
        // idx 1
        // lib.filter.002
        [-2],
        [-2]
    );
    (
        // idx 2
        // lib.filter.003
        [-1],
        []
    );
    (
        // idx 3
        // lib.filter.004
        [0],
        [0]
    );
    (
        // idx 4
        // lib.filter.005
        [1],
        []
    );
    (
        // idx 5
        // lib.filter.006
        [1; 2],
        [2]
    );
    (
        // idx 6
        // lib.filter.007
        [1; 3],
        []
    );
    (
        // idx 7
        // lib.filter.008
        [2; 3],
        [2]
    );
    (
        // idx 8
        // lib.filter.009
        [1; 2; 3],
        [2]
    );
    (
        // idx 9
        // lib.filter.010
        [2; 3; 4],
        [2; 4]
    );
    |]

[<TestCase(0, TestName = "lib.filter.01")>]
[<TestCase(1, TestName = "lib.filter.02")>]
[<TestCase(2, TestName = "lib.filter.03")>]
[<TestCase(3, TestName = "lib.filter.04")>]
[<TestCase(4, TestName = "lib.filter.05")>]
[<TestCase(5, TestName = "lib.filter.06")>]
[<TestCase(6, TestName = "lib.filter.07")>]
[<TestCase(7, TestName = "lib.filter.08")>]
[<TestCase(8, TestName = "lib.filter.09")>]
[<TestCase(9, TestName = "lib.filter.10")>]
    
[<Test>]
let ``List filter`` idx = 
    let (list, _) = filterValues.[idx]
    let (_, result) = filterValues.[idx]
    List.filter (fun x -> x % 2 = 0) list 
    |> should equal result
    filter (fun x -> x % 2 = 0) list 
    |> should equal result

let private findValues : (int list * int)[] = [| 
    (
        // idx 0
        // lib.find.001
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        [],
        -99  // Dummy value used as place holder
    ); 
    (
        // idx 1
        // lib.find.002
        [-2],
        -2
    );
    (
        // idx 2
        // lib.find.003
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        [-1],
        -99  // Dummy value used as place holder
    );
    (
        // idx 3
        // lib.find.004
        [0],
        0
    );
    (
        // idx 4
        // lib.find.005
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        [1],
        -99  // Dummy value used as place holder
    );
    (
        // idx 5
        // lib.find.006
        [1; 2],
        2
    );
    (
        // idx 6
        // lib.find.007
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        [1; 3],
        -99  // Dummy value used as place holder
    );
    (
        // idx 7
        // lib.find.008
        [2; 3],
        2
    );
    (
        // idx 8
        // lib.find.009
        [1; 2; 3],
        2
    );
    (
        // idx 9
        // lib.find.010
        [2; 3; 4],
        2
    );
    |]

[<TestCase(0, TestName = "lib.find.01", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(1, TestName = "lib.find.02")>]
[<TestCase(2, TestName = "lib.find.03", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(3, TestName = "lib.find.04")>]
[<TestCase(4, TestName = "lib.find.05", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(5, TestName = "lib.find.06")>]
[<TestCase(6, TestName = "lib.find.07", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(7, TestName = "lib.find.08")>]
[<TestCase(8, TestName = "lib.find.09")>]
[<TestCase(9, TestName = "lib.find.10")>]
   
[<Test>]
let ``List find`` idx = 
    let (list, _) = findValues.[idx]
    let (_, result) = findValues.[idx]
    List.find (fun x -> x % 2 = 0) list 
    |> should equal result
    find (fun x -> x % 2 = 0) list 
    |> should equal result

// This Test is to show that they both return
// the different exceptions when given an item not in the list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// find exception test case.

[<TestCase(0, TestName = "lib.findException.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]
[<TestCase(2, TestName = "lib.findException.02", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]
[<TestCase(4, TestName = "lib.findException.03", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]
[<TestCase(6, TestName = "lib.findException.04", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]

[<Test>]
let ``List find exception`` idx = 
    let (list, _) = findValues.[idx]
    let (_, result) = findValues.[idx]
    find (fun x -> x % 2 = 0) list 
    |> should equal result

let private foldBackValues : (int list * int * int)[] = [| 
    (
        // idx 0
        // lib.foldBack.001
        [], 10,
        10
    ); 
    (
        // idx 1
        // lib.foldBack.002
        [-2], 10,
        8
    );
    (
        // idx 2
        // lib.foldBack.003
        [-1], 10,
        9
    );
    (
        // idx 3
        // lib.foldBack.004
        [0], 10,
        10
    );
    (
        // idx 4
        // lib.foldBack.005
        [1], 10,
        11
    );
    (
        // idx 5
        // lib.foldBack.006
        [1; 2], 10,
        13
    );
    (
        // idx 6
        // lib.foldBack.007
        [1; 3], 10,
        14
    );
    (
        // idx 7
        // lib.foldBack.008
        [2; 3], 10,
        15
    );
    (
        // idx 8
        // lib.foldBack.009
        [1; 2; 3], 10,
        16
    );
    (
        // idx 9
        // lib.foldBack.010
        [2; 3; 4], 10,
        19
    );
    |]

[<TestCase(0, TestName = "lib.foldBack.01")>]
[<TestCase(1, TestName = "lib.foldBack.02")>]
[<TestCase(2, TestName = "lib.foldBack.03")>]
[<TestCase(3, TestName = "lib.foldBack.04")>]
[<TestCase(4, TestName = "lib.foldBack.05")>]
[<TestCase(5, TestName = "lib.foldBack.06")>]
[<TestCase(6, TestName = "lib.foldBack.07")>]
[<TestCase(7, TestName = "lib.foldBack.08")>]
[<TestCase(8, TestName = "lib.foldBack.09")>]
[<TestCase(9, TestName = "lib.foldBack.10")>]
  
[<Test>]
let ``List foldBack`` idx = 
    let (list, _, _) = foldBackValues.[idx]
    let (_, start_value, _) = foldBackValues.[idx]
    let (_, _, result) = foldBackValues.[idx]
    List.foldBack (fun acc elem -> acc + elem) list start_value
    |> should equal result
    itlist (fun acc elem -> acc + elem) list start_value
    |> should equal result

let private foldBack2Values : (int list * int list * int * int)[] = [| 
    (
        // idx 0
        // lib.foldBack2.001
        [], [], 10,
        10
    ); 
    (
        // idx 1
        // lib.foldBack2.002
        // System.ArgumentException - The lists had different lengths.
        [1], [], 10,
        -99  // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.foldBack2.003
        // System.ArgumentException - The lists had different lengths.
        [], [1], 10,
        -99  // Dummy value used as place holder
    );
    (
        // idx 3
        // lib.foldBack2.004
        [0], [0], 10,
        10
    );
    (
        // idx 4
        // lib.foldBack2.005
        [-2], [2], 10,
        6
    );
    (
        // idx 5
        // lib.foldBack2.006
        [2], [3], 10,
        16
    );
    (
        // idx 6
        // lib.foldBack2.007
        [1; 2], [4; 5], 10,
        24
    );
    (
        // idx 7
        // lib.foldBack2.008
        [1; 2; 4], [0; -1; 3], 10,
        20
    );
    (
        // idx 8
        // lib.foldBack2.009
        [1; 3; 4; 7], [0; 0; 0; 0], 10,
        10
    );
    |]

[<TestCase(0, TestName = "lib.foldBack2.01")>]
[<TestCase(1, TestName = "lib.foldBack2.02", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(2, TestName = "lib.foldBack2.03", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(3, TestName = "lib.foldBack2.04")>]
[<TestCase(4, TestName = "lib.foldBack2.05")>]
[<TestCase(5, TestName = "lib.foldBack2.06")>]
[<TestCase(6, TestName = "lib.foldBack2.07")>]
[<TestCase(7, TestName = "lib.foldBack2.08")>]
[<TestCase(8, TestName = "lib.foldBack2.09")>]

[<Test>]
let ``List foldBack2`` idx = 
    let (list1, _, _, _) = foldBack2Values.[idx]
    let (_, list2, _, _) = foldBack2Values.[idx]
    let (_, _, start_value, _) = foldBack2Values.[idx]
    let (_, _, _, result) = foldBack2Values.[idx]
    List.foldBack2 (fun elem1 elem2 acc -> elem1 * elem2 + acc) list1 list2 start_value
    |> should equal result
    itlist2 (fun elem1 elem2 acc -> elem1 * elem2 + acc) list1 list2 start_value
    |> should equal result

// This Test is to show that they both return
// different exceptions when the list have different lengths.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// itlist2 exception test case.
    
[<TestCase(1, TestName = "lib.itlistExcpetion.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="itlist2")>]
[<TestCase(2, TestName = "lib.itlistExcpetion.02", ExpectedException=typeof<System.Exception>, ExpectedMessage="itlist2")>]

[<Test>]
let ``List itlist2 exception`` idx = 
    let (list1, _, _, _) = foldBack2Values.[idx]
    let (_, list2, _, _) = foldBack2Values.[idx]
    let (_, _, start_value, _) = foldBack2Values.[idx]
    let (_, _, _, result) = foldBack2Values.[idx]
    itlist2 (fun elem1 elem2 acc -> elem1 * elem2 + acc) list1 list2 start_value
    |> should equal result

let private forallValues : (int list * bool)[] = [| 
    (
        // idx 0
        // lib.forall.001
        [],
        true
    ); 
    (
        // idx 1
        // lib.forall.002
        [-2],
        true
    );
    (
        // idx 2
        // lib.forall.003
        [-1],
        false
    );
    (
        // idx 3
        // lib.forall.004
        [0],
        true
    );
    (
        // idx 4
        // lib.forall.005
        [1],
        false
    );
    (
        // idx 5
        // lib.forall.006
        [2],
        true
    );
    (
        // idx 6
        // lib.forall.007
        [0; 0],
        true
    );
    (
        // idx 7
        // lib.forall.008
        [0; 1],
        false
    );
    (
        // idx 8
        // lib.forall.009
        [1; 0], 
        false
    );
    (
        // idx 9
        // lib.forall.010
        [1; 3],
        false
    );
    (
        // idx 10
        // lib.forall.011
        [2; 4],
        true
    );
    (
        // idx 11
        // lib.forall.012
        [1; 2; 3],
        false
    );
    (
        // idx 12
        // lib.forall.013
        [2; 3; 4],
        false
    );
    (
        // idx 13
        // lib.forall.014
        [1; 1; 1],
        false
    );
    (
        // idx 14
        // lib.forall.015
        [2; 2; 2],
        true
    );
    |]

[<TestCase(0, TestName = "lib.forall.01")>]
[<TestCase(1, TestName = "lib.forall.02")>]
[<TestCase(2, TestName = "lib.forall.03")>]
[<TestCase(3, TestName = "lib.forall.04")>]
[<TestCase(4, TestName = "lib.forall.05")>]
[<TestCase(5, TestName = "lib.forall.06")>]
[<TestCase(6, TestName = "lib.forall.07")>]
[<TestCase(7, TestName = "lib.forall.08")>]
[<TestCase(8, TestName = "lib.forall.09")>]
[<TestCase(9, TestName = "lib.forall.10")>]
[<TestCase(10, TestName = "lib.forall.11")>]
[<TestCase(12, TestName = "lib.forall.12")>]
[<TestCase(13, TestName = "lib.forall.13")>]
[<TestCase(14, TestName = "lib.forall.14")>]

[<Test>]
let ``List forall`` idx = 
    let (list, _) = forallValues.[idx]
    let (_, result) = forallValues.[idx]
    List.forall (fun x -> x % 2 = 0) list 
    |> should equal result
    forall (fun x -> x % 2 = 0) list 
    |> should equal result

let private forall2Values : (int list * int list * bool)[] = [| 
    (
        // idx 0
        // lib.forall2.001
        [], [],
        true
    ); 
    (
        // idx 1
        // lib.forall2.002
        // System.ArgumentException - The lists had different lengths.
        [1], [],
        false  // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.forall2.003
        // System.ArgumentException - The lists had different lengths.
        [], [1],
        false  // Dummy value used as place holder
    );
    (
        // idx 3
        // lib.forall2.004
        [0], [0],
        false
    );
    (
        // idx 4
        // lib.forall2.005
        [0], [1],
        true
    );
    (
        // idx 5
        // lib.forall2.006
        [1], [0],
        false
    );
    (
        // idx 6
        // lib.forall2.007
        // System.ArgumentException - The lists had different lengths.
        [0; 0], [],
        false  // Dummy value used as place holder
    );
    (
        // idx 7
        // lib.forall2.008
        // System.ArgumentException - The lists had different lengths.
        [], [0; 0],
         false  // Dummy value used as place holder
    );
    (
        // idx 8
        // lib.forall2.009
        [0; 0], [0; 0],
        false
    );
    (
        // idx 9
        // lib.forall2.010
        [0; 0], [0; 1],
        false
    );
    (
        // idx 10
        // lib.forall2.011
        [0; 0], [1; 0],
        false
    );
    (
        // idx 11
        // lib.forall2.012
        [0; 0], [1; 1],
        true
    );
    (
        // idx 12
        // lib.forall2.013
        [0; 1], [0; 0],
        false
    );
    (
        // idx 13
        // lib.forall2.014
        [0; 1], [0; 1],
        false
    );
    (
        // idx 14
        // lib.forall2.015
        [0; 1], [1; 0],
        false
    );
    (
        // idx 15
        // lib.forall2.016
        [0; 1], [1; 1],
        false
    );
    (
        // idx 16
        // lib.forall2.0017
        [1; 0], [0; 0],
        false
    );
    (
        // idx 17
        // lib.forall2.0018
        [1; 0], [0; 1],
        false
    );
    (
        // idx 18
        // lib.forall2.019
        [1; 0], [1; 0],
        false
    );
    (
        // idx 19
        // lib.forall2.020
        [1; 0], [1; 1],
        false
    );
    (
        // idx 20
        // lib.forall2.021
        [1; 1], [0; 0],
        false
    );
    (
        // idx 21
        // lib.forall2.022
        [1; 1], [0; 1],
        false
    );
    (
        // idx 22
        // lib.forall2.023
        [1; 1], [1; 0],
        false
    );
    (
        // idx 23
        // lib.forall2.024
        [1; 1], [1; 1],
        false
    );
    |]

[<TestCase(0, TestName = "lib.forall2.01")>]
[<TestCase(1, TestName = "lib.forall2.02", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(2, TestName = "lib.forall2.03", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(3, TestName = "lib.forall2.04")>]
[<TestCase(4, TestName = "lib.forall2.05")>]
[<TestCase(5, TestName = "lib.forall2.06")>]
[<TestCase(6, TestName = "lib.forall2.07", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(7, TestName = "lib.forall2.08", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(8, TestName = "lib.forall2.09")>]
[<TestCase(9, TestName = "lib.forall2.10")>]
[<TestCase(10, TestName = "lib.forall2.11")>]
[<TestCase(11, TestName = "lib.forall2.12")>]
[<TestCase(12, TestName = "lib.forall2.13")>]
[<TestCase(13, TestName = "lib.forall2.14")>]
[<TestCase(14, TestName = "lib.forall2.15")>]
[<TestCase(15, TestName = "lib.forall2.16")>]
[<TestCase(16, TestName = "lib.forall2.17")>]
[<TestCase(17, TestName = "lib.forall2.18")>]
[<TestCase(18, TestName = "lib.forall2.19")>]
[<TestCase(19, TestName = "lib.forall2.20")>]
[<TestCase(20, TestName = "lib.forall2.21")>]
[<TestCase(21, TestName = "lib.forall2.22")>]
[<TestCase(22, TestName = "lib.forall2.23")>]
[<TestCase(23, TestName = "lib.forall2.24")>]

[<Test>]
let ``List forall2`` idx = 
    let (list1, _, _) = forall2Values.[idx]
    let (_, list2, _) = forall2Values.[idx]
    let (_, _, result) = forall2Values.[idx]
    List.forall2 (fun elem1 elem2 -> (elem1 < elem2)) list1 list2
    |> should equal result
    forall2 (fun elem1 elem2 -> (elem1 < elem2)) list1 list2
    |> should equal result

let private headValues : (int list * int)[] = [| 
    (
        // idx 0
        // lib.head.01
        // System.ArgumentException - The input list was empty.
        [],
        -99  // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.head.02
        [1],
        1
    );
    (
        // idx 2
        // lib.head.03
        [1; 2],
        1
    );
    (
        // idx 3
        // lib.head.04
        [1; 2; 3],
        1
    );
    (
        // idx 4
        // lib.head.05
        [3; 2; 1],
        3
    )
    |]

[<TestCase(0, TestName = "lib.head.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.head.02")>]
[<TestCase(2, TestName = "lib.head.03")>]
[<TestCase(3, TestName = "lib.head.04")>]
[<TestCase(4, TestName = "lib.head.05")>]

[<Test>]
let ``List head`` idx = 
    let (list, _) = headValues.[idx]
    let (_, result) = headValues.[idx]
    List.head list
    |> should equal result
    hd list 
    |> should equal result

// This Test is to show that they both return
// different exceptions when given an empty list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// hd exception test case.

[<TestCase(0, TestName = "lib.hdException.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="hd")>]

[<Test>]
let ``List hd exception`` idx = 
    let (list, _) = headValues.[idx]
    let (_, result) = headValues.[idx]
    hd list 
    |> should equal result

let private imageValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.image.001
        [],
        []
    ); 
    (
        // idx 1
        // lib.image.002
        [-2],
        [0]
    );
    (
        // idx 2
        // lib.image.003
        [-1],
        [-1]
    );
    (
        // idx 3
        // lib.image.004
        [0],
        [0]
    );
    (
        // idx 4
        // lib.image.005
        [1],
        [1]
    );
    (
        // idx 5
        // lib.image.006
        [2],
        [0]
    );
    (
        // idx 6
        // lib.image.007
        [-5; -3; -1],
        [-1]
    );
    (
        // idx 7
        // lib.image.008
        [-9; -7;-5; -3; -1],
        [-1]
    );
    (
        // idx 8
        // lib.image.009
        [-2; 2], 
        [0]
    );
    (
        // idx 9
        // lib.image.010
        [-6; -4; -2; 2; 4; 6], 
        [0]
    );
    (
        // idx 10
        // lib.image.011
        [1; 3; 5],
        [1]
    );
    (
        // idx 11
        // lib.image.012
        [1; 3; 5; 7; 9],
        [1]
    );
    (
        // idx 12
        // lib.image.013
        [0; 1],
        [0; 1]
    );
    (
        // idx 13
        // lib.image.014
        [0; 1; 2],
        [0; 1]
    );
    (
        // idx 14
        // lib.image.015
        [-1; 0],
        [-1; 0]
    );
    (
        // idx 15
        // lib.image.016
        [-2; -1; 0],
        [-1; 0]
    );
    (
        // idx 16
        // lib.image.017
        [-10; -9; -8; -7; -6; -5; -4; -3; -2; -1; 0; 1; 2; 2; 4; 5; 6; 7; 8; 8; 10],
        [-1; 0; 1]
    );
    |]

[<TestCase(0, TestName = "lib.image.01")>]
[<TestCase(1, TestName = "lib.image.02")>]
[<TestCase(2, TestName = "lib.image.03")>]
[<TestCase(3, TestName = "lib.image.04")>]
[<TestCase(4, TestName = "lib.image.05")>]
[<TestCase(5, TestName = "lib.image.06")>]
[<TestCase(6, TestName = "lib.image.07")>]
[<TestCase(7, TestName = "lib.image.08")>]
[<TestCase(8, TestName = "lib.image.09")>]
[<TestCase(9, TestName = "lib.image.10")>]
[<TestCase(10, TestName = "lib.image.11")>]
[<TestCase(11, TestName = "lib.image.12")>]
[<TestCase(12, TestName = "lib.image.13")>]
[<TestCase(13, TestName = "lib.image.14")>]
[<TestCase(14, TestName = "lib.image.15")>]
[<TestCase(15, TestName = "lib.image.16")>]
[<TestCase(16, TestName = "lib.image.17")>]

[<Test>]
let ``List image`` idx = 
    let (list, _) = imageValues.[idx]
    let (_, result) = imageValues.[idx]
    image (fun x -> x % 2) list
    |> should equal result
    Set.map (fun x -> x % 2) (Set.ofList list)
    |> should equal (Set.ofList result)
    
let private indexValues : (int * int list * int)[] = [| 
    (
        // idx 0
        // lib.index.01
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        0, [],
        -99  // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.index.02
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        1, [],
        -99  // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.index.03
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        0, [1],
        -99  // Dummy value used as place holder
    );
    (
        // idx 3
        // lib.index.04
        1, [1],
        0
    );
    (
        // idx 4
        // lib.index.05
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        2, [1],
        -99  // Dummy value used as place holder
    );
    (
        // idx 5
        // lib.index.06
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        0, [1; 2],
        -99  // Dummy value used as place holder
    );
    (
        // idx 6
        // lib.index.07
        1, [1; 2],
        0
    );
    (
        // idx 7
        // lib.index.08
        2, [1; 2],
        1
    );
    (
        // idx 8
        // lib.index.09
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        3, [1; 2],
        -99  // Dummy value used as place holder
    );
    (
        // idx 9
        // lib.index.10
        1, [1; 1; 1],
        0
    );
    (
        // idx 10
        // lib.index.11
        1, [3; 2; 1],
        2
    );
    (
        // idx 11
        // lib.index.12
        2, [1; 2; 3],
        1
    );
    (
        // idx 12
        // lib.index.13
        3, [1; 2; 3],
        2
    );
    (
        // idx 13
        // lib.index.14
        -1, [-5; -4; -3; -2; -1; 0; 1; 2; 3; 4; 5],
        4
    );
    (
        // idx 14
        // lib.index.15
        // System.Exception - System.Collections.Generic.KeyNotFoundException
        5, [2; 4; 6; 8; 10; 12; 14; 16; 18],
        -99  // Dummy value used as place holder
    );
    (
        // idx 15
        // lib.index.16
        5, [-5; 0 ; 5; 10],
        2
    );
    |]

[<TestCase(0, TestName = "lib.index.01", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(1, TestName = "lib.index.02", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(2, TestName = "lib.index.03", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(3, TestName = "lib.index.04")>]
[<TestCase(4, TestName = "lib.index.05", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(5, TestName = "lib.index.06", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(6, TestName = "lib.index.07")>]
[<TestCase(7, TestName = "lib.index.08")>]
[<TestCase(8, TestName = "lib.index.09", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(9, TestName = "lib.index.10")>]
[<TestCase(10, TestName = "lib.index.11")>]
[<TestCase(11, TestName = "lib.index.12")>]
[<TestCase(12, TestName = "lib.index.13")>]
[<TestCase(13, TestName = "lib.index.14")>]
[<TestCase(14, TestName = "lib.index.15", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(15, TestName = "lib.index.16")>]

[<Test>]
let ``List index`` idx = 
    let (searchValue, _, _) = indexValues.[idx]
    let (_, list, _) = indexValues.[idx]
    let (_, _, result) = indexValues.[idx]
    index searchValue list
    |> should equal result
    index_orig searchValue list
    |> should equal result

// This Test is to show that they both return
// the different exceptions when given an item not in the list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// index exception test case.

[<TestCase(0, TestName = "lib.indexException.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="index")>]
[<TestCase(1, TestName = "lib.indexException.02", ExpectedException=typeof<System.Exception>, ExpectedMessage="index")>]
[<TestCase(2, TestName = "lib.indexException.03", ExpectedException=typeof<System.Exception>, ExpectedMessage="index")>]
[<TestCase(4, TestName = "lib.indexException.04", ExpectedException=typeof<System.Exception>, ExpectedMessage="index")>]
[<TestCase(5, TestName = "lib.indexException.05", ExpectedException=typeof<System.Exception>, ExpectedMessage="index")>]
[<TestCase(8, TestName = "lib.indexException.06", ExpectedException=typeof<System.Exception>, ExpectedMessage="index")>]
[<TestCase(14, TestName = "lib.indexException.07", ExpectedException=typeof<System.Exception>, ExpectedMessage="index")>]

[<Test>]
let ``List index exception`` idx = 
    let (searchValue, _, _) = indexValues.[idx]
    let (_, list, _) = indexValues.[idx]
    let (_, _, result) = indexValues.[idx]
    index_orig searchValue list
    |> should equal result

let private insertValues : (int * int list * int list)[] = [| 
    (
        // idx 0
        // lib.insert.01
        0, [],
        [0]
    );
    (
        // idx 1
        // lib.insert.02
        1, [],
        [1]
    );
    (
        // idx 2
        // lib.insert.03
        0, [1],
        [0; 1]
    );
    (
        // idx 3
        // lib.insert.04
        1, [1],
        [1]
    );
    (
        // idx 4
        // lib.insert.05
        2, [1],
        [1; 2]
    );
    (
        // idx 5
        // lib.insert.06
        0, [1; 2],
        [0; 1; 2]
    );
    (
        // idx 6
        // lib.insert.07
        1, [1; 2],
        [1; 2]
    );
    (
        // idx 7
        // lib.insert.08
        2, [1; 2],
        [1; 2]
    );
    (
        // idx 8
        // lib.insert.09
        3, [1; 2],
        [1; 2; 3]
    );
    (
        // idx 9
        // lib.insert.10
        0, [1; 2; 3],
        [0; 1; 2; 3]
    );
    (
        // idx 10
        // lib.insert.11
        1, [1; 2; 3],
        [1; 2; 3]
    );
    (
        // idx 11
        // lib.insert.12
        2, [1; 2; 3],
        [1; 2; 3]
    );
    (
        // idx 12
        // lib.insert.13
        3, [1; 2; 3],
        [1; 2; 3]
    );
    (
        // idx 13
        // lib.insert.14
        4, [1; 2; 3],
        [1; 2; 3; 4]
    );
    (
        // idx 14
        // lib.insert.15
        -1, [],
        [-1]
    );
    (
        // idx 15
        // lib.insert.16
        -1, [1],
        [-1; 1]
    );
    (
        // idx 16
        // lib.insert.17
        -1, [1; 2],
        [-1; 1; 2]
    );
    |]

[<TestCase(0, TestName = "lib.insert.01")>]
[<TestCase(1, TestName = "lib.insert.02")>]
[<TestCase(2, TestName = "lib.insert.03")>]
[<TestCase(3, TestName = "lib.insert.04")>]
[<TestCase(4, TestName = "lib.insert.05")>]
[<TestCase(5, TestName = "lib.insert.06")>]
[<TestCase(6, TestName = "lib.insert.07")>]
[<TestCase(7, TestName = "lib.insert.08")>]
[<TestCase(8, TestName = "lib.insert.09")>]
[<TestCase(9, TestName = "lib.insert.10")>]
[<TestCase(10, TestName = "lib.insert.11")>]
[<TestCase(11, TestName = "lib.insert.12")>]
[<TestCase(12, TestName = "lib.insert.13")>]
[<TestCase(13, TestName = "lib.insert.14")>]
[<TestCase(14, TestName = "lib.insert.15")>]
[<TestCase(15, TestName = "lib.insert.16")>]
[<TestCase(16, TestName = "lib.insert.17")>]

[<Test>]
let ``List insert`` idx = 
    let (insertValue, _, _) = insertValues.[idx]
    let (_, list, _) = insertValues.[idx]
    let (_, _, result) = insertValues.[idx]
    insert insertValue list
    |> should equal result
    Set.add insertValue (Set.ofList list)
    |> should equal (Set.ofList result)

let private insertatValues : (int * int * int list * int list)[] = [| 
    (
        // idx 0
        // lib.insertat.01
        // System.Exception - list too short for position to exist
        -1, 5, [],
        [] // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.insertat.02
        // System.Exception - list too short for position to exist
        1, 5, [],
        [] // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.insertat.03
        0, 5, [],
        [5]
    );
    (
        // idx 3
        // lib.insertat.04
        0, 5, [2],
        [5; 2]
    );
    (
        // idx 4
        // lib.insertat.05
        1, 5, [2],
        [2; 5]
    );
    (
        // idx 5
        // lib.insertat.06
        0, 5, [2; 4],
        [5; 2; 4]
    );
    (
        // idx 6
        // lib.insertat.07
        1, 5, [2; 4],
        [2; 5; 4]
    );
    (
        // idx 7
        // lib.insertat.08
        2, 5, [2; 4],
        [2; 4; 5]
    );
    (
        // idx 8
        // lib.insertat.09
        0, 5, [2; 4; 6],
        [5; 2; 4; 6]
    );
    (
        // idx 9
        // lib.insertat.10
        1, 5, [2; 4; 6],
        [2; 5; 4; 6]
    );
    (
        // idx 10
        // lib.insertat.11
        2, 5, [2; 4; 6],
        [2; 4; 5; 6]
    );
    (
        // idx 11
        // lib.insertat.12
        3, 5, [2; 4; 6],
        [2; 4; 6; 5]
    );
    |]

[<TestCase(0, TestName = "lib.insertat.01", ExpectedException=typeof<System.Exception>)>]
[<TestCase(1, TestName = "lib.insertat.02", ExpectedException=typeof<System.Exception>)>]
[<TestCase(2, TestName = "lib.insertat.03")>]
[<TestCase(3, TestName = "lib.insertat.04")>]
[<TestCase(4, TestName = "lib.insertat.05")>]
[<TestCase(5, TestName = "lib.insertat.06")>]
[<TestCase(6, TestName = "lib.insertat.07")>]
[<TestCase(7, TestName = "lib.insertat.08")>]
[<TestCase(8, TestName = "lib.insertat.09")>]
[<TestCase(9, TestName = "lib.insertat.10")>]
[<TestCase(10, TestName = "lib.insertat.11")>]
[<TestCase(11, TestName = "lib.insertat.12")>]

[<Test>]
let ``List insertat`` idx = 
    let (position, _, _, _) = insertatValues.[idx]
    let (_, insertValue, _, _) = insertatValues.[idx]
    let (_, _, list, _) = insertatValues.[idx]
    let (_, _, _, result) = insertatValues.[idx]
    insertat position insertValue list
    |> should equal result

let private intersectValues : (int list * int list * int list)[] = [| 
    (
        // idx 0
        // lib.intersect.01
        [], [],
        []
    );
    (
        // idx 1
        // lib.intersect.02
        [], [1],
        []
    );
    (
        // idx 2
        // lib.intersect.03
        [1], [],
        []
    );
    (
        // idx 3
        // lib.intersect.04
        [1], [1],
        [1]
    );
    (
        // idx 4
        // lib.intersect.05
        [1], [2],
        []
    );
    (
        // idx 5
        // lib.intersect.06
        [1; 2], [1; 2],
        [1; 2]
    );
    (
        // idx 6
        // lib.intersect.07
        [1; 2], [2; 3],
        [2]
    );
    (
        // idx 7
        // lib.intersect.08
        [1; 2; 3], [1],
        [1]
    );
    (
        // idx 8
        // lib.intersect.09
        [1; 2; 3], [2],
        [2]
    );
    (
        // idx 9
        // lib.intersect.10
        [1; 2; 3], [3],
        [3]
    );
    (
        // idx 10
        // lib.intersect.11
        [1; 2; 3], [1; 2],
        [1; 2]
    );
    (
        // idx 11
        // lib.intersect.12
        [1; 2; 3], [2; 3],
        [2; 3]
    );
    (
        // idx 12
        // lib.intersect.13
        [1; 2; 3], [1; 2; 3],
        [1; 2; 3]
    );
    (
        // idx 13
        // lib.intersect.14
        [1; 2; 3], [3; 2; 1],
        [1; 2; 3]
    );
    (
        // idx 14
        // lib.intersect.15
        [1; 2; 3], [1; 1; 2; 2],
        [1; 2]
    );
    (
        // idx 15
        // lib.intersect.16
        [1; 2; 3], [1; 1; 2; 2; 4; 4],
        [1; 2]
    );
    (
        // idx 16
        // lib.intersect.17
        [1; 2; 3], [-2; -1; 0; 1; 2; 3; 4; ],
        [1; 2; 3]
    );
    |]

[<TestCase(0, TestName = "lib.intersect.01")>]
[<TestCase(1, TestName = "lib.intersect.02")>]
[<TestCase(2, TestName = "lib.intersect.03")>]
[<TestCase(3, TestName = "lib.intersect.04")>]
[<TestCase(4, TestName = "lib.intersect.05")>]
[<TestCase(5, TestName = "lib.intersect.06")>]
[<TestCase(6, TestName = "lib.intersect.07")>]
[<TestCase(7, TestName = "lib.intersect.08")>]
[<TestCase(8, TestName = "lib.intersect.09")>]
[<TestCase(9, TestName = "lib.intersect.10")>]
[<TestCase(10, TestName = "lib.intersect.11")>]
[<TestCase(11, TestName = "lib.intersect.12")>]
[<TestCase(12, TestName = "lib.intersect.13")>]
[<TestCase(13, TestName = "lib.intersect.14")>]
[<TestCase(14, TestName = "lib.intersect.15")>]
[<TestCase(15, TestName = "lib.intersect.16")>]
[<TestCase(16, TestName = "lib.intersect.17")>]

[<Test>]
let ``List intersect`` idx = 
    let (list1, _, _) = intersectValues.[idx]
    let (_, list2, _) = intersectValues.[idx]
    let (_, _, result) = intersectValues.[idx]
    intersect list1 list2
    |> should equal result
    Set.intersect (Set.ofList list1) (Set.ofList list2)
    |> should equal (Set.ofList result)

let private iterValues : (string list * string)[] = [| 
    (
        // idx 0
        // lib.iter.01
        [], 
        @""
    );
    (
        // idx 1
        // lib.iter.02
        ["The"], 
        @"The"
    );
    (
        // idx 2
        // lib.iter.03
        ["The"; " quick"], 
        @"The quick"
    );
    (
        // idx 3
        // lib.iter.04
        ["The"; " quick"; " brown fox"], 
        @"The quick brown fox"
    );
    |]

[<TestCase(0, TestName = "lib.iter.01")>]
[<TestCase(1, TestName = "lib.iter.02")>]
[<TestCase(2, TestName = "lib.iter.03")>]
[<TestCase(3, TestName = "lib.iter.04")>]

// Note: Since List.iter returns unit, 
// need to use function with side effect
// or a mutable value :(
// to have some output to test against
// i.e. sb.Append.
[<Test>]
let ``List iter`` idx = 
    let (list, _) = iterValues.[idx]
    let (_, result) = iterValues.[idx]
    let sb = System.Text.StringBuilder ()
    list |> List.iter (fun (s : string) ->
        sb.Append s
        |> ignore)
    sb.ToString ()
    |> should equal result
    let sb1 = System.Text.StringBuilder ()
    list |> do_list (fun (s : string) ->
        sb1.Append s
        |> ignore)
    sb1.ToString ()
    |> should equal result

let private lastValues : (int list * int)[] = [| 
    (
        // idx 0
        // lib.last.01
        // System.Exception - Cannot get the last element of an empty list.
        [],
        -99  // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.last.02
        [1],
        1
    );
    (
        // idx 2
        // lib.last.03
        [1; 2],
        2
    );
    (
        // idx 3
        // lib.last.04
        [1; 2; 3],
        3
    );
    (
        // idx 4
        // lib.last.05
        [3; 2; 1],
        1
    )
    |]

[<TestCase(0, TestName = "lib.last.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="Cannot get the last element of an empty list.")>]
[<TestCase(1, TestName = "lib.last.02")>]
[<TestCase(2, TestName = "lib.last.03")>]
[<TestCase(3, TestName = "lib.last.04")>]
[<TestCase(4, TestName = "lib.last.05")>]

[<Test>]
let ``List last`` idx = 
    let (list, _) = lastValues.[idx]
    let (_, result) = lastValues.[idx]
    last list
    |> should equal result

let private lengthValues : (int list * int)[] = [| 
    (
        // idx 0
        // lib.length.01
        [],
        0
    );
    (
        // idx 1
        // lib.length.02
        [1],
        1
    );
    (
        // idx 2
        // lib.length.03
        [1; 2],
        2
    );
    (
        // idx 3
        // lib.length.04
        [1; 2; 3],
        3
    );
    (
        // idx 4
        // lib.length.05
        [3; 2; 1; 0],
        4
    )
    (
        // idx 5
        // lib.length.06
        [0; 1; 1; 2; 2; 3; 4; 5],
        8
    )
    |]

[<TestCase(0, TestName = "lib.length.01")>]
[<TestCase(1, TestName = "lib.length.02")>]
[<TestCase(2, TestName = "lib.length.03")>]
[<TestCase(3, TestName = "lib.length.04")>]
[<TestCase(4, TestName = "lib.length.05")>]
[<TestCase(5, TestName = "lib.length.06")>]

[<Test>]
let ``List length`` idx = 
    let (list, _) = lengthValues.[idx]
    let (_, result) = lengthValues.[idx]
    List.length list
    |> should equal result
    length list
    |> should equal result

let private mapValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.map.01
        [],
        []
    );
    (
        // idx 1
        // lib.map.02
        [1],
        [6]
    );
    (
        // idx 2
        // lib.map.03
        [1; 2],
        [6; 7]
    );
    (
        // idx 3
        // lib.map.04
        [1; 2; 3],
        [6; 7; 8]
    );
    |]

[<TestCase(0, TestName = "lib.map.01")>]
[<TestCase(1, TestName = "lib.map.02")>]
[<TestCase(2, TestName = "lib.map.03")>]
[<TestCase(3, TestName = "lib.map.04")>]

[<Test>]
let ``List map`` idx = 
    let (list, _) = mapValues.[idx]
    let (_, result) = mapValues.[idx]
    List.map (fun x -> x + 5) list
    |> should equal result
    map (fun x -> x + 5) list
    |> should equal result

let private map2Values : (int list * int list * int list)[] = [| 
    (
        // idx 0
        // lib.map2.01
        [], [],
        []
    );
    (
        // idx 1
        // lib.map2.02
        // System.ArgumentException - The lists had different lengths.
        [], [1],
        []
    );
    (
        // idx 2
        // lib.map2.03
        // System.ArgumentException - The lists had different lengths.
        [1], [],
        []
    );
    (
        // idx 3
        // lib.map2.04
        [1], [1],
        [2]
    );
    (
        // idx 4
        // lib.map2.05
        [1], [2],
        [3]
    );
    (
        // idx 5
        // lib.map2.06
        [1; 2], [1; 2],
        [2; 4]
    );
    (
        // idx 6
        // lib.map2.07
        [1; 2], [2; 3],
        [3; 5]
    );
    (
        // idx 7
        // lib.map2.08
        [1; 2; 3], [1; 2; 3],
        [2; 4; 6]
    );
    (
        // idx 8
        // lib.map2.09
        [1; 2; 3], [3; 2; 1],
        [4; 4; 4]
    );
    |]

[<TestCase(0, TestName = "lib.map2.01")>]
[<TestCase(1, TestName = "lib.map2.02", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(2, TestName = "lib.map2.03", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(3, TestName = "lib.map2.04")>]
[<TestCase(4, TestName = "lib.map2.05")>]
[<TestCase(5, TestName = "lib.map2.06")>]
[<TestCase(6, TestName = "lib.map2.07")>]
[<TestCase(7, TestName = "lib.map2.08")>]
[<TestCase(8, TestName = "lib.map2.09")>]

[<Test>]
let ``List map2`` idx = 
    let (list1, _, _) = map2Values.[idx]
    let (_, list2, _) = map2Values.[idx]
    let (_, _, result) = map2Values.[idx]
    List.map2 (fun x y -> x + y) list1 list2
    |> should equal result
    map2 (fun x y -> x + y) list1 list2
    |> should equal result

let private mapfilterValues : (int list * bool list)[] = [| 
    (
        // idx 0
        // lib.mapfilter.001
        [],
        []
    ); 
    (
        // idx 1
        // lib.mapfilter.002
        [-2],
        [true]
    );
    (
        // idx 2
        // lib.mapfilter.003
        [-1],
        [false]
    );
    (
        // idx 3
        // lib.mapfilter.004
        [0],
        [true]
    );
    (
        // idx 4
        // lib.mapfilter.005
        [1],
        [false]
    );
    (
        // idx 5
        // lib.mapfilter.006
        [1; 2],
        [false; true]
    );
    (
        // idx 6
        // lib.mapfilter.007
        [1; 3],
        [false; false]
    );
    (
        // idx 7
        // lib.mapfilter.008
        [2; 3],
        [true; false]
    );
    (
        // idx 8
        // lib.mapfilter.009
        [1; 2; 3],
        [false; true; false]
    );
    (
        // idx 9
        // lib.mapfilter.010
        [2; 3; 4],
        [true; false; true]
    );
    |]

[<TestCase(0, TestName = "lib.mapfilter.01")>]
[<TestCase(1, TestName = "lib.mapfilter.02")>]
[<TestCase(2, TestName = "lib.mapfilter.03")>]
[<TestCase(3, TestName = "lib.mapfilter.04")>]
[<TestCase(4, TestName = "lib.mapfilter.05")>]
[<TestCase(5, TestName = "lib.mapfilter.06")>]
[<TestCase(6, TestName = "lib.mapfilter.07")>]
[<TestCase(7, TestName = "lib.mapfilter.08")>]
[<TestCase(8, TestName = "lib.mapfilter.09")>]
[<TestCase(9, TestName = "lib.mapfilter.10")>]
    
[<Test>]
let ``List mapfilter`` idx = 
    let (list, _) = mapfilterValues.[idx]
    let (_, result) = mapfilterValues.[idx]
    mapfilter (fun x -> x % 2 = 0) list 
    |> should equal result

let private maximizeValues : (int list * int)[] = [| 
    (
        // idx 0
        // lib.maximize.001   
        // System.ArgumentException - The input list was empty.   
        [],
        -99  // Dummy value used as place holder
    ); 
    (
        // idx 1
        // lib.maximize.002
        [-2],
        -2
    );
    (
        // idx 2
        // lib.maximize.003
        [-2; 0],
        0
    );
    (
        // idx 3
        // lib.maximize.004
        [0; 2],
        2
    );
    (
        // idx 4
        // lib.maximize.005
        [-3; -2; -1; 0; 1; 2; 3],
        3
    );
    (
        // idx 5
        // lib.maximize.006
        [-6; -5; -4; -3; -2; -1; 0; 1; 2; 3],
        -6
    );
    |]

[<TestCase(0, TestName = "lib.maximize.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.maximize.02")>]
[<TestCase(2, TestName = "lib.maximize.03")>]
[<TestCase(3, TestName = "lib.maximize.04")>]
[<TestCase(4, TestName = "lib.maximize.05")>]
[<TestCase(5, TestName = "lib.maximize.06")>]

[<Test>]
let ``List maximize`` idx = 
    let (list, _) = maximizeValues.[idx]
    let (_, result) = maximizeValues.[idx]
    maximize (fun x -> (x + 1) * (x + 1)) list
    |> should equal result

// The next two Test are too show the similarities and differences
// between maximize and F# List.maxBy which should be
// replacable.
// 
// If there are multiple results that are the same
// maximize will return the last one while
// F# List.maxBy will return the first one
// 
// The first Test is to show that they both return
// the same exception when given an empty list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// F# List.maxBy exception test case.
//
// The second test is to show the different results
// for the same input.
[<TestCase(0, TestName = "lib.MaxByException.01", ExpectedException=typeof<System.ArgumentException>)>]

[<Test>]
let ``List MaxBy Exception`` idx = 
    let (list, _) = maximizeValues.[idx]
    let (_, maxByResult) = maximizeValues.[idx]
    List.maxBy (fun x -> 10) list
    |> should equal maxByResult

let private maximizeVsMaxByValues : (int list * int * int)[] = [| 
    (
        // idx 0
        // lib.maximizeVsMaxBy.001
        [1],
        1,
        1
    ); 
    (
        // idx 1
        // lib.maximizeVsMaxBy.002
        [1; 2],
        2,
        1
    ); 
    (
        // idx 2
        // lib.maximizeVsMaxBy.003
        [1; 2; 3],
        3,
        1
    ); 
    |]
    
[<TestCase(0, TestName = "lib.maximizeVsMaxBy.01")>]
[<TestCase(1, TestName = "lib.maximizeVsMaxBy.02")>]
[<TestCase(2, TestName = "lib.maximizeVsMaxBy.03")>]

[<Test>]
let ``List maximize Vs MaxBy`` idx = 
    let (list, _, _) = maximizeVsMaxByValues.[idx]
    let (_, maximizeResult, _) = maximizeVsMaxByValues.[idx]
    let (_, _, maxByResult) = maximizeVsMaxByValues.[idx]
    maximize (fun x -> 10) list
    |> should equal maximizeResult
    List.maxBy (fun x -> 10) list
    |> should equal maxByResult

let private memValues : (int * int list * bool)[] = [| 
    (
        // idx 0
        // lib.mem.001
        0, [],
        false
    ); 
    (
        // idx 1
        // lib.mem.002
        0, [1],
        false
    );
    (
        // idx 2
        // lib.mem.003
        1, [1],
        true
    );
    (
        // idx 3
        // lib.mem.004
        0, [1; 2],
        false
    );
    (
        // idx 4
        // lib.mem.005
        1, [1; 2],
        true
    );
    (
        // idx 5
        // lib.mem.006
        2, [1; 2],
        true
    );
    (
        // idx 6
        // lib.mem.007
        5, [1; 2; 3; 4; 5],
        true
    );
    (
        // idx 7
        // lib.mem.008
        6, [1; 2; 3; 4; 5],
        false
    );
    |]

[<TestCase(0, TestName = "lib.mem.01")>]
[<TestCase(1, TestName = "lib.mem.02")>]
[<TestCase(2, TestName = "lib.mem.03")>]
[<TestCase(3, TestName = "lib.mem.04")>]
[<TestCase(4, TestName = "lib.mem.05")>]
[<TestCase(5, TestName = "lib.mem.06")>]
[<TestCase(6, TestName = "lib.mem.07")>]
[<TestCase(7, TestName = "lib.mem.08")>]

[<Test>]
let ``List mem`` idx = 
    let (elem, _, _) = memValues.[idx]
    let (_, list, _) = memValues.[idx]
    let (_, _, result) = memValues.[idx]
    mem elem list 
    |> should equal result
    Set.contains elem (Set.ofList list)
    |> should equal result

let private mergeValues : (int list * int list * int list * int list * int list * int list * int list * int list)[] = [| 
    (
        // idx 0
        // lib.merge.01
        [], [],
        [],
        [],
        [],
        [],
        [],
        []
    );
    (
        // idx 1
        // lib.merge.02
        [], [1],
        [1],
        [1],
        [1],
        [1],
        [1],
        [1]
    );
    (
        // idx 2
        // lib.merge.03
        [1], [],
        [1],
        [1],
        [1],
        [1],
        [1],
        [1]
    );
    (
        // idx 3
        // lib.merge.04
        [1], [1],
        [1; 1],
        [1; 1],
        [1; 1],
        [1; 1],
        [1; 1],
        [1; 1]
    );
    (
        // idx 4
        // lib.merge.05
        [1], [2],
        [2; 1],
        [1; 2],
        [2; 1],
        [2; 1],
        [1; 2],
        [1; 2]
    );
    (
        // idx 5
        // lib.merge.06
        [1; 2], [1; 2],
        [1; 2; 1; 2],
        [1; 1; 2; 2],
        [1; 1; 2; 2],
        [1; 2; 1; 2],
        [1; 1; 2; 2],
        [1; 1; 2; 2]
    );
    (
        // idx 6
        // lib.merge.07
        [1; 2], [2; 3],
        [2; 3; 1; 2],
        [1; 2; 2; 3],
        [2; 3; 1; 2],
        [2; 3; 1; 2],
        [1; 2; 2; 3],
        [1; 2; 2; 3]
    );
    (
        // idx 7
        // lib.merge.08
        [1; 2; 3], [1],
        [1; 1; 2; 3],
        [1; 1; 2; 3],
        [1; 1; 2; 3],
        [1; 2; 3; 1],
        [1; 1; 2; 3],
        [1; 1; 2; 3]
    );
    (
        // idx 8
        // lib.merge.09
        [1; 2; 3], [2],
        [2; 1; 2; 3],
        [1; 2; 2; 3],
        [2; 1; 2; 3],
        [2; 1; 2; 3],
        [1; 2; 2; 3],
        [1; 2; 2; 3]
    );
    (
        // idx 9
        // lib.merge.10
        [1; 2; 3], [3],
        [3; 1; 2; 3],
        [1; 2; 3; 3],
        [3; 1; 2; 3],
        [3; 1; 2; 3],
        [1; 2; 3; 3],
        [1; 2; 3; 3]
    );
    (
        // idx 10
        // lib.merge.11
        [1; 2; 3], [1; 2],
        [1; 2; 1; 2; 3],
        [1; 1; 2; 2; 3],
        [1; 1; 2; 2; 3],
        [1; 2; 3; 1; 2],
        [1; 1; 2; 2; 3],
        [1; 1; 2; 2; 3]
    );
    (
        // idx 11
        // lib.merge.12
        [1; 2; 3], [2; 3],
        [2; 3; 1; 2; 3],
        [1; 2; 2; 3; 3],
        [2; 3; 1; 2; 3],
        [2; 3; 1; 2; 3],
        [1; 2; 2; 3; 3],
        [1; 2; 2; 3; 3]
    );
    (
        // idx 12
        // lib.merge.13
        [1; 2; 3], [1; 2; 3],
        [1; 2; 3; 1; 2; 3],
        [1; 1; 2; 2; 3; 3],
        [1; 1; 2; 2; 3; 3],
        [1; 2; 3; 1; 2; 3],
        [1; 1; 2; 2; 3; 3],
        [1; 1; 2; 2; 3; 3]
    );
    (
        // idx 13
        // lib.merge.14
        [1; 2; 3], [3; 2; 1],
        [3; 2; 1; 1; 2; 3],
        [1; 2; 3; 2; 1; 3],
        [3; 2; 1; 1; 2; 3],
        [3; 2; 1; 2; 3; 1],
        [1; 2; 3; 3; 2; 1],
        [1; 2; 3; 3; 2; 1]
    );
    (
        // idx 14
        // lib.merge.15
        [1; 2; 3], [1; 1; 2; 2],
        [1; 1; 2; 2; 1; 2; 3],
        [1; 1; 1; 2; 2; 2; 3],
        [1; 1; 1; 2; 2; 2; 3],
        [1; 2; 3; 1; 1; 2; 2],
        [1; 1; 1; 2; 2; 2; 3],
        [1; 1; 1; 2; 2; 2; 3]
    );
    (
        // idx 15
        // lib.merge.16
        [1; 2; 3], [1; 1; 2; 2; 4; 4],
        [1; 1; 2; 2; 4; 4; 1; 2; 3],
        [1; 1; 1; 2; 2; 2; 3; 4; 4],
        [1; 1; 1; 2; 2; 2; 4; 4; 3],
        [1; 2; 3; 1; 1; 2; 2; 4; 4],
        [1; 1; 1; 2; 2; 2; 3; 4; 4],
        [1; 1; 1; 2; 2; 2; 3; 4; 4]
    );
    (
        // idx 16
        // lib.merge.17
        [1; 2; 3], [-2; -1; 0; 1; 2; 3; 4],
        [1; 2; 3; -2; -1; 0; 1; 2; 3; 4],
        [-2; -1; 0; 1; 1; 2; 2; 3; 3; 4],
        [-2; -1; 0; 1; 1; 2; 2; 3; 3; 4],
        [1; 2; 3; -2; -1; 0; 1; 2; 3; 4],
        [-2; -1; 0; 1; 1; 2; 2; 3; 3; 4],
        [1; 2; 3; -2; -1; 0; 1; 2; 3; 4]
    );
    |]

[<TestCase(0, TestName = "lib.merge.01")>]
[<TestCase(1, TestName = "lib.merge.02")>]
[<TestCase(2, TestName = "lib.merge.03")>]
[<TestCase(3, TestName = "lib.merge.04")>]
[<TestCase(4, TestName = "lib.merge.05")>]
[<TestCase(5, TestName = "lib.merge.06")>]
[<TestCase(6, TestName = "lib.merge.07")>]
[<TestCase(7, TestName = "lib.merge.08")>]
[<TestCase(8, TestName = "lib.merge.09")>]
[<TestCase(9, TestName = "lib.merge.10")>]
[<TestCase(10, TestName = "lib.merge.11")>]
[<TestCase(11, TestName = "lib.merge.12")>]
[<TestCase(12, TestName = "lib.merge.13")>]
[<TestCase(13, TestName = "lib.merge.14")>]
[<TestCase(14, TestName = "lib.merge.15")>]
[<TestCase(15, TestName = "lib.merge.16")>]
[<TestCase(16, TestName = "lib.merge.17")>]

[<Test>]
let ``List merge`` idx = 
    let (list1, _, _, _, _, _, _, _) = mergeValues.[idx]
    let (_, list2, _, _, _, _, _, _) = mergeValues.[idx]
    let (_, _, greaterThanResult, _, _, _, _, _) = mergeValues.[idx]
    let (_, _, _, lessThanResult, _, _, _, _) = mergeValues.[idx]
    let (_, _, _, _, equalResult, _, _, _) = mergeValues.[idx]
    let (_, _, _, _, _, greaterThanOrEqualResult, _, _) = mergeValues.[idx]
    let (_, _, _, _, _, _, lessThanOrEqualResult, _) = mergeValues.[idx]
    let (_, _, _, _, _, _, _, notEqualResult) = mergeValues.[idx]
    merge (>) list1 list2
    |> should equal greaterThanResult
    merge (<) list1 list2
    |> should equal lessThanResult
    merge (=) list1 list2
    |> should equal equalResult
    merge (>=) list1 list2
    |> should equal greaterThanOrEqualResult
    merge (<=) list1 list2
    |> should equal lessThanOrEqualResult
    merge (<>) list1 list2
    |> should equal notEqualResult

let private minimizeValues : (int list * int)[] = [| 
    (
        // idx 0
        // lib.minimize.001   
        // System.ArgumentException - The input list was empty.   
        [],
        -99  // Dummy value used as place holder
    ); 
    (
        // idx 1
        // lib.minimize.002
        [-2],
        -2
    );
    (
        // idx 2
        // lib.minimize.003
        [-2; 0],
        0
    );
    (
        // idx 3
        // lib.minimize.004
        [0; 2],
        2
    );
    (
        // idx 4
        // lib.minimize.005
        [-3; -2; -1; 0; 1; 2; 3],
        3
    );
    (
        // idx 5
        // lib.minimize.006
        [-6; -5; -4; -3; -2; -1; 0; 1; 2; 3],
        -6
    );
    |]

[<TestCase(0, TestName = "lib.minimize.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.minimize.02")>]
[<TestCase(2, TestName = "lib.minimize.03")>]
[<TestCase(3, TestName = "lib.minimize.04")>]
[<TestCase(4, TestName = "lib.minimize.05")>]
[<TestCase(5, TestName = "lib.minimize.06")>]

[<Test>]
let ``List minimize`` idx = 
    let (list, _) = minimizeValues.[idx]
    let (_, result) = minimizeValues.[idx]
    minimize (fun x -> -((x + 1) * (x + 1))) list
    |> should equal result

// The next two Test are to show the similarities and differences
// between minimize and F# List.minBy which should be
// replacable.
// 
// If there are multiple results that are the same
// minimize will return the last one while
// F# List.minBy will return the first one
// 
// The first Test is to show that they both return
// the same exception when given an empty list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// F# List.minBy exception test case.
//
// The second test is to show the different results
// for the same input.
[<TestCase(0, TestName = "lib.minByException.01", ExpectedException=typeof<System.ArgumentException>)>]

[<Test>]
let ``List minBy Exception`` idx = 
    let (list, _) = minimizeValues.[idx]
    let (_, minByResult) = minimizeValues.[idx]
    List.minBy (fun x -> 10) list
    |> should equal minByResult

let private minimizeVsminByValues : (int list * int * int)[] = [| 
    (
        // idx 0
        // lib.minimizeVsminBy.001
        [1],
        1,
        1
    ); 
    (
        // idx 1
        // lib.minimizeVsminBy.002
        [1; 2],
        2,
        1
    ); 
    (
        // idx 2
        // lib.minimizeVsminBy.003
        [1; 2; 3],
        3,
        1
    ); 
    |]
    
[<TestCase(0, TestName = "lib.minimizeVsminBy.01")>]
[<TestCase(1, TestName = "lib.minimizeVsminBy.02")>]
[<TestCase(2, TestName = "lib.minimizeVsminBy.03")>]

[<Test>]
let ``List minimize Vs minBy`` idx = 
    let (list, _, _) = minimizeVsminByValues.[idx]
    let (_, minimizeResult, _) = minimizeVsminByValues.[idx]
    let (_, _, minByResult) = minimizeVsminByValues.[idx]
    minimize (fun x -> 10) list
    |> should equal minimizeResult
    List.minBy (fun x -> 10) list
    |> should equal minByResult

let private nthValues : (int list * int * int)[] = [| 
    (
        // idx 0
        // lib.nth.001   
        // System.ArgumentException - The index was outside the range of elemements in the list. 
        [], 1,
        -99  // Dummy value used as place holder
    ); 
    (
        // idx 1
        // System.ArgumentException - The index was outside the range of elemements in the list. 
        [3], -1,
        -99  // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.nth.003
        [3], 0,
        3
    );
    (
        // idx 3
        // lib.nth.004
        [3; 4], 0,
        3
    );
    (
        // idx 4
        // lib.nth.005
        [3; 4], 1,
        4
    );
    (
        // idx 5
        // lib.nth.006
        [1; 2; 3], 0,
        1
    );
    (
        // idx 6
        // lib.nth.007
        [1; 2; 3], 1,
        2
    );
    (
        // idx 7
        // lib.nth.008
        [1; 2; 3], 2,
        3
    );
    (
        // idx 8
        // lib.nth.009
        [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; 0], 3,
        7
    );
    |]

[<TestCase(0, TestName = "lib.nth.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.nth.02", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(2, TestName = "lib.nth.03")>]
[<TestCase(3, TestName = "lib.nth.04")>]
[<TestCase(4, TestName = "lib.nth.05")>]
[<TestCase(5, TestName = "lib.nth.06")>]
[<TestCase(6, TestName = "lib.nth.07")>]
[<TestCase(7, TestName = "lib.nth.08")>]
[<TestCase(8, TestName = "lib.nth.09")>]

[<Test>]
let ``List nth`` idx = 
    let (list, _, _) = nthValues.[idx]
    let (_, elem, result) = nthValues.[idx]
    let (_, _, result) = nthValues.[idx]
    List.nth list elem
    |> should equal result
    el elem list 
    |> should equal result

// This Test is to show that they both return
// the same exception when given an index was outside the 
// range of elemements in the list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// el exception test case.

[<TestCase(0, TestName = "lib.elException.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.elException.02", ExpectedException=typeof<System.ArgumentException>)>]

[<Test>]
let ``List el exception`` idx = 
    let (list, _, _) = nthValues.[idx]
    let (_, elem, result) = nthValues.[idx]
    let (_, _, result) = nthValues.[idx]
    el elem list 
    |> should equal result

// (--) is included here to demonstrate that
// OCaml (--) and F# [n..m] return same results.
let rec (--) = 
    fun m n -> 
        if m > n then [] 
        else m::((m + 1) -- n)

let private rangeIntValues : (int * int * int list)[] = [| 
    (
        // idx 0
        // lib.rangeInt.001 
        2, -2,
        []
    ); 
    (
        // idx 1
        // lib.rangeInt.002
        1, 1,
        [1]
    ); 
    (
        // idx 2
        // lib.rangeInt.003
        1, 2,
        [1; 2]
    ); 
    (
        // idx 3
        // lib.rangeInt.004
        1, 3,
        [1; 2; 3]
    ); 
    (
        // idx 4
        // lib.rangeInt.005
        -5, 5,
        [-5; -4; -3; -2; -1; 0; 1; 2; 3; 4; 5]
    ); 
    |]

[<TestCase(0, TestName = "lib.rangeInt.01")>]
[<TestCase(1, TestName = "lib.rangeInt.02")>]
[<TestCase(2, TestName = "lib.rangeInt.03")>]
[<TestCase(3, TestName = "lib.rangeInt.04")>]
[<TestCase(4, TestName = "lib.rangeInt.05")>]

[<Test>]
let ``List operator range (Int)`` idx = 
    let (start, _, _) = rangeIntValues.[idx]
    let (_, stop, result) = rangeIntValues.[idx]
    let (_, _, result) = rangeIntValues.[idx]
    [start..stop]
    |> should equal result
    (start -- stop) 
    |> should equal result

// (---) is included here to demonstrate that
// OCaml (---) and F# [n..m] return same results.
// Note: OCaml restricts values to Num by 
// using num operators for > and + .
// Since F# overloads operators,
// we have to restrict values using parameter types.
let rec (---) = 
    fun (m : num) (n : num) -> 
        if m > n then [] 
        else m::((m + (Int 1)) --- n)

let private rangeNumValues : (Num * Num * Num list)[] = [| 
    (
        // idx 0
        // lib.rangeNum.001 
        (num_of_int 2), (num_of_int -2),
        []
    ); 
    (
        // idx 1
        // lib.rangeNum.002
        (num_of_int 1), (num_of_int 1),
        [(num_of_int 1)]
    ); 
    (
        // idx 2
        // lib.rangeNum.003
        (num_of_int 1), (num_of_int 2),
        [(num_of_int 1); (num_of_int 2)]
    ); 
    (
        // idx 3
        // lib.rangeNum.004
        (num_of_int 1), (num_of_int 3),
        [(num_of_int 1); (num_of_int 2); (num_of_int 3)]
    ); 
    (
        // idx 4
        // lib.rangeNum.005
        (num_of_int -5), (num_of_int 5),
        [(num_of_int -5); (num_of_int -4); (num_of_int -3); (num_of_int -2); (num_of_int -1); (num_of_int 0); (num_of_int 1); (num_of_int 2); (num_of_int 3); (num_of_int 4); (num_of_int 5)]
    ); 
    |]

[<TestCase(0, TestName = "lib.rangeNum.01")>]
[<TestCase(1, TestName = "lib.rangeNum.02")>]
[<TestCase(2, TestName = "lib.rangeNum.03")>]
[<TestCase(3, TestName = "lib.rangeNum.04")>]
[<TestCase(4, TestName = "lib.rangeNum.05")>]

[<Test>]
let ``List operator range (Num)`` idx = 
    let (start, _, _) = rangeNumValues.[idx]
    let (_, stop, _) = rangeNumValues.[idx]
    let (_, _, result) = rangeNumValues.[idx]
    [start..stop]
    |> should equal result
    (start --- stop) 
    |> should equal result

let private partitionValues : (int list * (int list * int list))[] = [| 
    (
        // idx 0
        // lib.partition.001
        [],
        ( [], [] )
    ); 
    (
        // idx 1
        // lib.partition.002
        [-2],
        ( [-2], [] )
    );
    (
        // idx 2
        // lib.partition.003
        [-1],
        ( [], [-1] )
    );
    (
        // idx 3
        // lib.partition.004
        [0],
        ( [0], [] )
    );
    (
        // idx 4
        // lib.partition.005
        [1],
        ( [], [1] )
    );
    (
        // idx 5
        // lib.partition.006
        [1; 2],
        ( [2], [1] )
    );
    (
        // idx 6
        // lib.partition.007
        [1; 3],
        ( [], [1; 3] )
    );
    (
        // idx 7
        // lib.partition.008
        [2; 3],
        ( [2], [3] )
    );
    (
        // idx 8
        // lib.partition.009
        [1; 2; 3],
        ( [2], [1; 3] )
    );
    (
        // idx 9
        // lib.partition.010
        [2; 3; 4],
        ( [2; 4], [3] )
    ); 
    |]

[<TestCase(0, TestName = "lib.partition.01")>]
[<TestCase(1, TestName = "lib.partition.02")>]
[<TestCase(2, TestName = "lib.partition.03")>]
[<TestCase(3, TestName = "lib.partition.04")>]
[<TestCase(4, TestName = "lib.partition.05")>]
[<TestCase(5, TestName = "lib.partition.06")>]
[<TestCase(6, TestName = "lib.partition.07")>]
[<TestCase(7, TestName = "lib.partition.08")>]
[<TestCase(8, TestName = "lib.partition.09")>]
[<TestCase(9, TestName = "lib.partition.10")>]

[<Test>]
let ``List partition`` idx = 
    let (list, _) = partitionValues.[idx]
    let (_, result ) = partitionValues.[idx]
    List.partition (fun x -> x % 2 = 0) list 
    |> should equal result
    partition (fun x -> x % 2 = 0) list 
    |> should equal result

let private psubsetValues : (int list * int list * bool)[] = [| 
    (
        // idx 0
        // lib.psubset.01
        [], [],
        false
    );
    (
        // idx 1
        // lib.psubset.02
        [], [1],
        true
    );
    (
        // idx 2
        // lib.psubset.03
        [1], [],
        false
    );
    (
        // idx 3
        // lib.psubset.04
        [1], [1],
        false
    );
    (
        // idx 4
        // lib.psubset.05
        [1], [2],
        false
    );
    (
        // idx 5
        // lib.psubset.06
        [], [1; 2],
        true
    );
    (
        // idx 6
        // lib.psubset.07
        [1], [1; 2],
        true
    );
    (
        // idx 7
        // lib.psubset.08
        [2], [1; 2],
        true
    );
    (
        // idx 8
        // lib.psubset.09
        [1; 2], [1; 2],
        false
    );
    (
        // idx 9
        // lib.psubset.10
        [], [2; 1],
        true
    );
    (
        // idx 10
        // lib.psubset.11
        [1], [2; 1],
        true
    );
    (
        // idx 11
        // lib.psubset.12
        [2], [2; 1],
        true
    );
    (
        // idx 12
        // lib.psubset.13
        [1; 2], [2; 1],
        false
    );
    (
        // idx 13
        // lib.psubset.14
        [1; 2; 3], [3; 2; 1],
        false
    );
    (
        // idx 14
        // lib.psubset.15
        [1; 2; 3], [1; 1; 2; 2; 3; 3],
        false
    );
    (
        // idx 15
        // lib.psubset.16
        [1; 2; 3], [1; 2],
        false
    );
    (
        // idx 16
        // lib.psubset.17
        [-1; 0; 1], [-2; -1; 0; 1; 2; 3; 4],
        true
    );
    |]

[<TestCase(0, TestName = "lib.psubset.01")>]
[<TestCase(1, TestName = "lib.psubset.02")>]
[<TestCase(2, TestName = "lib.psubset.03")>]
[<TestCase(3, TestName = "lib.psubset.04")>]
[<TestCase(4, TestName = "lib.psubset.05")>]
[<TestCase(5, TestName = "lib.psubset.06")>]
[<TestCase(6, TestName = "lib.psubset.07")>]
[<TestCase(7, TestName = "lib.psubset.08")>]
[<TestCase(8, TestName = "lib.psubset.09")>]
[<TestCase(9, TestName = "lib.psubset.10")>]
[<TestCase(10, TestName = "lib.psubset.11")>]
[<TestCase(11, TestName = "lib.psubset.12")>]
[<TestCase(12, TestName = "lib.psubset.13")>]
[<TestCase(13, TestName = "lib.psubset.14")>]
[<TestCase(14, TestName = "lib.psubset.15")>]
[<TestCase(15, TestName = "lib.psubset.16")>]
[<TestCase(16, TestName = "lib.psubset.17")>]

[<Test>]
let ``List psubset`` idx = 
    let (list1, _, _) = psubsetValues.[idx]
    let (_, list2, _) = psubsetValues.[idx]
    let (_, _, result) = psubsetValues.[idx]
    psubset list1 list2
    |> should equal result
    Set.isProperSubset (Set.ofList list1) (Set.ofList list2)
    |> should equal result

let private reduceBackValues : (int list * int)[] = [| 
    (
        // idx 0
        // lib.reduceBack.01
        // System.ArgumentException - The input list was empty.
        // System.Exception - end_itlist
        [],
        -99  // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.reduceBack.02
        [1],
        1
    );
    (
        // idx 2
        // lib.reduceBack.03
        [1; 2],
        2
    );
    (
        // idx 3
        // lib.reduceBack.04
        [1; 2; 3],
        6
    );
    (
        // idx 4
        // lib.reduceBack.05
        [1; 2; 3; 4],
        24
    );
    |]

[<TestCase(0, TestName = "lib.reduceBack.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.reduceBack.02")>]
[<TestCase(2, TestName = "lib.reduceBack.03")>]
[<TestCase(3, TestName = "lib.reduceBack.04")>]
[<TestCase(4, TestName = "lib.reduceBack.05")>]

[<Test>]
let ``List reduceBack`` idx = 
    let (list, _) = reduceBackValues.[idx]
    let (_, result) = reduceBackValues.[idx]
    List.reduceBack (fun x y -> x * y) list 
    |> should equal result
    end_itlist (fun x y -> x * y) list 
    |> should equal result

// This Test is to show that they both return
// different exceptions when given an empty list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// end_itlist exception test case.

[<TestCase(0, TestName = "lib.end_itlistException.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="end_itlist")>]

[<Test>]
let ``List end_itlist Exception`` idx = 
    let (list, _) = minimizeValues.[idx]
    let (_, result) = minimizeValues.[idx]
    end_itlist (fun x y -> x * y) list 
    |> should equal result

let private replicateValues : (int * string * string list)[] = [| 
    (
        // idx 0
        // lib.replicate.01
        // F#: System.ArgumentException - The input must be non-negative.
        // OCaml: []
        -1, "a",
        [ ]  
    );
    (
        // idx 1
        // lib.replicate.02
        0, "a",
        [ ]
    );
    (
        // idx 2
        // lib.replicate.03
        1, "a",
        [ "a" ]
    );
    (
        // idx 3
        // lib.replicate.04
        2, "a",
        [ "a"; "a" ]
    );
    (
        // idx 4
        // lib.replicate.05
        2, "a b",
        [ "a b"; "a b" ]
    );
    (
        // idx 5
        // lib.replicate.04
        10, "a",
        [ "a"; "a"; "a"; "a"; "a"; "a"; "a"; "a"; "a"; "a" ]
    );
    |]

[<TestCase(0, TestName = "lib.replicate.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.replicate.02")>]
[<TestCase(2, TestName = "lib.replicate.03")>]
[<TestCase(3, TestName = "lib.replicate.04")>]
[<TestCase(4, TestName = "lib.replicate.05")>]
[<TestCase(5, TestName = "lib.replicate.06")>]

[<Test>]
let ``List replicate`` idx = 
    let (count, _, _) = replicateValues.[idx]
    let (_, initial, _) = replicateValues.[idx]
    let (_, _, result) = replicateValues.[idx]
    List.replicate count initial 
    |> should equal result
    replicate count initial 
    |> should equal result

// This Test is to show that when count is negative
// F# List.replicate will return exception and
// OCaml replicate will return [].
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// OCaml replicate test case.

[<TestCase(0, TestName = "lib.replicateDifference.01")>]

[<Test>]
let ``List replicate (OCaml) negative count`` idx = 
    let (count, _, _) = replicateValues.[idx]
    let (_, initial, _) = replicateValues.[idx]
    let (_, _, result) = replicateValues.[idx]
    replicate count initial 
    |> should equal result

let private revValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.rev.01
        [],
        []
    );
    (
        // idx 1
        // lib.rev.02
        [1],
        [1]
    );
    (
        // idx 2
        // lib.rev.03
        [1; 2],
        [2; 1]
    );
    (
        // idx 3
        // lib.rev.04
        [1; 2; 3],
        [3; 2; 1]
    );
    (
        // idx 4
        // lib.rev.05
        [-2; -1; 0; 1; 2],
        [2; 1; 0; -1; -2]
    );
    (
        // idx 5
        // lib.rev.06
        [4; 9; 5; 11; 6; 2],
        [2; 6; 11; 5; 9; 4]
    );
    |]

[<TestCase(0, TestName = "lib.rev.01")>]
[<TestCase(1, TestName = "lib.rev.02")>]
[<TestCase(2, TestName = "lib.rev.03")>]
[<TestCase(3, TestName = "lib.rev.04")>]
[<TestCase(4, TestName = "lib.rev.05")>]
[<TestCase(5, TestName = "lib.rev.06")>]

[<Test>]
let ``List rev`` idx = 
    let (list, _) = revValues.[idx]
    let (_, result) = revValues.[idx]
    List.rev list
    |> should equal result
    rev list
    |> should equal result

let private set_eqValues : (int list * int list * bool)[] = [| 
    (
        // idx 0
        // lib.set_eq.01
        [], [],
        true
    );
    (
        // idx 1
        // lib.set_eq.02
        [], [1],
        false
    );
    (
        // idx 2
        // lib.set_eq.03
        [], [1; 2],
        false
    );
    (
        // idx 3
        // lib.set_eq.04
        [], [1; 1],
        false
    );
    (
        // idx 4
        // lib.set_eq.05
        [1], [],
        false
    );
    (
        // idx 5
        // lib.set_eq.06
        [1; 2], [],
        false
    );
    (
        // idx 6
        // lib.set_eq.07
        [1; 1], [],
        false
    );
    (
        // idx 7
        // lib.set_eq.08
        [1], [1],
        true
    );
    (
        // idx 8
        // lib.set_eq.09
        [1], [1; 2],
        false
    );
    (
        // idx 9
        // lib.set_eq.10
        [1], [1; 2; 3],
        false
    );
    (
        // idx 10
        // lib.set_eq.11
        [1], [1; 1],
        true
    );
    (
        // idx 11
        // lib.set_eq.12
        [1; 2], [1],
        false
    );
    (
        // idx 12
        // lib.set_eq.13
        [1; 2; 3], [1],
        false
    );
    (
        // idx 13
        // lib.set_eq.14
        [1; 1], [1],
        true
    );
    (
        // idx 14
        // lib.set_eq.15
        [1; 2], [1; 2],
        true
    );
    (
        // idx 15
        // lib.set_eq.16
        [1; 2], [1; 2; 3],
        false
    );
    (
        // idx 16
        // lib.set_eq.17
        [1; 2], [1; 2; 3; 4],
        false
    );
    (
        // idx 17
        // lib.set_eq.18
        [1; 2], [1; 1; 2],
        true
    );
    (
        // idx 18
        // lib.set_eq.19
        [1; 2], [1; 2; 2],
        true
    );
    (
        // idx 19
        // lib.set_eq.20
        [1; 2], [1; 2; 1; 1],
        true
    );
    (
        // idx 20
        // lib.set_eq.21
        [1; 2], [2; 2; 2; 1],
        true
    );
    (
        // idx 21
        // lib.set_eq.22
        [1; 2; 3], [1; 2],
        false
    );
    (
        // idx 22
        // lib.set_eq.23
        [1; 2; 3; 4], [1; 2],
        false
    );
    (
        // idx 23
        // lib.set_eq.24
        [1; 1; 2], [1; 2],
        true
    );
    (
        // idx 24
        // lib.set_eq.25
        [1; 2; 2], [1; 2],
        true
    );
    (
        // idx 25
        // lib.set_eq.26
        [1; 2; 1; 1], [1; 2],
        true
    );
    (
        // idx 26
        // lib.set_eq.27
        [2; 2; 2; 1], [1; 2],
        true
    );
    |]

[<TestCase(0, TestName = "lib.set_eq.01")>]
[<TestCase(1, TestName = "lib.set_eq.02")>]
[<TestCase(2, TestName = "lib.set_eq.03")>]
[<TestCase(3, TestName = "lib.set_eq.04")>]
[<TestCase(4, TestName = "lib.set_eq.05")>]
[<TestCase(5, TestName = "lib.set_eq.06")>]
[<TestCase(6, TestName = "lib.set_eq.07")>]
[<TestCase(7, TestName = "lib.set_eq.08")>]
[<TestCase(8, TestName = "lib.set_eq.09")>]
[<TestCase(9, TestName = "lib.set_eq.10")>]
[<TestCase(10, TestName = "lib.set_eq.11")>]
[<TestCase(11, TestName = "lib.set_eq.12")>]
[<TestCase(12, TestName = "lib.set_eq.13")>]
[<TestCase(13, TestName = "lib.set_eq.14")>]
[<TestCase(14, TestName = "lib.set_eq.15")>]
[<TestCase(15, TestName = "lib.set_eq.16")>]
[<TestCase(16, TestName = "lib.set_eq.17")>]
[<TestCase(17, TestName = "lib.set_eq.18")>]
[<TestCase(18, TestName = "lib.set_eq.19")>]
[<TestCase(19, TestName = "lib.set_eq.20")>]
[<TestCase(20, TestName = "lib.set_eq.21")>]
[<TestCase(21, TestName = "lib.set_eq.22")>]
[<TestCase(22, TestName = "lib.set_eq.23")>]
[<TestCase(23, TestName = "lib.set_eq.24")>]
[<TestCase(24, TestName = "lib.set_eq.25")>]
[<TestCase(25, TestName = "lib.set_eq.26")>]
[<TestCase(26, TestName = "lib.set_eq.27")>]

[<Test>]
let ``List set_eq`` idx = 
    let (list1, _, _) = set_eqValues.[idx]
    let (_, list2, _) = set_eqValues.[idx]
    let (_, _, result) = set_eqValues.[idx]
    set_eq list1 list2
    |> should equal result
    let equalResult =  (Set.ofList list1) = (Set.ofList list2)
    equalResult
    |> should equal result

let private setifyValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.setify.01
        [],
        []
    );
    (
        // idx 1
        // lib.setify.02
        [1],
        [1]
    );
    (
        // idx 2
        // lib.setify.03
        [1; 1],
        [1]
    );
    (
        // idx 3
        // lib.setify.04
        [1; 2],
        [1; 2]
    );
    (
        // idx 4
        // lib.setify.05
        [2; 1],
        [1; 2]
    );
    (
        // idx 5
        // lib.setify.06
        [1; 1; 2],
        [1; 2]
    );
    (
        // idx 6
        // lib.setify.07
        [1; 1; 2; 2],
        [1; 2]
    );
    (
        // idx 7
        // lib.setify.08
        [1; 1; 1; 2; 2; 2],
        [1; 2]
    );
    (
        // idx 8
        // lib.setify.09
        [1; 1; 1; 1; 2; 2; 2; 2],
        [1; 2]
    );
    (
        // idx 9
        // lib.setify.10
        [1; 3; 5; 7; 9; 2; 4; 6; 8],
        [1; 2; 3; 4; 5; 6; 7; 8; 9]
    );
    (
        // idx 10
        // lib.setify.11
        [1; 3; 5; 7; 9; 2; 4; 6; 8; 7; 6; 5; 4; 3; 2; 1],
        [1; 2; 3; 4; 5; 6; 7; 8; 9]
    );
    (
        // idx 11
        // lib.setify.12
        [3; 5; 9; 2; 4; 6; 8; 7; 5; 4; 3; 1],
        [1; 2; 3; 4; 5; 6; 7; 8; 9]
    );
    |]

[<TestCase(0, TestName = "lib.setify.01")>]
[<TestCase(1, TestName = "lib.setify.02")>]
[<TestCase(2, TestName = "lib.setify.03")>]
[<TestCase(3, TestName = "lib.setify.04")>]
[<TestCase(4, TestName = "lib.setify.05")>]
[<TestCase(5, TestName = "lib.setify.06")>]
[<TestCase(6, TestName = "lib.setify.07")>]
[<TestCase(7, TestName = "lib.setify.08")>]
[<TestCase(8, TestName = "lib.setify.09")>]
[<TestCase(9, TestName = "lib.setify.10")>]
[<TestCase(10, TestName = "lib.setify.11")>]
[<TestCase(11, TestName = "lib.setify.12")>]

[<Test>]
let ``List setify`` idx = 
    let (list, _) = setifyValues.[idx]
    let (_, result) = setifyValues.[idx]
    setify list
    |> should equal result
    let setResult = Set.ofList list
    setResult
    |> should equal (Set.ofList result)
    
let private sortValues : (int list * int list * int list * int list * int list * int list * int list)[] = [| 
    (
        // idx 0
        // lib.sort.01
        [],
        [],
        [],
        [],
        [],
        [],
        []
    );
    (
        // idx 1
        // lib.sort.02
        [1],
        [1],
        [1],
        [1],
        [1],
        [1],
        [1]
    );
    (
        // idx 2
        // lib.sort.03
        [1; 2],
        [2; 1],
        [1; 2],
        [2; 1],
        [2; 1],
        [1; 2],
        [1; 2]
    );
    (
        // idx 3
        // lib.sort.04
        [2; 1],
        [2; 1],
        [1; 2],
        [1; 2],
        [2; 1],
        [1; 2],
        [2; 1]
    );
    (
        // idx 4
        // lib.sort.05
        [1; 2; 3],
        [3; 2; 1],
        [1; 2; 3],
        [2; 1; 3],
        [3; 2; 1],
        [1; 2; 3],
        [3; 1; 2]
    );
    (
        // idx 5
        // lib.sort.06
        [3; 2; 1],
        [3; 2; 1],
        [1; 2; 3],
        [2; 3; 1],
        [3; 2; 1],
        [1; 2; 3],
        [1; 3; 2]
    );
    (
        // idx 6
        // lib.sort.07
        [1; 2; 3; 4],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [2; 1; 4; 3],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [3; 4; 1; 2]
    );
    (
        // idx 7
        // lib.sort.08
        [4; 3; 2; 1],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [3; 4; 1; 2],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [2; 1; 4; 3]
    );
    (
        // idx 8
        // lib.sort.09
        [1; 3; 2; 4],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [3; 1; 4; 2],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [2; 4; 1; 3]
    );
    (
        // idx 9
        // lib.sort.10
        [2; 4; 1; 3],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [4; 2; 3; 1],
        [4; 3; 2; 1],
        [1; 2; 3; 4],
        [1; 3; 2; 4]
    );
    (
        // idx 10
        // lib.sort.11
        [1; 1; 2; 2],
        [2; 2; 1; 1],
        [1; 1; 2; 2],
        [1; 1; 2; 2],
        [2; 2; 1; 1],
        [1; 1; 2; 2],
        [2; 2; 1; 1]
    );
    (
        // idx 11
        // lib.sort.12
        [2; 1; 2; 1],
        [2; 2; 1; 1],
        [1; 1; 2; 2],
        [1; 1; 2; 2],
        [2; 2; 1; 1],
        [1; 1; 2; 2],
        [2; 2; 1; 1]
    );
    (
        // idx 12
        // lib.sort.13
        [10; 9; 8; 7; 6; 5; 4; 3; 2; 1],
        [10; 9; 8; 7; 6; 5; 4; 3; 2; 1],
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10],
        [7; 8; 5; 6; 9; 10; 3; 4; 1; 2],
        [10; 9; 8; 7; 6; 5; 4; 3; 2; 1],
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10],
        [2; 1; 4; 3; 10; 9; 6; 5; 8; 7]
    );
    (
        // idx 13
        // lib.sort.14
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10],
        [10; 9; 8; 7; 6; 5; 4; 3; 2; 1],
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10],
        [4; 3; 6; 5; 2; 1; 8; 7; 10; 9],
        [10; 9; 8; 7; 6; 5; 4; 3; 2; 1],
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10],
        [9; 10; 7; 8; 1; 2; 5; 6; 3; 4]
    );
    (
        // idx 14
        // lib.sort.15
        [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5],
        [9; 6; 5; 5; 5; 4; 3; 3; 2; 1; 1],
        [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9],
        [9; 5; 6; 2; 1; 1; 3; 3; 4; 5; 5],
        [9; 6; 5; 5; 5; 4; 3; 3; 2; 1; 1],
        [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9],
        [5; 5; 3; 4; 1; 3; 1; 2; 6; 5; 9]
    );
    |]

[<TestCase(0, TestName = "lib.sort.01")>]
[<TestCase(1, TestName = "lib.sort.02")>]
[<TestCase(2, TestName = "lib.sort.03")>]
[<TestCase(3, TestName = "lib.sort.04")>]
[<TestCase(4, TestName = "lib.sort.05")>]
[<TestCase(5, TestName = "lib.sort.06")>]
[<TestCase(6, TestName = "lib.sort.07")>]
[<TestCase(7, TestName = "lib.sort.08")>]
[<TestCase(8, TestName = "lib.sort.09")>]
[<TestCase(9, TestName = "lib.sort.10")>]
[<TestCase(10, TestName = "lib.sort.11")>]
[<TestCase(11, TestName = "lib.sort.12")>]
[<TestCase(12, TestName = "lib.sort.13")>]
[<TestCase(13, TestName = "lib.sort.14")>]
[<TestCase(14, TestName = "lib.sort.15")>]

[<Test>]
let ``List sort`` idx = 
    let (list, _, _, _, _, _, _) = sortValues.[idx]
    let (_, greaterThanResult, _, _, _, _, _) = sortValues.[idx]
    let (_, _, lessThanResult, _, _, _, _) = sortValues.[idx]
    let (_, _, _, equalResult, _, _, _) = sortValues.[idx]
    let (_, _, _, _, greaterThanOrEqualResult, _, _) = sortValues.[idx]
    let (_, _, _, _, _, lessThanOrEqualResult, _) = sortValues.[idx]
    let (_, _, _, _, _, _, notEqualResult) = sortValues.[idx]
    sort (>) list
    |> should equal greaterThanResult
    sort (<) list
    |> should equal lessThanResult
    sort (=) list
    |> should equal equalResult
    sort (>=) list
    |> should equal greaterThanOrEqualResult
    sort (<=) list
    |> should equal lessThanOrEqualResult
    sort (<>) list
    |> should equal notEqualResult

let private subsetValues : (int list * int list * bool)[] = [| 
    (
        // idx 0
        // lib.subset.01
        [], [],
        true
    );
    (
        // idx 1
        // lib.subset.02
        [], [1],
        true
    );
    (
        // idx 2
        // lib.subset.03
        [1], [],
        false
    );
    (
        // idx 3
        // lib.subset.04
        [1], [1],
        true
    );
    (
        // idx 4
        // lib.subset.05
        [1], [2],
        false
    );
    (
        // idx 5
        // lib.subset.06
        [], [1; 2],
        true
    );
    (
        // idx 6
        // lib.subset.07
        [1], [1; 2],
        true
    );
    (
        // idx 7
        // lib.subset.08
        [2], [1; 2],
        true
    );
    (
        // idx 8
        // lib.subset.09
        [1; 2], [1; 2],
        true
    );
    (
        // idx 9
        // lib.subset.10
        [], [2; 1],
        true
    );
    (
        // idx 10
        // lib.subset.11
        [1], [2; 1],
        true
    );
    (
        // idx 11
        // lib.subset.12
        [2], [2; 1],
        true
    );
    (
        // idx 12
        // lib.subset.13
        [1; 2], [2; 1],
        true
    );
    (
        // idx 13
        // lib.subset.14
        [1; 2; 3], [3; 2; 1],
        true
    );
    (
        // idx 14
        // lib.subset.15
        [1; 2; 3], [1; 1; 2; 2; 3; 3],
        true
    );
    (
        // idx 15
        // lib.subset.16
        [1; 2; 3], [1; 2],
        false
    );
    (
        // idx 16
        // lib.subset.17
        [-1; 0; 1], [-2; -1; 0; 1; 2; 3; 4],
        true
    );
    |]

[<TestCase(0, TestName = "lib.subset.01")>]
[<TestCase(1, TestName = "lib.subset.02")>]
[<TestCase(2, TestName = "lib.subset.03")>]
[<TestCase(3, TestName = "lib.subset.04")>]
[<TestCase(4, TestName = "lib.subset.05")>]
[<TestCase(5, TestName = "lib.subset.06")>]
[<TestCase(6, TestName = "lib.subset.07")>]
[<TestCase(7, TestName = "lib.subset.08")>]
[<TestCase(8, TestName = "lib.subset.09")>]
[<TestCase(9, TestName = "lib.subset.10")>]
[<TestCase(10, TestName = "lib.subset.11")>]
[<TestCase(11, TestName = "lib.subset.12")>]
[<TestCase(12, TestName = "lib.subset.13")>]
[<TestCase(13, TestName = "lib.subset.14")>]
[<TestCase(14, TestName = "lib.subset.15")>]
[<TestCase(15, TestName = "lib.subset.16")>]
[<TestCase(16, TestName = "lib.subset.17")>]

[<Test>]
let ``List subset`` idx = 
    let (list1, _, _) = subsetValues.[idx]
    let (_, list2, _) = subsetValues.[idx]
    let (_, _, result) = subsetValues.[idx]
    subset list1 list2
    |> should equal result
    Set.isSubset (Set.ofList list1) (Set.ofList list2)
    |> should equal result

let private subtractValues : (int list * int list * int list)[] = [| 
    (
        // idx 0
        // lib.subtract.01
        [], [],
        []
    );
    (
        // idx 1
        // lib.subtract.02
        [1], [1],
        []
    );
    (
        // idx 2
        // lib.subtract.03
        [1], [2],
        [1]
    );
    (
        // idx 3
        // lib.subtract.04
        [2], [1],
        [2]
    );
    (
        // idx 4
        // lib.subtract.05
        [1; 2], [1],
        [2]
    );
    (
        // idx 5
        // lib.subtract.06
        [1; 2], [2],
        [1]
    );
    (
        // idx 6
        // lib.subtract.07
        [1; 1; 2], [1],
        [2]
    );
    (
        // idx 7
        // lib.subtract.08
        [1; 1; 2], [2],
        [1]
    );
    (
        // idx 8
        // lib.subtract.09
        [1; 1; 2; 2], [1; 2],
        []
    );
    (
        // idx 9
        // lib.subtract.10
        [1; 2; 3], [1],
        [2; 3]
    );
    (
        // idx 10
        // lib.subtract.11
        [1; 2; 3], [2],
        [1; 3]
    );
    (
        // idx 11
        // lib.subtract.12
        [1; 2; 3], [2],
        [1; 3]
    );
    (
        // idx 12
        // lib.subtract.13
        [1; 2; 3], [3],
        [1; 2]
    );
    (
        // idx 13
        // lib.subtract.14
        [3; 2; 1], [1],
        [2; 3]
    );
    (
        // idx 14
        // lib.subtract.15
        [3; 2; 1], [2],
        [1; 3]
    );
    (
        // idx 15
        // lib.subtract.16
        [3; 2; 1], [1],
        [2; 3]
    );
    (
        // idx 16
        // lib.subtract.17
        [1; 2; 3], [1; 2],
        [3]
    );
    (
        // idx 17
        // lib.subtract.18
        [1; 2; 3], [1; 3],
        [2]
    );
    (
        // idx 18
        // lib.subtract.19
        [1; 2; 3], [2; 3],
        [1]
    );
    (
        // idx 19
        // lib.subtract.20
        [3; 2; 1], [2; 3],
        [1]
    );
    (
        // idx 20
        // lib.subtract.21
        [3; 2; 1], [3; 2],
        [1]
    );
    |]

[<TestCase(0, TestName = "lib.subtract.01")>]
[<TestCase(1, TestName = "lib.subtract.02")>]
[<TestCase(2, TestName = "lib.subtract.03")>]
[<TestCase(3, TestName = "lib.subtract.04")>]
[<TestCase(4, TestName = "lib.subtract.05")>]
[<TestCase(5, TestName = "lib.subtract.06")>]
[<TestCase(6, TestName = "lib.subtract.07")>]
[<TestCase(7, TestName = "lib.subtract.08")>]
[<TestCase(8, TestName = "lib.subtract.09")>]
[<TestCase(9, TestName = "lib.subtract.10")>]
[<TestCase(10, TestName = "lib.subtract.11")>]
[<TestCase(11, TestName = "lib.subtract.12")>]
[<TestCase(12, TestName = "lib.subtract.13")>]
[<TestCase(13, TestName = "lib.subtract.14")>]
[<TestCase(14, TestName = "lib.subtract.15")>]
[<TestCase(15, TestName = "lib.subtract.16")>]
[<TestCase(16, TestName = "lib.subtract.17")>]
[<TestCase(17, TestName = "lib.subtract.18")>]
[<TestCase(18, TestName = "lib.subtract.19")>]
[<TestCase(19, TestName = "lib.subtract.20")>]
[<TestCase(20, TestName = "lib.subtract.21")>]

[<Test>]
let ``List subtract`` idx = 
    let (list1, _, _) = subtractValues.[idx]
    let (_, list2, _) = subtractValues.[idx]
    let (_, _, result) = subtractValues.[idx]
    subtract list1 list2
    |> should equal result
    Set.difference (Set.ofList list1) (Set.ofList list2)
    |> should equal (Set.ofList result)

let private tailValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.tail.01
        // System.ArgumentException - The input list was empty.
        [],
        [-99]  // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.tail.02
        [1],
        []
    );
    (
        // idx 2
        // lib.tail.03
        [1; 2],
        [2]
    );
    (
        // idx 3
        // lib.tail.04
        [1; 2; 3],
        [2; 3]
    );
    (
        // idx 4
        // lib.tail.05
        [3; 2; 1],
        [2; 1]
    )
    |]

[<TestCase(0, TestName = "lib.tail.01", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(1, TestName = "lib.tail.02")>]
[<TestCase(2, TestName = "lib.tail.03")>]
[<TestCase(3, TestName = "lib.tail.04")>]
[<TestCase(4, TestName = "lib.tail.05")>]

[<Test>]
let ``List tail`` idx = 
    let (list, _) = tailValues.[idx]
    let (_, result) = tailValues.[idx]
    List.tail list
    |> should equal result
    tl list 
    |> should equal result

// This Test is to show that they both return
// different exceptions when given an empty list.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// tl exception test case.

[<TestCase(0, TestName = "lib.tlException.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="tl")>]

[<Test>]
let ``List tl exception`` idx = 
    let (list, _) = tailValues.[idx]
    let (_, result) = tailValues.[idx]
    tl list 
    |> should equal result

let private unionValues : (int list * int list * int list)[] = [| 
    (
        // idx 0
        // lib.union.01
        [], [],
        []
    );
    (
        // idx 1
        // lib.union.02
        [], [1],
        [1]
    );
    (
        // idx 2
        // lib.union.03
        [1], [],
        [1]
    );
    (
        // idx 3
        // lib.union.04
        [1], [1],
        [1]
    );
    (
        // idx 4
        // lib.union.05
        [1; 1], [],
        [1]
    );
    (
        // idx 5
        // lib.union.06
        [], [1; 1],
        [1]
    );
    (
        // idx 6
        // lib.union.07
        [1; 1], [1; 1],
        [1]
    );
    (
        // idx 7
        // lib.union.08
        [1], [2],
        [1; 2]
    );
    (
        // idx 8
        // lib.union.09
        [2], [1],
        [1; 2]
    );
    (
        // idx 9
        // lib.union.10
        [1; 2], [1],
        [1; 2]
    );
    (
        // idx 10
        // lib.union.11
        [1; 2], [2],
        [1; 2]
    );
    (
        // idx 11
        // lib.union.12
        [1; 1; 2], [1],
        [1; 2]
    );
    (
        // idx 12
        // lib.union.13
        [1; 1; 2], [2],
        [1; 2]
    );
    (
        // idx 13
        // lib.union.14
        [1; 1; 2; 2], [1; 2],
        [1; 2]
    );
    (
        // idx 14
        // lib.union.15
        [1; 2; 3], [1],
        [1; 2; 3]
    );
    (
        // idx 15
        // lib.union.16
        [1; 2; 3], [2],
        [1; 2; 3]
    );
    (
        // idx 16
        // lib.union.17
        [1; 2; 3], [3],
        [1; 2; 3]
    );
    (
        // idx 17
        // lib.union.18
        [3; 2; 1], [1],
        [1; 2; 3]
    );
    (
        // idx 18
        // lib.union.19
        [3; 2; 1], [2],
        [1; 2; 3]
    );
    (
        // idx 19
        // lib.union.20
        [3; 2; 1], [3],
        [1; 2; 3]
    );
    (
        // idx 20
        // lib.union.21
        [3; 2; 1], [1; 2],
        [1; 2; 3]
    );
    (
        // idx 21
        // lib.union.22
        [1; 2; 3], [1; 2],
        [1; 2; 3]
    );
    (
        // idx 22
        // lib.union.23
        [1; 2; 3], [1; 3],
        [1; 2; 3]
    );
    (
        // idx 23
        // lib.union.24
        [1; 2; 3], [2; 3],
        [1; 2; 3]
    );
    (
        // idx 24
        // lib.union.25
        [3; 2; 1], [2; 3],
        [1; 2; 3]
    );
    (
        // idx 25
        // lib.union.26
        [3; 2; 1], [3; 2],
        [1; 2; 3]
    );
    (
        // idx 26
        // lib.union.27
        [9; 7; 5; 3; 1], [2; 4; 6; 8; 10],
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
    );
    (
        // idx 27
        // lib.union.28
        [1; 7; 9; 3; 5], [10; 6; 2; 8; 4],
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
    );
    |]

[<TestCase(0, TestName = "lib.union.01")>]
[<TestCase(1, TestName = "lib.union.02")>]
[<TestCase(2, TestName = "lib.union.03")>]
[<TestCase(3, TestName = "lib.union.04")>]
[<TestCase(4, TestName = "lib.union.05")>]
[<TestCase(5, TestName = "lib.union.06")>]
[<TestCase(6, TestName = "lib.union.07")>]
[<TestCase(7, TestName = "lib.union.08")>]
[<TestCase(8, TestName = "lib.union.09")>]
[<TestCase(9, TestName = "lib.union.10")>]
[<TestCase(10, TestName = "lib.union.11")>]
[<TestCase(11, TestName = "lib.union.12")>]
[<TestCase(12, TestName = "lib.union.13")>]
[<TestCase(13, TestName = "lib.union.14")>]
[<TestCase(14, TestName = "lib.union.15")>]
[<TestCase(15, TestName = "lib.union.16")>]
[<TestCase(16, TestName = "lib.union.17")>]
[<TestCase(17, TestName = "lib.union.18")>]
[<TestCase(18, TestName = "lib.union.19")>]
[<TestCase(19, TestName = "lib.union.20")>]
[<TestCase(20, TestName = "lib.union.21")>]
[<TestCase(21, TestName = "lib.union.22")>]
[<TestCase(22, TestName = "lib.union.23")>]
[<TestCase(23, TestName = "lib.union.24")>]
[<TestCase(24, TestName = "lib.union.25")>]
[<TestCase(25, TestName = "lib.union.26")>]
[<TestCase(26, TestName = "lib.union.27")>]
[<TestCase(27, TestName = "lib.union.28")>]

[<Test>]
let ``List union`` idx = 
    let (list1, _, _) = unionValues.[idx]
    let (_, list2, _) = unionValues.[idx]
    let (_, _, result) = unionValues.[idx]
    union list1 list2
    |> should equal result
    Set.union (Set.ofList list1) (Set.ofList list2)
    |> should equal (Set.ofList result)

let private unionsValues : (int list list * int list)[] = [| 
    (
        // idx 0
        // lib.unions.01
        [],
        []
    ); 
    (
        // idx 1
        // lib.unions.02
        [ [] ],
        []
    ); 
    (
        // idx 2
        // lib.unions.03
        [ [1] ],
        [1]
    );
    (
        // idx 3
        // lib.unions.04
        [ [1; 2] ],
        [1; 2]
    );
    (
        // idx 4
        // lib.unions.05
        [ [2; 1] ],
        [1; 2]
    );
    (
        // idx 5
        // lib.unions.06
        [ [1; 2; 3] ],
        [1; 2; 3]
    );
    (
        // idx 6
        // lib.unions.07
        [ [3; 2; 1] ],
        [1; 2; 3]
    );
    (
        // idx 7
        // lib.unions.08
        [ []; [] ],
        []
    ); 
    (
        // idx 8
        // lib.unions.09
        [ []; [1] ],
        [1]
    ); 
    (
        // idx 9
        // lib.unions.10
        [ [1]; [] ],
        [1]
    ); 
    (
        // idx 10
        // lib.unions.11
        [ [1]; [1] ],
        [1]
    ); 
    (
        // idx 11
        // lib.unions.12
        [ [1; 2]; [1] ],
        [1; 2]
    ); 
    (
        // idx 12
        // lib.unions.13
        [ [2; 1]; [1] ],
        [1; 2]
    ); 
    (
        // idx 13
        // lib.unions.14
        [ [1]; [2; 1] ],
        [1; 2]
    ); 
    (
        // idx 14
        // lib.unions.15
        [ [1]; [2; 1] ],
        [1; 2]
    ); 
    (
        // idx 15
        // lib.unions.16
        [ [1]; [1; 2; 3] ],
        [1; 2; 3]
    ); 
    (
        // idx 16
        // lib.unions.17
        [ [2]; [1; 2; 3] ],
        [1; 2; 3]
    ); 
    (
        // idx 17
        // lib.unions.18
        [ [3]; [1; 2; 3] ],
        [1; 2; 3]
    ); 
    (
        // idx 18
        // lib.unions.19
        [ [1]; [3; 2; 1] ],
        [1; 2; 3]
    ); 
    (
        // idx 19
        // lib.unions.20
        [ [2]; [3; 2; 1] ],
        [1; 2; 3]
    ); 
    (
        // idx 20
        // lib.unions.21
        [ [3]; [3; 2; 1] ],
        [1; 2; 3]
    ); 
    (
        // idx 21
        // lib.unions.22
        [ [1; 2]; [1; 2] ],
        [1; 2]
    ); 
    (
        // idx 22
        // lib.unions.23
        [ [1; 2]; [2; 1] ],
        [1; 2]
    ); 
    (
        // idx 23
        // lib.unions.24
        [ [1; 1; 1]; [2; 2; 2] ],
        [1; 2]
    ); 
    (
        // idx 24
        // lib.unions.25
        [ [1; 2; 1]; [2; 1; 2] ],
        [1; 2]
    ); 
    (
        // idx 25
        // lib.unions.26
        [ []; []; [] ],
        []
    ); 
    (
        // idx 26
        // lib.unions.27
        [ []; []; [1] ],
        [1]
    ); 
    (
        // idx 27
        // lib.unions.28
        [ []; [1]; [] ],
        [1]
    ); 
    (
        // idx 28
        // lib.unions.29
        [ [1]; []; [] ],
        [1]
    ); 
    (
        // idx 29
        // lib.unions.30
        [ [1]; [2]; [] ],
        [1; 2]
    ); 
    (
        // idx 30
        // lib.unions.31
        [ [1]; []; [2] ],
        [1; 2]
    ); 
    (
        // idx 31
        // lib.unions.32
        [ [2]; []; [1] ],
        [1; 2]
    ); 
    (
        // idx 32
        // lib.unions.33
        [ []; [1]; [2] ],
        [1; 2]
    ); 
    (
        // idx 33
        // lib.unions.34
        [ [1]; [1]; [2] ],
        [1; 2]
    ); 
    (
        // idx 34
        // lib.unions.35
        [ []; []; [2; 1] ],
        [1; 2]
    ); 
    (
        // idx 35
        // lib.unions.36
        [ [1; 1]; []; [2; 2] ],
        [1; 2]
    ); 
    (
        // idx 36
        // lib.unions.37
        [ [1; 1]; [1; 2]; [2; 2] ],
        [1; 2]
    ); 
    (
        // idx 37
        // lib.unions.38
        [ [1; 1]; [2; 1]; [2; 2] ],
        [1; 2]
    ); 
    (
        // idx 38
        // lib.unions.39
        [ []; []; [1; 2; 1; 2] ],
        [1; 2]
    ); 
    (
        // idx 39
        // lib.unions.40
        [ [1]; [2]; [3] ],
        [1; 2; 3]
    ); 
    (
        // idx 40
        // lib.unions.41
        [ [3]; [2]; [1] ],
        [1; 2; 3]
    ); 
    (
        // idx 41
        // lib.unions.42
        [ [2]; [3]; [1] ],
        [1; 2; 3]
    ); 
    (
        // idx 42
        // lib.unions.43
        [ [1; 2; 3]; []; [] ],
        [1; 2; 3]
    ); 
    (
        // idx 43
        // lib.unions.44
        [ [1]; []; [2; 3] ],
        [1; 2; 3]
    ); 
    (
        // idx 44
        // lib.unions.45
        [ [1]; []; [3; 2] ],
        [1; 2; 3]
    ); 
    (
        // idx 45
        // lib.unions.46
        [ []; [3; 2; 1]; [] ],
        [1; 2; 3]
    ); 
    (
        // idx 46
        // lib.unions.47
        [ []; []; []; [] ],
        []
    ); 
    (
        // idx 47
        // lib.unions.48
        [ [1]; []; []; [] ],
        [1]
    ); 
    (
        // idx 48
        // lib.unions.49
        [ []; [1]; []; [] ],
        [1]
    ); 
    (
        // idx 49
        // lib.unions.50
        [ []; []; [1]; [] ],
        [1]
    );
    (
        // idx 50
        // lib.unions.51
        [ []; []; []; [1] ],
        [1]
    );
    (
        // idx 51
        // lib.unions.52
        [ []; []; [1]; [1] ],
        [1]
    );
    (
        // idx 52
        // lib.unions.53
        [ []; [1]; [1]; [1] ],
        [1]
    );
    (
        // idx 53
        // lib.unions.54
        [ [1]; [1]; [1]; [1] ],
        [1]
    );
    (
        // idx 54
        // lib.unions.55
        [ [1; 1]; [1; 1]; [1; 1]; [1; 1] ],
        [1]
    );
    (
        // idx 55
        // lib.unions.56
        [ [1; 2]; [1; 2]; [1; 2]; [1; 2] ],
        [1; 2]
    );
    (
        // idx 56
        // lib.unions.57
        [ [1; 2]; []; []; [2; 1] ],
        [1; 2]
    );
    (
        // idx 57
        // lib.unions.58
        [ []; [2; 1]; [1; 2]; [] ],
        [1; 2]
    );
    (
        // idx 58
        // lib.unions.59
        [ [1]; [2; 1]; [1; 2]; [2] ],
        [1; 2]
    );
    (
        // idx 59
        // lib.unions.60
        [ [1]; [2]; [2]; [2] ],
        [1; 2]
    );
    (
        // idx 60
        // lib.unions.61
        [ [2]; [2]; [2]; [1] ],
        [1; 2]
    );
    (
        // idx 61
        // lib.unions.62
        [ [7; 8]; [5; 6]; [3; 4]; [1; 2] ],
        [1; 2; 3; 4; 5; 6; 7; 8]
    );
    |]
    
[<TestCase(0, TestName = "lib.unions.01")>]
[<TestCase(1, TestName = "lib.unions.02")>]
[<TestCase(2, TestName = "lib.unions.03")>]
[<TestCase(3, TestName = "lib.unions.04")>]
[<TestCase(4, TestName = "lib.unions.05")>]
[<TestCase(5, TestName = "lib.unions.06")>]
[<TestCase(6, TestName = "lib.unions.07")>]
[<TestCase(7, TestName = "lib.unions.08")>]
[<TestCase(8, TestName = "lib.unions.09")>]
[<TestCase(9, TestName = "lib.unions.10")>]
[<TestCase(10, TestName = "lib.unions.11")>]
[<TestCase(11, TestName = "lib.unions.12")>]
[<TestCase(12, TestName = "lib.unions.13")>]
[<TestCase(13, TestName = "lib.unions.14")>]
[<TestCase(14, TestName = "lib.unions.15")>]
[<TestCase(15, TestName = "lib.unions.16")>]
[<TestCase(16, TestName = "lib.unions.17")>]
[<TestCase(17, TestName = "lib.unions.18")>]
[<TestCase(18, TestName = "lib.unions.19")>]
[<TestCase(19, TestName = "lib.unions.20")>]
[<TestCase(20, TestName = "lib.unions.21")>]
[<TestCase(21, TestName = "lib.unions.22")>]
[<TestCase(22, TestName = "lib.unions.23")>]
[<TestCase(23, TestName = "lib.unions.24")>]
[<TestCase(24, TestName = "lib.unions.25")>]
[<TestCase(25, TestName = "lib.unions.26")>]
[<TestCase(26, TestName = "lib.unions.27")>]
[<TestCase(27, TestName = "lib.unions.28")>]
[<TestCase(28, TestName = "lib.unions.29")>]
[<TestCase(29, TestName = "lib.unions.30")>]
[<TestCase(30, TestName = "lib.unions.31")>]
[<TestCase(31, TestName = "lib.unions.32")>]
[<TestCase(32, TestName = "lib.unions.33")>]
[<TestCase(33, TestName = "lib.unions.34")>]
[<TestCase(34, TestName = "lib.unions.35")>]
[<TestCase(35, TestName = "lib.unions.36")>]
[<TestCase(36, TestName = "lib.unions.37")>]
[<TestCase(37, TestName = "lib.unions.38")>]
[<TestCase(38, TestName = "lib.unions.39")>]
[<TestCase(39, TestName = "lib.unions.40")>]
[<TestCase(40, TestName = "lib.unions.41")>]
[<TestCase(41, TestName = "lib.unions.42")>]
[<TestCase(42, TestName = "lib.unions.43")>]
[<TestCase(43, TestName = "lib.unions.44")>]
[<TestCase(44, TestName = "lib.unions.45")>]
[<TestCase(45, TestName = "lib.unions.46")>]
[<TestCase(46, TestName = "lib.unions.47")>]
[<TestCase(47, TestName = "lib.unions.48")>]
[<TestCase(48, TestName = "lib.unions.49")>]
[<TestCase(49, TestName = "lib.unions.50")>]
[<TestCase(50, TestName = "lib.unions.51")>]
[<TestCase(51, TestName = "lib.unions.52")>]
[<TestCase(52, TestName = "lib.unions.53")>]
[<TestCase(53, TestName = "lib.unions.54")>]
[<TestCase(54, TestName = "lib.unions.55")>]
[<TestCase(55, TestName = "lib.unions.56")>]
[<TestCase(56, TestName = "lib.unions.57")>]
[<TestCase(57, TestName = "lib.unions.58")>]
[<TestCase(58, TestName = "lib.unions.59")>]
[<TestCase(59, TestName = "lib.unions.60")>]
[<TestCase(60, TestName = "lib.unions.61")>]
[<TestCase(61, TestName = "lib.unions.62")>]

[<Test>]
let ``List unions`` idx = 
    let (lists, _) = unionsValues.[idx]
    let (_, result) = unionsValues.[idx]
    unions lists 
    |> should equal result
    let listOfListToSeqOfSet lists =
        List.fold (fun acc elem ->  
                Set.add (Set.ofList elem) acc)
            Set.empty lists
        |> Set.toSeq
    Set.unionMany (listOfListToSeqOfSet lists)
    |> should equal (Set.ofList result)

let private unzipValues : ((int * int) list * (int list * int list))[] = [| 
    (
        // idx 0
        // lib.unzip.01
        [],
        ([], [])
    );
    (
        // idx 1
        // lib.unzip.02
        [(1, 2)],
        ([1], [2])
    );
    (
        // idx 2
        // lib.unzip.03
        [(1, 2); (3, 4)],
        ([1; 3], [2; 4])
    );
    (
        // idx 3
        // lib.unzip.04
        [(1, 2); (3, 4); (5, 6)],
        ([1; 3; 5], [2; 4; 6])
    ); 
    |]
    
[<TestCase(0, TestName = "lib.unzip.01")>]
[<TestCase(1, TestName = "lib.unzip.02")>]
[<TestCase(2, TestName = "lib.unzip.03")>]
[<TestCase(3, TestName = "lib.unzip.04")>]

[<Test>]
let ``List unzip`` idx = 
    let (list, _) = unzipValues.[idx]
    let (_, result) = unzipValues.[idx]
    unzip list
    |> should equal result
    List.unzip list
    |> should equal result

let private zipValues : (int list * int list * (int * int) list)[] = [| 
    (
        // idx 0
        // lib.zip.01
        [], [],
        []
    );
    (
        // idx 1
        // lib.zip.02
        // F#:   System.ArgumentException - The lists had different lengths.
        // OCaml: System.Exception - zip
        [], [1],
        [(-99, -99)] // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.zip.03
        // F#: System.ArgumentException - The lists had different lengths.
        // OCaml: System.Exception - zip
        [1], [],
        [(-99, -99)] // Dummy value used as place holder
    );
    (
        // idx 3
        // lib.zip.04
        [1], [1],
        [(1,1)]
    );
    (
        // idx 4
        // lib.zip.05
        [1], [2],
        [(1, 2)]
    );
    (
        // idx 5
        // lib.zip.06
        [1; 3], [2; 4],
        [(1, 2); (3, 4)]
    );
    (
        // idx 6
        // lib.zip.07
        [1; 3; 5], [2; 4; 6],
        [(1, 2); (3, 4); (5, 6)]
    ); 
    |]
    
[<TestCase(0, TestName = "lib.zip.01")>]
[<TestCase(1, TestName = "lib.zip.02",ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(2, TestName = "lib.zip.03",ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(3, TestName = "lib.zip.04")>]
[<TestCase(4, TestName = "lib.zip.05")>]
[<TestCase(5, TestName = "lib.zip.06")>]
[<TestCase(6, TestName = "lib.zip.07")>]

[<Test>]
let ``List zip`` idx = 
    let (list1, _, _) = zipValues.[idx]
    let (_, list2, _) = zipValues.[idx]
    let (_, _, result) = zipValues.[idx]
    List.zip list1 list2
    |> should equal result
    zip list1 list2
    |> should equal result

// This Test is to show that they both return
// different exceptions when the list have different lengths.
//
// Since an exception will end a test case, one can not
// run back to back functions returning exceptions
// for one test case, thus a second test for the 
// zip exception test case.

[<TestCase(1, TestName = "lib.zipException.01",ExpectedException=typeof<System.Exception>, ExpectedMessage="zip")>]
[<TestCase(2, TestName = "lib.zipException.02",ExpectedException=typeof<System.Exception>, ExpectedMessage="zip")>]

[<Test>]
let ``List zip exception`` idx = 
    let (list1, _, _) = zipValues.[idx]
    let (_, list2, _) = zipValues.[idx]
    let (_, _, result) = zipValues.[idx]
    zip list1 list2
    |> should equal result

let private allnonemptysubsetsValues : (int list * int list list)[] = [| 
    (
        // idx 0
        // lib.allnonemptysubsets.01
        [],
        [ ]
    );
    (
        // idx 1
        // lib.allnonemptysubsets.02
        [1],
        [ [1] ]
    );
    (
        // idx 2
        // lib.allnonemptysubsets.03
        [1; 2],
        [ [1]; [1; 2]; [2] ]
    );
    (
        // idx 3
        // lib.allnonemptysubsets.04
        [1; 2; 3],
        [[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]
    ); 
    |]
    
[<TestCase(0, TestName = "lib.allnonemptysubsets.01")>]
[<TestCase(1, TestName = "lib.allnonemptysubsets.02")>]
[<TestCase(2, TestName = "lib.allnonemptysubsets.03")>]
[<TestCase(3, TestName = "lib.allnonemptysubsets.04")>]

[<Test>]
let ``List allnonemptysubsets`` idx = 
    let (list, _) = allnonemptysubsetsValues.[idx]
    let (_, result) = allnonemptysubsetsValues.[idx]
    allnonemptysubsets list
    |> should equal result

let private allpairsValues : (int list * int list * int list)[] = [| 
    (
        // idx 0
        // lib.allpairs.01
        [], [],
        []
    );
    (
        // idx 1
        // lib.allpairs.02
        [], [1],
        []
    );
    (
        // idx 2
        // lib.allpairs.03
        [1], [],
        []
    );
    (
        // idx 3
        // lib.allpairs.04
        [1], [1],
        [1]
    );
    (
        // idx 4
        // lib.allpairs.05
        [1], [2],
        [2]
    );
    (
        // idx 5
        // lib.allpairs.06
        [1; 2], [1; 2],
        [1; 2; 2; 4]
    );
    (
        // idx 6
        // lib.allpairs.07
        [1; 2], [2; 3],
        [2; 3; 4; 6]
    );
    (
        // idx 7
        // lib.allpairs.08
        [1; 2; 3], [1],
        [1; 2; 3]
    );
    (
        // idx 8
        // lib.allpairs.09
        [1; 2; 3], [2],
        [2; 4; 6]
    );
    (
        // idx 9
        // lib.allpairs.10
        [1; 2; 3], [3],
        [3; 6; 9]
    );
    (
        // idx 10
        // lib.allpairs.11
        [1; 2; 3], [1; 2],
        [1; 2; 2; 4; 3; 6]
    );
    (
        // idx 11
        // lib.allpairs.12
        [1; 2; 3], [2; 3],
        [2; 3; 4; 6; 6; 9]
    );
    (
        // idx 12
        // lib.allpairs.13
        [1; 2; 3], [1; 2; 3],
        [1; 2; 3; 2; 4; 6; 3; 6; 9]
    );
    (
        // idx 13
        // lib.allpairs.14
        [1; 2; 3], [3; 2; 1],
        [3; 2; 1; 6; 4; 2; 9; 6; 3]
    );
    (
        // idx 14
        // lib.allpairs.15
        [1; 2; 3], [1; 1; 2; 2],
        [1; 1; 2; 2; 2; 2; 4; 4; 3; 3; 6; 6]
    );
    (
        // idx 15
        // lib.allpairs.16
        [1; 2; 3], [1; 1; 2; 2; 4; 4],
        [1; 1; 2; 2; 4; 4; 2; 2; 4; 4; 8; 8; 3; 3; 6; 6; 12; 12]
    );
    (
        // idx 16
        // lib.allpairs.17
        [1; 2; 3], [-2; -1; 0; 1; 2; 3; 4],
        [-2; -1; 0; 1; 2; 3; 4; -4; -2; 0; 2; 4; 6; 8; -6; -3; 0; 3; 6; 9; 12]
    );
    |]
    
[<TestCase(0, TestName = "lib.allpairs.01")>]
[<TestCase(1, TestName = "lib.allpairs.02")>]
[<TestCase(2, TestName = "lib.allpairs.03")>]
[<TestCase(3, TestName = "lib.allpairs.04")>]
[<TestCase(4, TestName = "lib.allpairs.05")>]
[<TestCase(5, TestName = "lib.allpairs.06")>]
[<TestCase(6, TestName = "lib.allpairs.07")>]
[<TestCase(7, TestName = "lib.allpairs.08")>]
[<TestCase(8, TestName = "lib.allpairs.09")>]
[<TestCase(9, TestName = "lib.allpairs.10")>]
[<TestCase(10, TestName = "lib.allpairs.11")>]
[<TestCase(11, TestName = "lib.allpairs.12")>]
[<TestCase(12, TestName = "lib.allpairs.13")>]
[<TestCase(13, TestName = "lib.allpairs.14")>]
[<TestCase(14, TestName = "lib.allpairs.15")>]
[<TestCase(15, TestName = "lib.allpairs.16")>]
[<TestCase(16, TestName = "lib.allpairs.17")>]

[<Test>]
let ``List allpairs`` idx = 
    let (list1, _, _) = allpairsValues.[idx]
    let (_, list2, _) = allpairsValues.[idx]
    let (_, _, result) = allpairsValues.[idx]
    allpairs (fun x y -> x * y) list1 list2
    |> should equal result

let private allsetsValues : (int * int list * int list list)[] = [| 
    (
        // idx 0
        // lib.allsets.01
        0, [],
        [ [] ]
    );
    (
        // idx 1
        // lib.allsets.02
        0, [1],
        [ [] ]
    );
    (
        // idx 2
        // lib.allsets.03
        0, [1; 2],
        [ [] ]
    );
    (
        // idx 3
        // lib.allsets.04
        0, [1; 2; 3],
        [ [] ]
    ); 
    (
        // idx 4
        // lib.allsets.05
        1, [],
        [ ]
    );
    (
        // idx 5
        // lib.allsets.06
        1, [1],
        [ [1] ]
    );
    (
        // idx 6
        // lib.allsets.07
        1, [1; 2],
        [ [1]; [2] ]
    );
    (
        // idx 7
        // lib.allsets.08
        1, [1; 2; 3],
        [ [1]; [2]; [3] ]
    ); 
    (
        // idx 8
        // lib.allsets.09
        2, [],
        [ ]
    );
    (
        // idx 9
        // lib.allsets.10
        2, [1],
        []
    );
    (
        // idx 10
        // lib.allsets.11
        2, [1; 2],
        [ [1; 2] ]
    );
    (
        // idx 11
        // lib.allsets.12
        2, [1; 2; 3],
        [ [1; 2]; [1; 3]; [2; 3] ]
    ); 
    (
        // idx 12
        // lib.allsets.13
        3, [],
        [ ]
    );
    (
        // idx 13
        // lib.allsets.14
        3, [1],
        [ ]
    );
    (
        // idx 14
        // lib.allsets.15
        3, [1; 2],
        [ ]
    );
    (
        // idx 15
        // lib.allsets.16
        3, [1; 2; 3],
        [ [1; 2; 3] ]
    ); 
    |]
    
[<TestCase(0, TestName = "lib.allsets.01")>]
[<TestCase(1, TestName = "lib.allsets.02")>]
[<TestCase(2, TestName = "lib.allsets.03")>]
[<TestCase(3, TestName = "lib.allsets.04")>]
[<TestCase(4, TestName = "lib.allsets.05")>]
[<TestCase(5, TestName = "lib.allsets.06")>]
[<TestCase(6, TestName = "lib.allsets.07")>]
[<TestCase(7, TestName = "lib.allsets.08")>]
[<TestCase(8, TestName = "lib.allsets.09")>]
[<TestCase(9, TestName = "lib.allsets.10")>]
[<TestCase(10, TestName = "lib.allsets.11")>]
[<TestCase(11, TestName = "lib.allsets.12")>]
[<TestCase(12, TestName = "lib.allsets.13")>]
[<TestCase(13, TestName = "lib.allsets.14")>]
[<TestCase(14, TestName = "lib.allsets.15")>]
[<TestCase(15, TestName = "lib.allsets.16")>]

[<Test>]
let ``List allsets`` idx = 
    let (size, _, _) = allsetsValues.[idx]
    let (_, list, _) = allsetsValues.[idx]
    let (_, _, result) = allsetsValues.[idx]
    allsets size list
    |> should equal result

let private allsubsetsValues : (int list * int list list)[] = [| 
    (
        // idx 0
        // lib.allsubsets.01
        [],
        [ [] ]
    );
    (
        // idx 1
        // lib.allsubsets.02
        [1],
        [ []; [1] ]
    );
    (
        // idx 2
        // lib.allsubsets.03
        [1; 2],
        [ []; [1]; [1; 2]; [2] ]
    );
    (
        // idx 3
        // lib.allsubsets.04
        [1; 2; 3],
        [ []; [1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3] ]
    ); 
    |]
    
[<TestCase(0, TestName = "lib.allsubsets.01")>]
[<TestCase(1, TestName = "lib.allsubsets.02")>]
[<TestCase(2, TestName = "lib.allsubsets.03")>]
[<TestCase(3, TestName = "lib.allsubsets.04")>]

[<Test>]
let ``List allsubsets`` idx = 
    let (list, _) = allsubsetsValues.[idx]
    let (_, result) = allsubsetsValues.[idx]
    allsubsets list
    |> should equal result

let private gcd_numValues : (num * num * num)[] = [| 
    (
        // idx 0
        // lib.gcd_num.01
        (num_of_int 0), (num_of_int 0),
        (num_of_int 0)
    );
    (
        // idx 1
        // lib.gcd_num.02
        (num_of_int 0), (num_of_int 1),
        (num_of_int 1)
    );
    (
        // idx 2
        // lib.gcd_num.03
        (num_of_int 0), (num_of_int 2),
        (num_of_int 2)
    );
    (
        // idx 3
        // lib.gcd_num.04
        (num_of_int 1), (num_of_int 0),
        (num_of_int 1)
    );
    (
        // idx 4
        // lib.gcd_num.05
        (num_of_int 1), (num_of_int 1),
        (num_of_int 1)
    );
    (
        // idx 5
        // lib.gcd_num.06
        (num_of_int 1), (num_of_int 2),
        (num_of_int 1)
    );
    (
        // idx 6
        // lib.gcd_num.07
        (num_of_int 2), (num_of_int 0),
        (num_of_int 2)
    );
    (
        // idx 7
        // lib.gcd_num.08
        (num_of_int 2), (num_of_int 1),
        (num_of_int 1)
    );
    (
        // idx 8
        // lib.gcd_num.09
        (num_of_int 2), (num_of_int 2),
        (num_of_int 2)
    );
    (
        // idx 9
        // lib.gcd_num.10
        (num_of_int 2), (num_of_int 3),
        (num_of_int 1)
    );
    (
        // idx 10
        // lib.gcd_num.11
        (num_of_int 2), (num_of_int 4),
        (num_of_int 2)
    );
    (
        // idx 11
        // lib.gcd_num.12
        (num_of_int 2), (num_of_int 5),
        (num_of_int 1)
    );
    (
        // idx 12
        // lib.gcd_num.13
        (num_of_int 2), (num_of_int 6),
        (num_of_int 2)
    );
    (
        // idx 13
        // lib.gcd_num.14
        (num_of_int 3), (num_of_int 0),
        (num_of_int 3)
    );
    (
        // idx 14
        // lib.gcd_num.15
        (num_of_int 3), (num_of_int 1),
        (num_of_int 1)
    );
    (
        // idx 15
        // lib.gcd_num.16
        (num_of_int 3), (num_of_int 2),
        (num_of_int 1)
    );
    (
        // idx 16
        // lib.gcd_num.17
        (num_of_int 3), (num_of_int 3),
        (num_of_int 3)
    );
    (
        // idx 17
        // lib.gcd_num.18
        (num_of_int 3), (num_of_int 4),
        (num_of_int 1)
    );
    (
        // idx 18
        // lib.gcd_num.19
        (num_of_int 3), (num_of_int 5),
        (num_of_int 1)
    );
    (
        // idx 19
        // lib.gcd_num.20
        (num_of_int 3), (num_of_int 6),
        (num_of_int 3)
    );
    |]
    
[<TestCase(0, TestName = "lib.gcd_num.01")>]
[<TestCase(1, TestName = "lib.gcd_num.02")>]
[<TestCase(2, TestName = "lib.gcd_num.03")>]
[<TestCase(3, TestName = "lib.gcd_num.04")>]
[<TestCase(4, TestName = "lib.gcd_num.05")>]
[<TestCase(5, TestName = "lib.gcd_num.06")>]
[<TestCase(6, TestName = "lib.gcd_num.07")>]
[<TestCase(7, TestName = "lib.gcd_num.08")>]
[<TestCase(8, TestName = "lib.gcd_num.09")>]
[<TestCase(9, TestName = "lib.gcd_num.10")>]
[<TestCase(10, TestName = "lib.gcd_num.11")>]
[<TestCase(11, TestName = "lib.gcd_num.12")>]
[<TestCase(12, TestName = "lib.gcd_num.13")>]
[<TestCase(13, TestName = "lib.gcd_num.14")>]
[<TestCase(14, TestName = "lib.gcd_num.15")>]
[<TestCase(15, TestName = "lib.gcd_num.16")>]
[<TestCase(16, TestName = "lib.gcd_num.17")>]
[<TestCase(17, TestName = "lib.gcd_num.18")>]
[<TestCase(18, TestName = "lib.gcd_num.19")>]
[<TestCase(19, TestName = "lib.gcd_num.20")>]

[<Test>]
let ``math gcd_num`` idx = 
    let (value1, _, _) = gcd_numValues.[idx]
    let (_, value2, _) = gcd_numValues.[idx]
    let (_, _, result) = gcd_numValues.[idx]
    gcd_num value1 value2
    |> should equal result

let private lcm_numValues : (num * num * num)[] = [| 
    (
        // idx 0
        // lib.lcm_num.01
        (num_of_int 0), (num_of_int 0),
        (num_of_int -99) // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.lcm_num.02
        (num_of_int 0), (num_of_int 1),
        (num_of_int 0)
    );
    (
        // idx 2
        // lib.lcm_num.03
        (num_of_int 0), (num_of_int 2),
        (num_of_int 0)
    );
    (
        // idx 3
        // lib.lcm_num.04
        (num_of_int 1), (num_of_int 0),
        (num_of_int 0)
    );
    (
        // idx 4
        // lib.lcm_num.05
        (num_of_int 1), (num_of_int 1),
        (num_of_int 1)
    );
    (
        // idx 5
        // lib.lcm_num.06
        (num_of_int 1), (num_of_int 2),
        (num_of_int 2)
    );
    (
        // idx 6
        // lib.lcm_num.07
        (num_of_int 2), (num_of_int 0),
        (num_of_int 0)
    );
    (
        // idx 7
        // lib.lcm_num.08
        (num_of_int 2), (num_of_int 1),
        (num_of_int 2)
    );
    (
        // idx 8
        // lib.lcm_num.09
        (num_of_int 2), (num_of_int 2),
        (num_of_int 2)
    );
    (
        // idx 9
        // lib.lcm_num.10
        (num_of_int 2), (num_of_int 3),
        (num_of_int 6)
    );
    (
        // idx 10
        // lib.lcm_num.11
        (num_of_int 2), (num_of_int 4),
        (num_of_int 4)
    );
    (
        // idx 11
        // lib.lcm_num.12
        (num_of_int 2), (num_of_int 5),
        (num_of_int 10)
    );
    (
        // idx 12
        // lib.lcm_num.13
        (num_of_int 2), (num_of_int 6),
        (num_of_int 6)
    );
    (
        // idx 13
        // lib.lcm_num.14
        (num_of_int 3), (num_of_int 0),
        (num_of_int 0)
    );
    (
        // idx 14
        // lib.lcm_num.15
        (num_of_int 3), (num_of_int 1),
        (num_of_int 3)
    );
    (
        // idx 15
        // lib.lcm_num.16
        (num_of_int 3), (num_of_int 2),
        (num_of_int 6)
    );
    (
        // idx 16
        // lib.lcm_num.17
        (num_of_int 3), (num_of_int 3),
        (num_of_int 3)
    );
    (
        // idx 17
        // lib.lcm_num.18
        (num_of_int 3), (num_of_int 4),
        (num_of_int 12)
    );
    (
        // idx 18
        // lib.lcm_num.19
        (num_of_int 3), (num_of_int 5),
        (num_of_int 15)
    );
    (
        // idx 19
        // lib.lcm_num.20
        (num_of_int 3), (num_of_int 6),
        (num_of_int 6)
    );
    |]
    
[<TestCase(0, TestName = "lib.lcm_num.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="Division_by_zero")>]
[<TestCase(1, TestName = "lib.lcm_num.02")>]
[<TestCase(2, TestName = "lib.lcm_num.03")>]
[<TestCase(3, TestName = "lib.lcm_num.04")>]
[<TestCase(4, TestName = "lib.lcm_num.05")>]
[<TestCase(5, TestName = "lib.lcm_num.06")>]
[<TestCase(6, TestName = "lib.lcm_num.07")>]
[<TestCase(7, TestName = "lib.lcm_num.08")>]
[<TestCase(8, TestName = "lib.lcm_num.09")>]
[<TestCase(9, TestName = "lib.lcm_num.10")>]
[<TestCase(10, TestName = "lib.lcm_num.11")>]
[<TestCase(11, TestName = "lib.lcm_num.12")>]
[<TestCase(12, TestName = "lib.lcm_num.13")>]
[<TestCase(13, TestName = "lib.lcm_num.14")>]
[<TestCase(14, TestName = "lib.lcm_num.15")>]
[<TestCase(15, TestName = "lib.lcm_num.16")>]
[<TestCase(16, TestName = "lib.lcm_num.17")>]
[<TestCase(17, TestName = "lib.lcm_num.18")>]
[<TestCase(18, TestName = "lib.lcm_num.19")>]
[<TestCase(19, TestName = "lib.lcm_num.20")>]

[<Test>]
let ``math lcm_num`` idx = 
    let (value1, _, _) = lcm_numValues.[idx]
    let (_, value2, _) = lcm_numValues.[idx]
    let (_, _, result) = lcm_numValues.[idx]
    lcm_num value1 value2
    |> should equal result

let private explodeValues : (string * string list)[] = [| 
    (
        // idx 0
        // lib.explode.01
        "",
        []
    );
    (
        // idx 1
        // lib.explode.02
        "a",
        ["a"]
    );
    (
        // idx 2
        // lib.explode.03
        "ab",
        ["a"; "b"]
    );
    (
        // idx 3
        // lib.explode.04
        "abc",
        ["a"; "b"; "c"]
    );
    |]
    
[<TestCase(0, TestName = "lib.explode.01")>]
[<TestCase(1, TestName = "lib.explode.02")>]
[<TestCase(2, TestName = "lib.explode.03")>]
[<TestCase(3, TestName = "lib.explode.04")>]

[<Test>]
let ``String explode`` idx = 
    let (string1, _) = explodeValues.[idx]
    let (_, result) = explodeValues.[idx]
    explode string1
    |> should equal result

let private implodeValues : (string list * string)[] = [| 
    (
        // idx 0
        // lib.implode.01
        [],
        ""
    );
    (
        // idx 1
        // lib.implode.02
        ["a"],
        "a"
    );
    (
        // idx 2
        // lib.implode.03
        ["a"; "b"],
        "ab"
    );
    (
        // idx 3
        // lib.implode.04
        ["a"; "b"; "c"],
        "abc"
    );
    |]
    
[<TestCase(0, TestName = "lib.implode.01")>]
[<TestCase(1, TestName = "lib.implode.02")>]
[<TestCase(2, TestName = "lib.implode.03")>]
[<TestCase(3, TestName = "lib.implode.04")>]

[<Test>]
let ``String implode`` idx = 
    let (list, _) = implodeValues.[idx]
    let (_, result) = implodeValues.[idx]
    implode list
    |> should equal result

let private increasingValues : (int * int * bool)[] = [| 
    (
        // idx 0
        // lib.increasing.01
        -2, -2,
        false
    );
    (
        // idx 1
        // lib.increasing.02
        -2, -1,
        true
    );
    (
        // idx 2
        // lib.increasing.03
        -2, 0,
        true
    );
    (
        // idx 3
        // lib.increasing.04
        -2, 1,
        true
    );
    (
        // idx 4
        // lib.increasing.05
        -2, 2,
        true
    );
    (
        // idx 5
        // lib.increasing.06
        -1, -2,
        false
    );
    (
        // idx 6
        // lib.increasing.07
        -1, -1,
        false
    );
    (
        // idx 7
        // lib.increasing.08
        -1, 0,
        true
    );
    (
        // idx 8
        // lib.increasing.09
        -1, 1,
        true
    );
    (
        // idx 9
        // lib.increasing.10
        -1, 2,
        true
    );
    (
        // idx 10
        // lib.increasing.11
        0, -2,
        false
    );
    (
        // idx 11
        // lib.increasing.12
        0, -1,
        false
    );
    (
        // idx 12
        // lib.increasing.13
        0, 0,
        false
    );
    (
        // idx 13
        // lib.increasing.14
        0, 1,
        true
    );
    (
        // idx 14
        // lib.increasing.15
        0, 2,
        true
    );
    (
        // idx 15
        // lib.increasing.16
        1, -2,
        false
    );
    (
        // idx 16
        // lib.increasing.17
        1, -1,
        false
    );
    (
        // idx 17
        // lib.increasing.18
        1, 0,
        false
    );
    (
        // idx 18
        // lib.increasing.19
        1, 1,
        false
    );
    (
        // idx 19
        // lib.increasing.20
        1, 2,
        true
    );
    (
        // idx 20
        // lib.increasing.21
        2, -2,
        false
    );
    (
        // idx 21
        // lib.increasing.22
        2, -1,
        false
    );
    (
        // idx 22
        // lib.increasing.23
        2, 0,
        false
    );
    (
        // idx 23
        // lib.increasing.24
        2, 1,
        false
    );
    (
        // idx 24
        // lib.increasing.25
        2, 2,
        false
    );
    |]
    
[<TestCase(0, TestName = "lib.increasing.01")>]
[<TestCase(1, TestName = "lib.increasing.02")>]
[<TestCase(2, TestName = "lib.increasing.03")>]
[<TestCase(3, TestName = "lib.increasing.04")>]
[<TestCase(4, TestName = "lib.increasing.05")>]
[<TestCase(5, TestName = "lib.increasing.06")>]
[<TestCase(6, TestName = "lib.increasing.07")>]
[<TestCase(7, TestName = "lib.increasing.08")>]
[<TestCase(8, TestName = "lib.increasing.09")>]
[<TestCase(9, TestName = "lib.increasing.10")>]
[<TestCase(10, TestName = "lib.increasing.11")>]
[<TestCase(11, TestName = "lib.increasing.12")>]
[<TestCase(12, TestName = "lib.increasing.13")>]
[<TestCase(13, TestName = "lib.increasing.14")>]
[<TestCase(14, TestName = "lib.increasing.15")>]
[<TestCase(15, TestName = "lib.increasing.16")>]
[<TestCase(16, TestName = "lib.increasing.17")>]
[<TestCase(17, TestName = "lib.increasing.18")>]
[<TestCase(18, TestName = "lib.increasing.19")>]
[<TestCase(19, TestName = "lib.increasing.20")>]
[<TestCase(20, TestName = "lib.increasing.21")>]
[<TestCase(21, TestName = "lib.increasing.22")>]
[<TestCase(22, TestName = "lib.increasing.23")>]
[<TestCase(23, TestName = "lib.increasing.24")>]
[<TestCase(24, TestName = "lib.increasing.25")>]

[<Test>]
let ``Predicate increasing`` idx = 
    let (x, _, _) = increasingValues.[idx]
    let (_, y, _) = increasingValues.[idx]
    let (_, _, result) = increasingValues.[idx]
    increasing (fun x -> x ) x y
    |> should equal result

let private decreasingValues : (int * int * bool)[] = [| 
    (
        // idx 0
        // lib.decreasing.01
        -2, -2,
        false
    );
    (
        // idx 1
        // lib.decreasing.02
        -2, -1,
        false
    );
    (
        // idx 2
        // lib.decreasing.03
        -2, 0,
        false
    );
    (
        // idx 3
        // lib.decreasing.04
        -2, 1,
        false
    );
    (
        // idx 4
        // lib.decreasing.05
        -2, 2,
        false
    );
    (
        // idx 5
        // lib.decreasing.06
        -1, -2,
        true
    );
    (
        // idx 6
        // lib.decreasing.07
        -1, -1,
        false
    );
    (
        // idx 7
        // lib.decreasing.08
        -1, 0,
        false
    );
    (
        // idx 8
        // lib.decreasing.09
        -1, 1,
        false
    );
    (
        // idx 9
        // lib.decreasing.10
        -1, 2,
        false
    );
    (
        // idx 10
        // lib.decreasing.11
        0, -2,
        true
    );
    (
        // idx 11
        // lib.decreasing.12
        0, -1,
        true
    );
    (
        // idx 12
        // lib.decreasing.13
        0, 0,
        false
    );
    (
        // idx 13
        // lib.decreasing.14
        0, 1,
        false
    );
    (
        // idx 14
        // lib.decreasing.15
        0, 2,
        false
    );
    (
        // idx 15
        // lib.decreasing.16
        1, -2,
        true
    );
    (
        // idx 16
        // lib.decreasing.17
        1, -1,
        true
    );
    (
        // idx 17
        // lib.decreasing.18
        1, 0,
        true
    );
    (
        // idx 18
        // lib.decreasing.19
        1, 1,
        false
    );
    (
        // idx 19
        // lib.decreasing.20
        1, 2,
        false
    );
    (
        // idx 20
        // lib.decreasing.21
        2, -2,
        true
    );
    (
        // idx 21
        // lib.decreasing.22
        2, -1,
        true
    );
    (
        // idx 22
        // lib.decreasing.23
        2, 0,
        true
    );
    (
        // idx 23
        // lib.decreasing.24
        2, 1,
        true
    );
    (
        // idx 24
        // lib.decreasing.25
        2, 2,
        false
    );
    |]
    
[<TestCase(0, TestName = "lib.decreasing.01")>]
[<TestCase(1, TestName = "lib.decreasing.02")>]
[<TestCase(2, TestName = "lib.decreasing.03")>]
[<TestCase(3, TestName = "lib.decreasing.04")>]
[<TestCase(4, TestName = "lib.decreasing.05")>]
[<TestCase(5, TestName = "lib.decreasing.06")>]
[<TestCase(6, TestName = "lib.decreasing.07")>]
[<TestCase(7, TestName = "lib.decreasing.08")>]
[<TestCase(8, TestName = "lib.decreasing.09")>]
[<TestCase(9, TestName = "lib.decreasing.10")>]
[<TestCase(10, TestName = "lib.decreasing.11")>]
[<TestCase(11, TestName = "lib.decreasing.12")>]
[<TestCase(12, TestName = "lib.decreasing.13")>]
[<TestCase(13, TestName = "lib.decreasing.14")>]
[<TestCase(14, TestName = "lib.decreasing.15")>]
[<TestCase(15, TestName = "lib.decreasing.16")>]
[<TestCase(16, TestName = "lib.decreasing.17")>]
[<TestCase(17, TestName = "lib.decreasing.18")>]
[<TestCase(18, TestName = "lib.decreasing.19")>]
[<TestCase(19, TestName = "lib.decreasing.20")>]
[<TestCase(20, TestName = "lib.decreasing.21")>]
[<TestCase(21, TestName = "lib.decreasing.22")>]
[<TestCase(22, TestName = "lib.decreasing.23")>]
[<TestCase(23, TestName = "lib.decreasing.24")>]
[<TestCase(24, TestName = "lib.decreasing.25")>]

[<Test>]
let ``Predicate decreasing`` idx = 
    let (x, _, _) = decreasingValues.[idx]
    let (_, y, _) = decreasingValues.[idx]
    let (_, _, result) = decreasingValues.[idx]
    decreasing (fun x -> x ) x y
    |> should equal result

let private assocValues : (int * (int * int) list * int)[] = [| 
    (
        // idx 0
        // lib.assoc.01
        // System.Exception - find
        1, [],
        -99 // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.assoc.02
        // System.Exception - find
        2, [1,2],
        -99 // Dummy value used as place holder
    );
    (
        // idx 2
        // lib.assoc.03
        1, [1,2],
        2
    );
    (
        // idx 3
        // lib.assoc.04
        1, [1,2; 1,3],
        2
    );
    (
        // idx 4
        // lib.assoc.05
        4, [1,2; 2,4; 3,9; 4,16],
        16
    );
    |]

[<TestCase(0, TestName = "lib.assoc.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]
[<TestCase(1, TestName = "lib.assoc.02", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]
[<TestCase(2, TestName = "lib.assoc.03")>]
[<TestCase(3, TestName = "lib.assoc.04")>]
[<TestCase(4, TestName = "lib.assoc.05")>]

[<Test>]
let ``Association List assoc`` idx = 
    let (x, _, _) = assocValues.[idx]
    let (_, list, _) = assocValues.[idx]
    let (_, _, result) = assocValues.[idx]
    assoc x list
    |> should equal result

let private rev_assocValues : (int * (int * int) list * int)[] = [| 
    (
        // idx 0
        // lib.rev_assoc.01
        // System.Exception - find
        1, [],
        -99 // Dummy value used as place holder
    );
    (
        // idx 1
        // lib.rev_assoc.02
        // System.Exception - find
        2, [1,2],
        1
    );
    (
        // idx 2
        // lib.rev_assoc.03
        1, [1,2],
        2
    );
    (
        // idx 3
        // lib.rev_assoc.04
        4, [1,4; 2,4],
        1
    );
    (
        // idx 4
        // lib.rev_assoc.05
        // System.IndexOutOfRangeException - Index was outside the bounds of the array.
        16, [1,2; 2,4; 3,9; 4,16],
        4
    );
    |]

[<TestCase(0, TestName = "lib.rev_assoc.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]
[<TestCase(1, TestName = "lib.rev_assoc.02")>]
[<TestCase(2, TestName = "lib.rev_assoc.03", ExpectedException=typeof<System.Exception>, ExpectedMessage="find")>]
[<TestCase(3, TestName = "lib.rev_assoc.04")>]
[<TestCase(4, TestName = "lib.rev_assoc.05")>]

[<Test>]
let ``Association List rev_assoc`` idx = 
    let (x, _, _) = rev_assocValues.[idx]
    let (_, list, _) = rev_assocValues.[idx]
    let (_, _, result) = rev_assocValues.[idx]
    rev_assoc x list
    |> should equal result

// --------------------------------------------------------------------

let divideBy x =
    match x with
    | 0 -> failwith "divide by zero."
    | _ -> true

let countItems x =
    match x with
    | x when x >= 0 -> true
    | _ -> raise (System.ArgumentException("x"))

let displayValue x =
    match x with 
    | x when (x > 32 && x < 127) -> true
    | _ -> invalidArg "x" "value is not printable."

let keyBeFound x =
    match x with
    | x when x >= 0 -> true
    | _ -> raise (System.Collections.Generic.KeyNotFoundException("x"))

let private canValues : ((int -> bool) * int * int)[] = [| 
    (
        // idx 0
        // lib.can01.01
        divideBy,
        -1, 
        0
    );
    (
        // idx 1
        // lib.can01.02
        countItems,
        1,
        -2
    );
    (
        // idx 2
        // lib.can01.03
        displayValue,
        33,
        4
    );
    (
        // idx 3
        // lib.can01.04
        displayValue,
        33,
        4
    );
    (
        // idx 4
        // lib.can01.05
        keyBeFound,
        33,
        -10
    );
    |]

// Run the can test with the false value to show that an exception will occur.
[<TestCase(0, TestName = "lib.can_Exception.01", ExpectedException=typeof<System.Exception>, ExpectedMessage="divide by zero.")>]
[<TestCase(1, TestName = "lib.can_Exception.02", ExpectedException=typeof<System.ArgumentException>, ExpectedMessage="x")>]
[<TestCase(2, TestName = "lib.can_Exception.03", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(3, TestName = "lib.can_Exception.04", ExpectedException=typeof<System.ArgumentException>)>]
[<TestCase(4, TestName = "lib.can_Exception.05", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>, ExpectedMessage="x")>]

[<Test>]
let ``function can exception`` idx =
    let (func, _, _) = canValues.[idx]
    let (_, _, falseValue) = canValues.[idx]
    func falseValue
    |> should equal () // Dummy value used as place holder

[<TestCase(0, TestName = "lib.can.01")>]
[<TestCase(1, TestName = "lib.can.02")>]
[<TestCase(2, TestName = "lib.can.03")>]
[<TestCase(3, TestName = "lib.can.04")>]
[<TestCase(4, TestName = "lib.can.05")>]

// Run the can test with both the true and the false value to show that
// the results are either true or false, and that no exception is returned
// when the false value is used.
[<Test>]
let ``function can`` idx =
    let (func, _, _) = canValues.[idx]
    let (_, trueValue, _) = canValues.[idx]
    let (_, _, falseValue) = canValues.[idx]
    can func trueValue
    |> should equal true
    can func falseValue
    |> should equal false

// ....................................................................................

let stepTwo x =
    x + 2;;

let private stepTwoValues : (int * int * int)[] = [| 
    (
        // idx 0
        // lib.stepTwo.01
        1,
        -1, 
        1
    );
    (
        // idx 1
        // lib.stepTwo.02
        2,
        -1, 
        3
    );
    (
        // idx 2
        // lib.stepTwo.03
        3,
        -1, 
        5
    );
    (
        // idx 3
        // lib.stepTwo.04
        10,
        -1, 
        19
    );
    (
        // idx 4
        // lib.stepTwo.05
        100,
        -1, 
        199
    );
    |]

[<TestCase(0, TestName = "lib.funpow.stepTwo.01")>]
[<TestCase(1, TestName = "lib.funpow.stepTwo.02")>]
[<TestCase(2, TestName = "lib.funpow.stepTwo.03")>]
[<TestCase(3, TestName = "lib.funpow.stepTwo.04")>]
[<TestCase(4, TestName = "lib.funpow.stepTwo.05")>]

[<Test>]
let ``function funpow stepTwo`` idx =
    let (reps, _, _) = stepTwoValues.[idx]
    let (_, init, _) = stepTwoValues.[idx]
    let (_, _, result) = stepTwoValues.[idx]
    funpow reps stepTwo init
    |> should equal result

// Based on BSD formula. See: http://rosettacode.org/wiki/Linear_congruential_generator
let rnd seed =
    (1103515245 * seed + 12345) &&& System.Int32.MaxValue;;

let private rndValues : (int * int * int)[] = [| 
    (
        // idx 0
        // lib.rnd.01
        1,
        -1, 
        1043980748
    );
    (
        // idx 1
        // lib.rnd.02
        2,
        -1, 
        288979989
    );
    (
        // idx 2
        // lib.rnd.03
        3,
        -1, 
        646343466
    );
    (
        // idx 3
        // lib.rnd.04
        10,
        -1, 
        834541773
    );
    (
        // idx 4
        // lib.rnd.05
        100,
        -1, 
        402220219
    );
    |]

[<TestCase(0, TestName = "lib.funpow.rnd.01")>]
[<TestCase(1, TestName = "lib.funpow.rnd.02")>]
[<TestCase(2, TestName = "lib.funpow.rnd.03")>]
[<TestCase(3, TestName = "lib.funpow.rnd.04")>]
[<TestCase(4, TestName = "lib.funpow.rnd.05")>]

[<Test>]
let ``function funpow rnd`` idx =
    let (reps, _, _) = rndValues.[idx]
    let (_, init, _) = rndValues.[idx]
    let (_, _, result) = rndValues.[idx]
    funpow reps rnd init
    |> should equal result

let pi (x : double) =
    x + (sin x);;

let private piValues : (int * double * double)[] = [| 
    (
        // idx 0
        // lib.pi.01
        1,
        3.0, 
        3.1411200080598674
    );
    (
        // idx 1
        // lib.pi.02
        2,
        3.0, 
        3.1415926535721956
    );
    (
        // idx 2
        // lib.pi.03
        3,
        3.0, 
        3.1415926535897931
    );
    (
        // idx 3
        // lib.pi.04
        10,
        3.0, 
        3.1415926535897931
    );
    (
        // idx 4
        // lib.pi.05
        100,
        3.0, 
        3.1415926535897931
    );
    |]

[<TestCase(0, TestName = "lib.funpow.pi.01")>]
[<TestCase(1, TestName = "lib.funpow.pi.02")>]
[<TestCase(2, TestName = "lib.funpow.pi.03")>]
[<TestCase(3, TestName = "lib.funpow.pi.04")>]
[<TestCase(4, TestName = "lib.funpow.pi.05")>]

[<Test>]
let ``function funpow pi`` idx =
    let (reps, _, _) = piValues.[idx]
    let (_, init, _) = piValues.[idx]
    let (_, _, result) = piValues.[idx]
    funpow reps pi init
    |> should equal result


let truthCaseGenerator values =
    match values with
    | [] -> [ "0"; "1" ]
    | _ -> 
        let zeroList = List.map (fun item ->  "0" + item) values
        let oneList = List.map (fun item ->  "1" + item) values
        let newList = List.append zeroList oneList
        (newList : string list);;

let private truthCaseGeneratorValues : (int * string list * string list)[] = [| 
    (
        // idx 0
        // lib.truthCaseGenerator.01
        1,
        [], 
        ["0"; "1"]
    );
    (
        // idx 1
        // lib.truthCaseGenerator.02
        2,
        [], 
        ["00"; "01"; "10"; "11"]
    );
    (
        // idx 2
        // lib.truthCaseGenerator.03
        3,
        [], 
        ["000"; "001"; "010"; "011"; "100"; "101"; "110"; "111"]
    );
    (
        // idx 3
        // lib.truthCaseGenerator.04
        4,
        [], 
        ["0000"; "0001"; "0010"; "0011"; "0100"; "0101"; "0110"; "0111";
         "1000"; "1001"; "1010"; "1011"; "1100"; "1101"; "1110"; "1111"]
    );
    (
        // idx 4
        // lib.truthCaseGenerator.05
        5,
        [], 
        ["00000"; "00001"; "00010"; "00011"; "00100"; "00101"; "00110";
         "00111"; "01000"; "01001"; "01010"; "01011"; "01100"; "01101";
         "01110"; "01111"; "10000"; "10001"; "10010"; "10011"; "10100";
         "10101"; "10110"; "10111"; "11000"; "11001"; "11010"; "11011";
         "11100"; "11101"; "11110"; "11111"]
    );
    |]

[<TestCase(0, TestName = "lib.funpow.truthCaseGenerator.01")>]
[<TestCase(1, TestName = "lib.funpow.truthCaseGenerator.02")>]
[<TestCase(2, TestName = "lib.funpow.truthCaseGenerator.03")>]
[<TestCase(3, TestName = "lib.funpow.truthCaseGenerator.04")>]
[<TestCase(4, TestName = "lib.funpow.truthCaseGenerator.05")>]

[<Test>]
let ``function funpow truthCaseGenerator`` idx =
    let (reps, _, _) = truthCaseGeneratorValues.[idx]
    let (_, init, _) = truthCaseGeneratorValues.[idx]
    let (_, _, result) = truthCaseGeneratorValues.[idx]
    funpow reps truthCaseGenerator init
    |> should equal result

// =================================================================================

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
let ``function operator backward composition`` () =
    (addFive << timesFour) 2
    |> should equal 13

// lib.p040
// (2 + 5) * 4 = 28
[<Test>]
let ``function operator forward composition`` () =
    (addFive >> timesFour) 2
    |> should equal 28

// lib.p043
[<Test>]
let ``idiom non`` () =
    non (fun x -> x % 2 = 0) 5
    |> should equal true

// lib.p044
//[<Test>]
//let ``function funpow`` () =
//    funpow 10 (fun x -> x + x) 1
//    |> should equal 1024

let list1 = [1; 2; 3]
let list2 = [1; 3; 5]
// Crate a function that returns failure
let containsEven x =
    match x with
    | _ when  x % 2 = 0 -> true
    | _ -> failwith "not even"

// lib.p060
[<Test>]
let ``function tryfind 1`` () =
    try
        tryfind containsEven list1
    with
        | Failure _ -> false
        | _ -> true 
    |> should equal true

// lib.p061
[<Test>]
let ``function tryfind 2`` () =
    try
        tryfind containsEven list2
    with
        | Failure _ -> false
        | _ -> true  
    |> should equal false

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
let ``finite partial function operator update`` () =
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
