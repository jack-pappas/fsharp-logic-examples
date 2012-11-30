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

let private butLastValues : (int list * int list)[] = [| 
    (
        // idx 0
        // lib.butLast.01
        // System.Exception - butlast
        [],
        []
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
        [1;]
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
        ( [], [] )
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
        ( [], [] )
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
        ( [], [] )
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
        ( [], [] )
    );
    (
        // idx 14
        // lib.chopList.15
        // System.Exception - chop_list
        -1, [],
        ( [], [1; 2; 3] )
    );
    (
        // idx 15
        // lib.chopList.16
        // System.Exception - chop_list
        -1, [1],
        ( [1], [2; 3] )
    );
    (
        // idx 16
        // lib.chopList.17
        // System.Exception - chop_list
        -1, [1; 2],
        ( [1; 2], [3] )
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1], 1, -1, 
        true
    );
    (
        // idx 16
        // lib.earlier.017
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2], 1, 2, 
        true
    );
    (
        // idx 32
        // lib.earlier.033
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2], 1, 3, 
        true
    );
    (
        // idx 33
        // lib.earlier.034
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2], 2, -1, 
        true
    );
    (
        // idx 34
        // lib.earlier.035
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2; 3], 1, 3,
        true
    );
    (
        // idx 58
        // lib.earlier.059
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2; 3], 2, 3,
        true
    );
    (
        // idx 63
        // lib.earlier.064
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2; 3], 3, -1,
        true
    );
    (
        // idx 64
        // lib.earlier.065
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2; 3; 4], 2, 4,
        true
    );
    (
        // idx 92
        // lib.earlier.093
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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
        // TODO: EGT Is this correct result?  argument(s) exceed list size
        [1; 2; 3; 4], 4, -1,
        true
    );
    (
        // idx 99
        // lib.earlier.100
        // TODO: EGT Is this correct result?  argument(s) exceed list size
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


[<Test>]
let ``List end_itlist`` () =
    end_itlist (fun x y -> x * y) [1; 2; 3; 4]
    |> should equal 24

    
// =================================================================================

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
//[<Test>]
//let ``List end_itlist`` () =
//    end_itlist (fun x y -> x * y) [1; 2; 3; 4]
//    |> should equal 24
    
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
let ``List sort all`` () =
    sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5]
    |> should equal [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9]

// lib.p025
[<Test>]
let ``List sort uniq`` () =
    uniq (sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5])
    |> should equal [1; 2; 3; 4; 5; 6; 9]

// lib.p026
[<Test>]
let ``List sort by increasing length`` () =
    sort (increasing List.length) [[1]; [1;2;3]; []; [3; 4]]
    |> should equal [[]; [1]; [3; 4]; [1; 2; 3]]

// lib.p027
[<Test>]
let ``List unions`` () =
    unions [[1; 2; 3]; [4; 8; 12]; [3; 6; 9; 12]; [1]]
    |> should equal [1; 2; 3; 4; 6; 8; 9; 12]

// lib.p028
[<Test>]
let ``List image`` () =
    image (fun x -> x % 2) [1; 2; 3; 4; 5]
    |> should equal [0; 1]    

// lib.p029
[<Test>]
let ``List allsubsets`` () =
    allsubsets [1; 2; 3]
    |> should equal [[]; [1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]

// lib.p030
[<Test>]
let ``List allnonemptysubsets`` () =
    allnonemptysubsets [1; 2; 3]
    |> should equal [[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]

// lib.p031
[<Test>]
let ``List allsets`` () =
    allsets 2 [1; 2; 3]
    |> should equal [[1; 2]; [1; 3]; [2; 3]]

// lib.p032
[<Test>]
let ``List allpairs`` () =
    allpairs (fun x y -> x * y) [2; 3; 5] [7; 11]
    |> should equal [14; 22; 21; 33; 35; 55]

// lib.p033
//[<Test>]
//let ``List distinctpairs`` () =
//    distinctpairs [1; 2; 3; 4]
//    |> should equal [(1, 2); (1, 3); (1, 4); (2, 3); (2, 4); (3, 4)]

// lib.p034
[<Test>]
let ``Association List assoc`` () =
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
let ``function operator backward composition`` () =
    (addFive << timesFour) 2
    |> should equal 13

// lib.p040
// (2 + 5) * 4 = 28
[<Test>]
let ``function operator forward composition`` () =
    (addFive >> timesFour) 2
    |> should equal 28

// lib.p041
[<Test>]
let ``math gcd`` () =
    gcd_num (num_of_int 12) (num_of_int 15)
    |> should equal (num_of_int 3)

// lib.p042
[<Test>]
let ``math lcm`` () =
    lcm_num (num_of_int 12) (num_of_int 15)
    |> should equal (num_of_int 60)

// lib.p043
[<Test>]
let ``idiom non`` () =
    non (fun x -> x % 2 = 0) 5
    |> should equal true

// lib.p044
[<Test>]
let ``function funpow`` () =
    funpow 10 (fun x -> x + x) 1
    |> should equal 1024

let divideBy x =
    match x with
    | 0 -> failwith "zero"
    | _ -> true

// lib.p045
[<Test>]
let ``function can`` () =
    can divideBy 0
    |> should equal false

// lib.p046
[<Test>]
let ``List operator range (int)`` () =
    3--5
    |> should equal [3; 4; 5]

// lib.p047
[<Test>]
let ``List operator range (num)`` () =
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
//[<Test>]
//let ``List earlier`` () =
//    earlier [1; 2; 3] 3 2
//    |> should equal false

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
