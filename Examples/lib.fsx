// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharp.Compatibility.OCaml.Num 

// pg. 619

// lib.p001
butlast [1; 2; 3; 4];;

// lib.p002
chop_list 3 [1; 2; 3; 4; 5];;

// lib.p003
// NOTE: do_list has been replaced with the built-in F# function List.iter.
let list_iter () =
    let l = ["See "; "the "; "dog"]
    let sb = System.Text.StringBuilder ()
    l |> List.iter (fun (s : string) ->
        sb.Append s
        |> ignore)
    sb.ToString ()

// lib.p004
// NOTE: el has been replaced with the equivalent built-in F# function List.nth.
// NOTE: reversal or parameters between OCaml el and F# nth
List.nth [0; 1; 2; 3] 2

// lib.p005
// Multiply all items in list, i.e. 1 * 2 * 3 * 4
List.reduceBack (fun x y -> x * y) [1; 2; 3; 4];;

// lib.p006
// NOTE: exists has been replaced with the equivalent built-in F# function List.exists.
// Test list to see if it contains an even number
List.exists (fun x -> x % 2 = 0) [1; 2; 3];;

// lib.p007
explode "hello";;

// lib.p008
// NOTE: forall has been replaced with the equivalent built-in F# function List.forall.
// Test list to see if all items in list are less than 5?
List.forall (fun x -> (x < 5)) [1; 2; 3];;

// lib.p009
// NOTE: forall2 has been replaced with the equivalent built-in F# function List.forall2.
// Test first list to see if each item is lest than item in same position in second list.
List.forall2 (fun x y -> (x < y)) [1; 2; 3; 4] [3; 4; 5; 6];;

// lib.p010
// NOTE: hd has been replaced with the equivalent built-in F# function List.head.
List.head [1; 2; 3];;

// lib.p011
implode ["w"; "x"; "y"; "z"];;

// lib.p012
insertat 3 9 [0; 1; 2; 3; 4; 5];;

// lib.p013
// NOTE: itlist has been replaced with the equivalent built-in F# function List.foldBack.
List.foldBack (fun x y -> x + y) [1; 2; 3] 5;;

// lib.p014
// NOTE: itlist2 has been replaced with the equivalent built-in F# function List.foldBack2.
List.foldBack2 (fun a x y -> a + x + y) ["a"; "b"; "c"] ["1"; "2"; "3"] " Hello";;

// lib.p015
last [1; 2; 3; 4];;

// lib.p016
// NOTE: map has been replaced with the equivalent built-in F# function List.map.
List.map (fun x -> x + 5) [1; 2; 3];;

// lib.p017
// NOTE: map2 has been replaced with the equivalent built-in F# function List.map2.
List.map2 (fun x y -> x + y) [1; 2; 3] [10; 11; 12];;

// lib.p018
mapfilter (fun x -> x % 2 = 0) [1; 2; 3; 4];;

// lib.p019
// NOTE: replicate is not used in code.

// lib.p020
// NOTE: rev has been replaced with the equivalent built-in F# function List.rev.
List.rev [1; 2; 3; 4];;

// lib.p021
// NOTE: tl has been replaced with the equivalent built-in F# function List.tail.
List.tail [1; 2; 3; 4];;

// lib.p022
// NOTE: upzip has been replaced with the equivalent built-in F# function List.unzip.
List.unzip [(1,"a"); (2,"b"); (3,"c")];;

// lib.p023
// NOTE: zip has been replaced with the equivalent built-in F# function List.zip.
List.zip [1; 2; 3] ["a"; "b"; "c"];;

// lib.p024
sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5];;

// lib.p025
uniq (sort (<) [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5]);;

// lib.p026
sort (increasing List.length) [[1]; [1;2;3]; []; [3; 4]];;

// pg. 620

// lib.p027
unions [[1; 2; 3]; [4; 8; 12]; [3; 6; 9; 12]; [1]];;

// lib.p028
image (fun x -> x % 2) [1; 2; 3; 4; 5];;

// lib.p029
allsubsets [1; 2; 3];;

// lib.p030
allnonemptysubsets [1; 2; 3];;

// lib.p031
allsets 2 [1; 2; 3];;

// lib.p032
allpairs (fun x y -> x * y) [2; 3; 5] [7; 11];;

// lib.p033
distinctpairs [1; 2; 3; 4];;

// lib.p034
assoc 3 [1,2; 2,4; 3,9; 4,16];;

// pg. 621
let smallsqs = fpf [1;2;3] [1;4;9];;

// lib.p035
graph smallsqs;;

// lib.p036
graph (undefine 2 smallsqs);;

// lib.p037
graph ((3 |-> 0) smallsqs);;

// lib.p038
apply smallsqs 3;;

// Some additional tests (not in the book)

// NOTE: The ( ** ) operator has been replaced with the equivalent built-in F# operator ( << ).
let addFive x = x + 5;;
let timesFour x = x * 4;;

// lib.p039
// (2 * 4) + 5 = 13
(addFive << timesFour) 2;;

// lib.p040
// (2 + 5) * 4 = 28
(addFive >> timesFour) 2;;

// pg. 610
// lib.p041
gcd_num (num_of_int 12) (num_of_int 15);;

// lib.p042
lcm_num (num_of_int 12) (num_of_int 15);;

// lib.p043
non (fun x -> x % 2 = 0) 5;;

// pg. 612 
// lib.p044
funpow 10 (fun x -> x + x) 1;;

let divideBy x =
    match x with
    | 0 -> failwith "zero"
    | _ -> true;;

// lib.p045
can divideBy 0;;

// lib.p046
3--5;;

// lib.p047
(num_of_int 3)---(num_of_int 5);;

// lib.p048
// NOTE: partition has been replaced with the equivalent built-in F# function List.partition.
List.partition (fun x -> x % 2 = 0) [0; 1; 2; 3; 4];;

// lib.p049
// NOTE: filter has been replaced with the equivalent built-in F# function List.filter.
List.filter (fun x -> x % 2 = 0) [0; 1; 2; 3; 4];;

// lib.p050
// NOTE: length has been replaced with the equivalent built-in F# function List.length.
List.length [1; 2; 3];;

// lib.p051
// NOTE: find has been replaced with the equivalent built-in F# function List.find.
List.find (fun x -> x % 2 = 0) [1; 2; 3; 4];;

// lib.p052
index 1 [1; 2; 3; 1];;

// lib.p053
earlier [1; 2; 3] 3 2;;

// lib.p054
merge (<) [3] [1];;

// lib.p055
merge (>) [1] [3];;

// lib.p056
//mergepairs (<) [[1;10]; [3;7]; [5;8]] [[2;11]; [4;12]; [6;9]];;

// lib.p057
//mergepairs (>) [[10;1]; [7;3]; [8;5]] [[11;2]; [12;4]; [9;6]];;

// lib.p058
increasing List.length [1] [1;2;3];;

// lib.p059
decreasing List.length [1] [1;2;3];;

// NOTE: Harrison's tryfind works with functions that use failure as a normal result which is customary for OCaml,
// as opposed to F# which recommends the use of options in such situations,
// due to exceptions being expensive in terms of processing time for Microsoft .NET in general .
// NOTE: Harrison's tryfind is primarly used for bakctracking when searching.
let list1 = [1; 2; 3;];;
let list2 = [1; 3; 5;];;
// Crate a function that returns failure
let containsEven x =
    match x with
    | _ when  x % 2 = 0 -> true
    | _ -> failwith "not even";;

// lib.p060
try
    tryfind containsEven list1
with
    | Failure _ -> false
    | _ -> true ;;

// lib.p061
try
    tryfind containsEven list2
with
    | Failure _ -> false
    | _ -> true ;;
 
 // lib.p062
 // Note: mapfilter needs a function that returns failure for items to be filtered out.
 mapfilter (fun x -> 
    match x with
    | _ when x % 2 = 0 -> x
    | _ -> failwith "invalid")
    [1; 2; 3; 4];;

// lib.p063
maximize (fun x -> x * x) [-4; 1; 2];;

// lib.p064
minimize (fun x -> x * x) [-4; 1; 2];;

// lib.p065
setify [1; 5; 2; 1; 3; 6; 4; 5];;

// lib.p066
union [1; 2; 3; 5; 6] [2; 4; 5];;

// lib.p067
intersect [1; 2; 3; 5; 6] [2; 4; 5];;

// lib.p068
subtract [1; 2; 3; 5; 6] [2; 4; 5];;

// lib.p069
subset [1; 2; 3; 5; 6] [2; 4; 5];;

// lib.p070
subset [1; 2; 3; 5; 6] [1; 2; 3; 5; 6];;

// lib.p071
subset [2; 5] [1; 2; 3; 5; 6];;

// lib.p072
psubset [1; 2; 3; 5; 6] [2; 4; 5];;

// lib.p073
psubset [1; 2; 3; 5; 6] [1; 2; 3; 5; 6];;

// lib.p074
psubset [2; 5] [1; 2; 3; 5; 6];;

// lib.p075
set_eq [1; 2; 3; 5; 6] [2; 4; 5];;

// lib.p076
set_eq [1; 2; 3; 6; 5] [1; 2; 3; 5; 6];;

// lib.p077
set_eq [] [];;

// lib.p078
insert 3 [1; 2; 4];;

// lib.p079
mem 3 [1; 2; 4];;

// lib.p080
mem 2 [1; 2; 4];;

// lib.p081
// An empty tree
let patricia_tree_empty : func<int,int> = (fpf [] []);;
print_patricia_tree (fpf [] []);;

// lib.p082
// NOTE: No branches, just one leaf
let patricia_tree_one_leaf = (fpf [1] [1]);;
print_patricia_tree (fpf [1] [1]);;

// lib.p083
// NOTE: One branch and two leaves
print_patricia_tree (fpf [1;2] [1;4]);;

// lib.p084
// NOTE: A branch with one branch and one leaf.
print_patricia_tree (fpf [1;2;3] [1;4;9]);;

// lib.p085
// NOTE: A branch with two branches, and two branches with two leaves.
print_patricia_tree (fpf [1;2;3;4] [1;4;9;16]);;

// lib.p086
mapf (fun x -> x + 5) smallsqs;;

// lib.p087
dom smallsqs;;

// lib.p088
ran smallsqs;;

// lib.p089
apply smallsqs 9;;

// lib.p090
tryapplyd smallsqs 9 -1;;

// lib.p091
tryapplyd smallsqs 3 -1;;

let words = fpf [1;2;3] [ ["a"]; ["i";"t"]; ["d";"o";"g"] ];;

// lib.p092
tryapplyl words 1;;

// lib.p093
tryapplyl words 3;;

// lib.p094
defined smallsqs 9;;

// lib.p095
defined smallsqs 3;;

// lib.p096
undefine 9 smallsqs;;

// lib.p097
undefine 3 smallsqs;;

// lib.p098
let pt = 10 |=> 100;;
print_patricia_tree pt;;

// lib.p099
valmod 0 1 (fun z -> z + 5) 0;;

// lib.p100
valmod 0 1 (fun z -> z + 5) -1;;

let y = fun x -> undef x;;
// lib.p101
printfn "y: %A" (y 1);;

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
List.map (fun x -> canonize ptn x) [-1;0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19];;

// lib.p103
let testValues = 
    seq { 
        for x in -1 .. 18 do
            for y in -1 .. 18 do
                yield (x,y)
    };;
let mapEq items =
    let (x,y) = items
    let eq = equivalent ptn x y
    (x,y,eq);;
let filterEq items =
    let (x,y,eq) = items
    eq;;
let simplifyEq items =
    let (x,y,eq) = items
    (x,y);;
List.map mapEq (Seq.toList testValues)
|> List.filter filterEq
|> List.map simplifyEq;;
      
// lib.p104
equated ptn;;
