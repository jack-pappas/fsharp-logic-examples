// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

/// Misc library functions to set up a nice environment.
[<AutoOpen>]
module FSharpx.Books.AutomatedReasoning.lib

open LanguagePrimitives
open FSharp.Compatibility.OCaml.Num


// The exception fired by failwith is used as a control flow.
// KeyNotFoundException is not recognized in many cases, so we have to use redefine Failure for compatibility.
// Using exception as a control flow should be eliminated in the future.
let (|Failure|_|) (exn: exn) =
    match exn with
    | :? System.Collections.Generic.KeyNotFoundException as p -> Some p.Message
    | :? System.ArgumentException as p -> Some p.Message
    | Failure s -> Some s
    | _ -> None

// pg. 618
// NOTE: The ( ** ) operator has been replaced with the equivalent built-in F# operator ( << ).

// ------------------------------------------------------------------------- //
// GCD and LCM on arbitrary-precision numbers.                               //
// ------------------------------------------------------------------------- //

// pg. 618
let rec gcd_num (n1 : num) (n2 : num) =
    if n2 = GenericZero then n1
    else gcd_num n2 (n1 % n2)
            
// pg. 618
let lcm_num (n1 : num) (n2 : num) =
    (abs (n1 * n2)) / gcd_num n1 n2

// ------------------------------------------------------------------------- //
// A useful idiom for "non contradictory" etc.                               //
// ------------------------------------------------------------------------- //

// pg. 618
let inline non p x =
    not <| p x

// ------------------------------------------------------------------------- //
// Kind of assertion checking.                                               //
// ------------------------------------------------------------------------- //

// Not in book
// Support fucntion for end user use if needed. 
// Not used in handbook code.
let check p x =
    assert (p x)
    x

// ------------------------------------------------------------------------- //
// Repetition of a function.                                                 //
// ------------------------------------------------------------------------- //

// pg. 612
let rec funpow n f x =
    if n < 1 then x
    else funpow (n - 1) f (f x)

// pg. 618
let can f x = 
    try 
        f x |> ignore
        true
    with Failure _ ->
        false

// pg. 618
let rec repeat f x = 
    try repeat f (f x)
    with Failure _ -> x

// ------------------------------------------------------------------------- //
// Handy list operations.                                                    //
// ------------------------------------------------------------------------- //

// pg. 618
// NOTE: (--) operator has been replaced with an equivalent using built-in F# range expression.
let inline (--) (m : int) (n : int) = [m..n]

// pg.618
// NOTE: (---) operator has been replaced with an equivalent using built-in F# range expression.
let inline (---) (m : num) (n : num) = [m..n]

// pg. 619
// NOTE: map2 has been replaced with the equivalent built-in F# function List.map2.

// pg. 619
// NOTE: rev has been replaced with the equivalent built-in F# function List.rev.

// pg. 619
// NOTE: hd has been replaced with the equivalent built-in F# function List.head.
        
// pg. 619
// NOTE: tl has been replaced with the equivalent built-in F# function List.tail.

// pg. 619 - list iterator
// NOTE: itlist has been replaced with the equivalent built-in F# function List.foldBack.
        
// pg. 619
// NOTE: end_itlist has been replaced with the equivalent built-in F# function List.reduceBack.
        
// pg. 619
// NOTE: itlist2 has been replaced with the equivalent built-in F# function List.foldBack2.
        
// pg. 619
// NOTE: zip has been replaced with the equivalent built-in F# function List.zip.

// pg. 619
// NOTE: forall has been replaced with the equivalent built-in F# function List.forall.
        
// pg. 619
// NOTE: exists has been replaced with the equivalent built-in F# function List.exists.
        
// pg. 619
// NOTE: partition has been replaced with the equivalent built-in F# function List.partition.

// pg. 619
// NOTE: filter has been replaced with the equivalent built-in F# function List.filter.

// pg. 619
// NOTE: length has been replaced with the equivalent built-in F# function List.length.
        
// pg. 619
let rec last l =
    match l with
    | [] ->
        failwith "Cannot get the last element of an empty list."
    | [x] -> x
    | _ :: tl ->
        last tl
        
/// Private, recursive implementation of 'butlast' which
/// improves performance by using continuation-passing-style.
//let rec private butlastImpl lst cont =
//    match lst with
//    | [] ->
//        failwith "butlastImpl"
//    | [_] ->
//        cont []
//    | hd :: tl ->
//        butlastImpl tl <| fun lst' ->
//            cont (hd :: lst')

// pg. 619
//let butlast l =
//    butlastImpl l id

// pg. 619
let rec butlast l =
    match l with
    | [_]    -> []
    | (h::t) -> h::(butlast t)
    | []     -> failwith "butlast"
        
// pg. 619
// NOTE: find has been replaced with the equivalent built-in F# function List.find.

// In comparing exceptions in terms of computing time, 
// Ocaml's exceptions are inexpensive in comparison with F# exceptions.
// To avoid exceptions from F# List.find, use F# List.tryFind which
// does not return an exception if an item is not found.

// pg. 619
// NOTE: el has been replaced with the equivalent built-in F# function List.nth.

// pg. 619
// NOTE: map has been replaced with the equivalent built-in F# function List.map.
        
// pg. 620
let rec allpairs f l1 l2 =
    match l1 with
    | [] -> []
    | h1 :: t1 ->
        List.foldBack (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)

// pg. 620
/// Given a list, creates a new list containing all unique 2-combinations
/// of the list elements. (I.e., (x, y) and (y, x) are the same and
/// will only be included once.)
let rec distinctpairs l =
    match l with
    | [] -> []
    | x :: t ->
        List.foldBack (fun y a -> (x, y) :: a) t (distinctpairs t)
        
// pg. 619
let rec chop_list n l =
    if n = 0 then [], l
    else
        try
            let m, l' = chop_list (n - 1) (List.tail l) 
            (List.head l) :: m, l'
        with _ ->
            failwith "chop_list"
        
// pg. 619
// NOTE: replicate has been replaced with the equivalent built-in F# function List.replicate.
    
// pg. 619
let rec insertat i x l =
    if i = 0 then x :: l
    else
        match l with
        | [] -> failwith "insertat: list too short for position to exist"
        | h :: t ->
            h :: (insertat (i - 1) x t)
        
// pg. 619
// NOTE: forall2 has been replaced with the equivalent built-in F# function List.forall2.
        
// pg. 619
// NOTE: index has been replaced with an equivalent using built-in F# function List.findIndex.
let inline index x xs = List.findIndex ((=) x) xs
        
// pg. 619
// NOTE: upzip has been replaced with the equivalent built-in F# function List.unzip.

// ------------------------------------------------------------------------- //
// Whether the first of two items comes earlier in the list.                 //
// ------------------------------------------------------------------------- //

// pg. 619
let rec earlier l x y =
    match l with
    | [] -> false
    | h :: t ->
        (compare h y <> 0) && (compare h x = 0 || earlier t x y)
        

// ------------------------------------------------------------------------- //
// Application of (presumably imperative) function over a list.              //
// ------------------------------------------------------------------------- //

// pg. 619
// NOTE: do_list has been replaced with the built-in F# function List.iter.

// ------------------------------------------------------------------------- //
// Association lists.                                                        //
// ------------------------------------------------------------------------- //

// pg. 620
let rec assoc a l =
    match l with
    | [] -> failwith "find"
    | (x, y) :: t ->
        if compare x a = 0 then y
        else assoc a t

// Not in book
// Support fucntion for end user use if needed. 
// Not used in handbook code.
let rec rev_assoc a l =
    match l with
    | [] -> failwith "find"
    | (x, y) :: t ->
        if compare y a = 0 then x
        else rev_assoc a t

// ------------------------------------------------------------------------- //
// Merging of sorted lists (maintaining repetitions).                        //
// ------------------------------------------------------------------------- //

// Not in book
// Support function for use with mergepairs, sort
let rec merge comparer l1 l2 =
    match l1, l2 with
    | [], x
    | x, [] -> x
    | h1 :: t1, h2 :: t2 ->
        if comparer h1 h2 then
            h1 :: (merge comparer t1 l2)
        else
            h2 :: (merge comparer l1 t2)

// ------------------------------------------------------------------------- //
// Bottom-up mergesort.                                                      //
// ------------------------------------------------------------------------- //

// pg. 619
let sort ord =
    let rec mergepairs l1 l2 =
        match l1, l2 with
        | [s],[] -> s
        | l,[] ->
            mergepairs [] l
        | l,[s1] ->
            mergepairs (s1::l) []
        | l, s1 :: s2 :: ss ->
            mergepairs ((merge ord s1 s2)::l) ss
    fun l -> 
        if l = [] then [] 
        else mergepairs [] (List.map (fun x -> [x]) l)


// ------------------------------------------------------------------------- //
// Common measure predicates to use with "sort".                             //
// ------------------------------------------------------------------------- //

// pg. 619
let increasing f x y =
    compare (f x) (f y) < 0
    
// pg. 619
let decreasing f x y =
    compare (f x) (f y) > 0

// ------------------------------------------------------------------------- //
// Eliminate repetitions of adjacent elements, with and without counting.    //
// ------------------------------------------------------------------------- //

// pg. 619
let rec uniq l =
    match l with
    | x :: (y :: _ as t) -> 
        let t' = uniq t
        if compare x y = 0 then t' 
        else
            if t' = t then l 
            else x :: t'
    | _ -> l

// Not in book
// Support fucntion for end user use if needed. 
// Not used in handbook code.
let repetitions =
    let rec repcount n l =
        match l with
        | [] -> failwith "repcount"
        | [x] -> [x,n]
        |  x :: (y :: _ as ys) -> 
            if compare y x = 0 then
                repcount (n + 1) ys
            else (x, n) :: (repcount 1 ys)
            
    fun l -> 
        if l = [] then [] 
        else repcount 1 l
        
// pg. 619
let rec tryfind f l =
    match l with
    | [] ->
        failwith "tryfind"
    | h :: t ->
        try f h
        with Failure _ ->
            tryfind f t
        
// pg. 619
let rec mapfilter f l =
    match l with
    | [] -> []
    | h :: t ->
        let rest = mapfilter f t
        try (f h) :: rest
        with Failure _ -> rest

// ------------------------------------------------------------------------- //
// Find list member that maximizes or minimizes a function.                  //
// ------------------------------------------------------------------------- //

// Not in book
// Support function for use with maximize and minimize
let optimize ord f lst =
    lst
    |> List.map (fun x -> x, f x)
    |> List.reduceBack (fun (_, y1 as p1) (_, y2 as p2) ->
        if ord y1 y2 then p1 else p2)
    |> fst
                        
// pg. 620
let maximize f l =
    optimize (>) f l
    
// pg. 620
let minimize f l =
    optimize (<) f l

// ------------------------------------------------------------------------- //
// Set operations on ordered lists.                                          //
// ------------------------------------------------------------------------- //

// pg. 620
let setify =
    let rec canonical lis =
        match lis with
        | x :: (y :: _ as rest) ->
            compare x y < 0
            && canonical rest
        | _ -> true
    fun l -> 
        if canonical l then l
        else uniq (sort (fun x y -> compare x y <= 0) l)

// pg. 620
let union =
    let rec union l1 l2 =
        match l1, l2 with
        | [], l2 -> l2
        | l1, [] -> l1
        | (h1 :: t1 as l1), (h2 :: t2 as l2) ->
            if h1 = h2 then
                h1 :: (union t1 t2)
            elif h1 < h2 then
                h1 :: (union t1 l2)
            else
                h2 :: (union l1 t2)
    fun s1 s2 ->
        union (setify s1) (setify s2)
        
// pg. 620
let intersect =
    let rec intersect l1 l2 =
        match l1, l2 with
        | [], l2 -> []
        | l1, [] -> []
        | (h1 :: t1 as l1), (h2 :: t2 as l2) ->
            if h1 = h2 then
                h1 :: (intersect t1 t2)
            elif h1 < h2 then
                intersect t1 l2
            else
                intersect l1 t2
    fun s1 s2 ->
        intersect (setify s1) (setify s2)
        
// pg. 620
let subtract =
    let rec subtract l1 l2 =
        match l1, l2 with
        | [], l2 -> []
        | l1, [] -> l1
        | (h1 :: t1 as l1), (h2 :: t2 as l2) ->
            if h1 = h2 then
                subtract t1 t2
            elif h1 < h2 then
                h1 :: (subtract t1 l2)
            else
                subtract l1 t2
    fun s1 s2 ->
        subtract (setify s1) (setify s2)
        
// pg. 620
let subset,psubset =
    let rec subset l1 l2 =
        match l1, l2 with
        | [], l2 -> true
        | l1, [] -> false
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then subset t1 t2
            elif h1 < h2 then false
            else subset l1 t2
    and psubset l1 l2 =
        match l1, l2 with
        | l1, [] -> false
        | [], l2 -> true
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then psubset t1 t2
            elif h1 < h2 then false
            else subset l1 t2
    (fun s1 s2 -> subset (setify s1) (setify s2)),
    (fun s1 s2 -> psubset (setify s1) (setify s2))

// pg. 620
let rec set_eq s1 s2 =
    setify s1 = setify s2
    
// pg. 620
let insert x s =
    union [x] s
    
// pg. 620
let image f s =
    setify (List.map f s)

// ------------------------------------------------------------------------- //
// Union of a family of sets.                                                //
// ------------------------------------------------------------------------- //

// pg. 620
let unions s =
    List.foldBack (@) s []
    |> setify

// ------------------------------------------------------------------------- //
// List membership. This does *not* assume the list is a set.                //
// ------------------------------------------------------------------------- //

// pg. 620
let rec mem x lis =
    match lis with
    | [] -> false
    | hd :: tl ->
        hd = x
        || mem x tl

// ------------------------------------------------------------------------- //
// Finding all subsets or all subsets of a given size.                       //
// ------------------------------------------------------------------------- //

// pg. 620
let rec allsets m l =
    if m = 0 then [[]]
    else
        match l with
        | [] -> []
        | h :: t ->
            union (image (fun g -> h :: g) (allsets (m - 1) t)) (allsets m t)
        
// pg. 620
let rec allsubsets s =
    match s with
    | [] -> [[]]
    | a :: t ->
        let res = allsubsets t
        union (image (fun b -> a :: b) res) res
                    
// pg. 620
let allnonemptysubsets s =
    subtract (allsubsets s) [[]]

// pg. 619
// ------------------------------------------------------------------------- //
// Explosion and implosion of strings.                                       //
// ------------------------------------------------------------------------- //

// pg. 619
let explode s =
    let mutable charList = []
    for i = (String.length s) - 1 downto 0 do
        charList <-
            s.[i].ToString() :: charList
    charList
        
// pg. 619
let implode l =
    let sb = System.Text.StringBuilder ()
    l |> List.iter (fun (s : string) ->
        sb.Append s
        |> ignore)
    sb.ToString ()

// ------------------------------------------------------------------------- //
// Timing; useful for documentation but not logically necessary.             //
// ------------------------------------------------------------------------- //

// pg. 617
let time f x =
    let timer = System.Diagnostics.Stopwatch.StartNew ()
    let result = f x
    timer.Stop ()
    printfn "CPU time (user): %f" timer.Elapsed.TotalSeconds
    result

// ------------------------------------------------------------------------- //
// Polymorphic finite partial functions via Patricia trees.                  //
//                                                                           //
// The point of this strange representation is that it is canonical (equal   //
// functions have the same encoding) yet reasonably efficient on average.    //
//                                                                           //
// Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        //
// ------------------------------------------------------------------------- //
//

// pg. 621
type func<'a,'b> =
    | Empty
    | Leaf of int * ('a * 'b) list
    | Branch of int * int * func<'a,'b> * func<'a,'b>

let rec string_of_patricia_tree_with_level pt (level : int) =
    match pt with
    | Empty  -> 
        let emptyindent = String.replicate level " "        
        emptyindent + "Empty"
    | Leaf (n,l) ->
        let leafindent = String.replicate level " "
        let leaf = "Leaf " + string n 
        let valueindent = String.replicate (level + 1) " "
        let value = sprintf "%A" l
        leafindent + leaf + "\n" + valueindent + value
    | Branch (n1, n2, b1, b2) ->
        let branchindent = String.replicate level " "
        let branchIndex = string n1 + "," + string n2
        let branch1 = string_of_patricia_tree_with_level b1 (level + 1)
        let branch2 = string_of_patricia_tree_with_level b2 (level + 1)
        let branch = "Branch " + branchIndex 
        branchindent + branch  + "\n" + branch1  + "\n" + branch2

let rec string_of_patricia_tree pt =
    string_of_patricia_tree_with_level pt 0

let sprint_patricia_tree pt =
    string_of_patricia_tree pt

let print_patricia_tree pt =
    printfn "%O" (sprint_patricia_tree pt) |> ignore

// ------------------------------------------------------------------------- //
// Undefined function.                                                       //
// ------------------------------------------------------------------------- //

// pg. 621
let undefined = Empty

// ------------------------------------------------------------------------- //
// In case of equality comparison worries, better use this.                  //
// ------------------------------------------------------------------------- //

// pg. 621
let is_undefined = function
    | Empty -> true
    | _     -> false

// ------------------------------------------------------------------------- //
// Operation analogous to "map" for lists.                                   //
// ------------------------------------------------------------------------- //

// pg. 621
let mapf =
    let rec map_list f l =
        match l with
        | [] -> []
        | (x, y) :: t ->
            (x, f y) :: (map_list f t)
    let rec mapf f t =
        match t with
        | Empty -> Empty
        | Leaf (h, l) ->
            Leaf (h, map_list f l)
        | Branch (p, b, l, r) ->
            Branch (p, b, mapf f l, mapf f r)
    mapf

// ------------------------------------------------------------------------- //
// Operations analogous to "fold" for lists.                                 //
// ------------------------------------------------------------------------- //

// Not in book
// Support function for use with graph, dom, and ran.
let foldl =
    let rec foldl_list f a l =
        match l with
        | [] -> a
        | (x, y) :: t ->
            foldl_list f (f a x y) t
    let rec foldl f a t =
        match t with
        | Empty -> a
        | Leaf (h, l) ->
            foldl_list f a l
        | Branch (p, b, l, r) ->
            foldl f (foldl f a l) r
    foldl
        
// Not in book
// Support fucntion for end user use if needed. 
// Not used in handbook code.
let foldr =
    let rec foldr_list f l a =
        match l with
        | [] -> a
        | (x, y) :: t ->
            f x y (foldr_list f t a)
    let rec foldr f t a =
        match t with
        | Empty -> a
        | Leaf (h, l) ->
            foldr_list f l a
        | Branch (p, b, l, r) ->
            foldr f l (foldr f r a)
    foldr

// ------------------------------------------------------------------------- //
// Mapping to sorted-list representation of the graph, domain and range.     //
// ------------------------------------------------------------------------- //

// pg. 621
let graph f =
    foldl (fun a x y -> (x, y) :: a) [] f
    |> setify
    
// pg. 621
let dom f =
    foldl (fun a x y -> x :: a) [] f
    |> setify
    
// pg. 621
let ran f =
    foldl (fun a x y -> y :: a) [] f
    |> setify

// ------------------------------------------------------------------------- //
// Application.                                                              //
// ------------------------------------------------------------------------- //

// Not in book
// Support function for use with apply, tryapplyd, and tryapplyl.
let applyd =
    let rec apply_listd l d x =
        match l with
        | [] -> d x
        | (a, b) :: tl ->
            let c = compare x a
            if c = 0 then b
            elif c > 0 then apply_listd tl d x
            else d x
            
    fun f d x ->
        let k = hash x
        let rec look t =
            match t with
            | Leaf (h, l) when h = k ->
                apply_listd l d x
            | Branch (p, b, l, r) when (k ^^^ p) &&& (b - 1) = 0 ->
                if k &&& b = 0 then l else r
                |> look
            | _ -> d x
        look f

// pg. 621
let apply f =
    applyd f (fun _ -> failwith "apply")

// pg. 621
let tryapplyd f a d =
    applyd f (fun _ -> d) a

// pg. 621
let tryapplyl f x =
    tryapplyd f x []
    
// pg. 621
let defined f x =
    try
        apply f x |> ignore
        true
    with
    | Failure _ -> false

// ------------------------------------------------------------------------- //
// Undefinition.                                                             //
// ------------------------------------------------------------------------- //

// pg. 621
let undefine =
    let rec undefine_list x l =
        match l with
        | [] -> []
        | (a, b as ab) :: t ->
                let c = compare x a
                if c = 0 then t
                elif c < 0 then l
                else
                    let t' = undefine_list x t
                    if t' = t then l
                    else ab :: t'
                              
    fun x ->
        let k = hash x
        let rec und t =
            match t with
            | Leaf (h, l) when h = k ->
                let l' = undefine_list x l
                if l' = l then t
                elif l' = [] then Empty
                else Leaf (h, l')

            | Branch (p, b, l, r) when k &&& (b - 1) = p ->
                if k &&& b = 0 then
                    let l' = und l
                    if l' = l then t
                    else
                        match l' with
                        | Empty -> r
                        | _ -> Branch (p, b, l', r)
                else
                    let r' = und r
                    if r' = r then t
                    else
                        match r' with
                        | Empty -> l
                        | _ -> Branch (p, b, l, r')
            | _ -> t
        und

// ------------------------------------------------------------------------- //
// Redefinition and combination.                                             //
// ------------------------------------------------------------------------- //

// Finite Partial Functions (FPF)

// To update the FPF with a new mapping from x to y.
// Not in book
// Support function for use with FPF
let (|->),combine =
    let newbranch p1 t1 p2 t2 =
        let zp = p1 ^^^ p2
        let b = zp &&& -zp
        let p = p1 &&& (b - 1)
        if p1 &&& b = 0 then Branch (p, b, t1, t2)
        else Branch (p, b, t2, t1)

    let rec define_list (x, y as xy) l =
        match l with
        | [] -> [xy]
        | (a, b as ab) :: t ->
            let c = compare x a
            if c = 0 then xy :: t
            elif c < 0 then xy :: l
            else ab :: (define_list xy t)

    and combine_list op z l1 l2 =
        match l1, l2 with
        | [], x
        | x, [] -> x
        | ((x1, y1 as xy1) :: t1, (x2, y2 as xy2) :: t2) ->
            let c = compare x1 x2
            if c < 0 then xy1 :: (combine_list op z t1 l2)
            elif c > 0 then xy2 :: (combine_list op z l1 t2)
            else
                let y = op y1 y2
                let l = combine_list op z t1 t2
                if z y then l
                else (x1, y) :: l

    let (|->) x y =
        let k = hash x
        let rec upd t =
            match t with
            | Empty -> Leaf (k, [x, y])
            | Leaf (h, l) ->
                if h = k then Leaf (h, define_list (x, y) l)
                else newbranch h t k (Leaf (k, [x, y]))
            | Branch (p, b, l, r) ->
                if k &&& (b - 1) <> p then newbranch p t k (Leaf (k, [x, y]))
                elif k &&& b = 0 then Branch (p, b, upd l, r)
                else Branch (p, b, l, upd r)
        upd

    let rec combine op z t1 t2 =
        match t1, t2 with
        | Empty, x
        | x, Empty -> x
        | Leaf (h1, l1), Leaf (h2, l2) ->
            if h1 = h2 then
                let l = combine_list op z l1 l2
                if l = [] then Empty
                else Leaf (h1, l)
            else newbranch h1 t1 h2 t2

        | (Leaf (k, lis) as lf), (Branch (p, b, l, r) as br) ->
            if k &&& (b - 1) = p then
                if k &&& b = 0 then
                    match combine op z lf l with
                    | Empty -> r
                    | l' -> Branch (p, b, l', r)
                else
                    match combine op z lf r with
                    | Empty -> l
                    | r' -> Branch (p, b, l, r')
            else
                newbranch k lf p br

        | (Branch (p, b, l, r) as br), (Leaf (k, lis) as lf) ->
            if k &&& (b - 1) = p then
                if k &&& b = 0 then
                    match combine op z l lf with
                    | Empty -> r
                    | l' -> Branch (p, b, l', r)
                else
                    match combine op z r lf with
                    | Empty -> l
                    | r' -> Branch (p, b, l, r')
            else
                newbranch p br k lf

        | Branch (p1, b1, l1, r1), Branch (p2, b2, l2, r2) ->
            if b1 < b2 then
                if p2 &&& (b1 - 1) <> p1 then
                    newbranch p1 t1 p2 t2
                elif p2 &&& b1 = 0 then
                    match combine op z l1 t2 with
                    | Empty -> r1
                    | l -> Branch (p1, b1, l, r1)
                else
                    match combine op z r1 t2 with
                    | Empty -> l1
                    | r -> Branch (p1, b1, l1, r)

            elif b2 < b1 then
                if p1 &&& (b2 - 1) <> p2 then
                    newbranch p1 t1 p2 t2
                elif p1 &&& b2 = 0 then
                    match combine op z t1 l2 with
                    | Empty -> r2
                    | l -> Branch (p2, b2, l, r2)
                else
                    match combine op z t1 r2 with
                    | Empty -> l2
                    | r -> Branch (p2, b2, l2, r)

            elif p1 = p2 then
                match combine op z l1 l2, combine op z r1 r2 with
                | Empty, x
                | x, Empty -> x
                | l, r ->
                    Branch (p1, b1, l, r)
            else
                newbranch p1 t1 p2 t2

    (|->), combine

// ------------------------------------------------------------------------- //
// Special case of point function.                                           //
// ------------------------------------------------------------------------- //

// Finite Partial Functions (FPF)
// To create a new funtion in the FPF defined only for the value x and mapping it to y.
// pg. 621
let (|=>) x y = 
    (x |-> y) undefined

// ------------------------------------------------------------------------- //
// Idiom for a mapping zipping domain and range lists.                       //
// ------------------------------------------------------------------------- //

// pg. 621
let fpf xs ys =
    List.foldBack2 (|->) xs ys undefined

// ------------------------------------------------------------------------- //
// Grab an arbitrary element.                                                //
// ------------------------------------------------------------------------- //

// Not in book
// Support fucntion for end user use if needed. 
// Not used in handbook code.
let rec choose t =
    match t with
    | Empty ->
        failwith "choose: completely undefined function"
    | Leaf (_, l) ->
        // NOTE : This will fail (crash) when 'l' is an empty list!
        List.head l
    | Branch (b, p, t1, t2) ->
        choose t1

// ------------------------------------------------------------------------- //
// Install a (trivial) printer for finite partial functions.                 //
// ------------------------------------------------------------------------- //

// Not in book
//let print_fpf (f : func<'a,'b>) = printf "<func>"

// ------------------------------------------------------------------------- //
// Related stuff for standard functions.                                     //
// ------------------------------------------------------------------------- //

// pg. 618
let valmod a y f x =
    if x = a then y
    else f x
    
// pg. 618
let undef x =
    failwith "undefined function"

// ------------------------------------------------------------------------- //
// Union-find algorithm.                                                     //
// ------------------------------------------------------------------------- //

// Not in book
// Type for use with union-find algorithm  
type pnode<'a> =
    | Nonterminal of 'a 
    | Terminal of 'a * int
    
// Not in book
// Type for use with union-find algorithm 
// HOL Light: termequivalence
type partition<'a> = Partition of func<'a, pnode<'a>>

// EGT - print Partition
let rec string_of_partition par =
    let rec string_of_partition_interal par level =
        match par with
        | Partition x -> 
            let pt = string_of_patricia_tree_with_level x 1
            "Partition\n" + pt
    string_of_partition_interal par 0

let sprint_partition pt =
    string_of_partition pt

let print_partition pt =
    printfn "%O" (sprint_partition pt) |> ignore
    
// Not in book
// Support function for use with union-find algorithm 
let rec terminus (Partition f as ptn) a =
    match apply f a with
    | Terminal (p, q) ->
        p, q
    | Nonterminal b ->
        terminus ptn b
        
// Not in book
// Support function for use with union-find algorithm 
let tryterminus ptn a =
    try terminus ptn a
    with _ -> (a, 1)
        
// pg. 622
let canonize ptn a =
    fst <| tryterminus ptn a

// pg. 622
let equivalent eqv a b =
    canonize eqv a = canonize eqv b
    
// pg. 622
let equate (a, b) (Partition f as ptn) =
    let a', na = tryterminus ptn a
    let b', nb = tryterminus ptn b
    if a' = b' then f
    elif na <= nb then
        List.foldBack id [a' |-> Nonterminal b'; b' |-> Terminal (b', na + nb)] f
    else
        List.foldBack id [b' |-> Nonterminal a'; a' |-> Terminal (a', na + nb)] f
    |> Partition

// pg. 622
let unequal = Partition undefined
    
// pg. 622
let equated (Partition f) = dom f

// ------------------------------------------------------------------------- //
// First number starting at n for which p succeeds.                          //
// ------------------------------------------------------------------------- //

// pg. 618
let rec first n p =
    if p n then n
    else first (n + Int 1) p

/// Write from a StringWriter to a string
let writeToString fn = 
    use sw = new System.IO.StringWriter()
    fn sw
    sw.ToString()

