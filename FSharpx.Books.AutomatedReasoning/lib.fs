// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

/// Misc library functions to set up a nice environment.
[<AutoOpen>]
module FSharpx.Books.AutomatedReasoning.lib

open LanguagePrimitives
open FSharpx.Compatibility.OCaml.Num

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
// OCaml: val ( ** ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b = <fun>
// F#:    val ( << ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
    // NOTE : The ( ** ) operator has been replaced with the equivalent,
    // built-in F# operator ( << ).

// ------------------------------------------------------------------------- //
// GCD and LCM on arbitrary-precision numbers.                               //
// ------------------------------------------------------------------------- //

// pg. 618
// OCaml: val gcd_num : num -> num -> num = <fun>
// F#:    val gcd_num : num -> num -> num
let rec gcd_num (n1 : num) (n2 : num) =
    if n2 = GenericZero then n1
    else gcd_num n2 (n1 % n2)
            
// pg. 618
// OCaml: val lcm_num : num -> num -> num = <fun>
// F#:    val lcm_num : num -> num -> num
let lcm_num (n1 : num) (n2 : num) =
    (abs (n1 * n2)) / gcd_num n1 n2

// ------------------------------------------------------------------------- //
// A useful idiom for "non contradictory" etc.                               //
// ------------------------------------------------------------------------- //

// pg. 618
// OCaml: val non : ('a -> bool) -> 'a -> bool = <fun>
// F#:    val non : ('a -> bool) -> 'a -> bool
let inline non p x =
    not <| p x

// ------------------------------------------------------------------------- //
// Kind of assertion checking.                                               //
// ------------------------------------------------------------------------- //

// pg. ???
// OCaml: val check : ('a -> bool) -> 'a -> 'a = <fun>
// F#:    val check : ('a -> bool) -> 'a -> 'a
let check p x =
    #if DEBUG
    assert (p x)
    x
    #else
    if p x then x
    else failwith "check"
    #endif

// ------------------------------------------------------------------------- //
// Repetition of a function.                                                 //
// ------------------------------------------------------------------------- //

// pg. 612
// OCaml: val funpow : int -> ('a -> 'a) -> 'a -> 'a = <fun>
// F#:    val funpow : int -> ('a -> 'a) -> 'a -> 'a
let rec funpow n f x =
    if n < 1 then x
    else funpow (n - 1) f (f x)

// pg. 618
// OCaml: val can : ('a -> 'b) -> 'a -> bool = <fun>
// F#:    val can : ('a -> 'b) -> 'a -> bool 
let can f x = 
    try 
        f x |> ignore
        true
    with Failure _ ->
        false

// pg. 618
// OCaml: val repeat : ('a -> 'a) -> 'a -> 'a = <fun>
// F#:    val repeat : ('a -> 'a) -> 'a -> 'a
let rec repeat f x = 
    try repeat f (f x)
    with Failure _ -> x

// ------------------------------------------------------------------------- //
// Handy list operations.                                                    //
// ------------------------------------------------------------------------- //

// pg. 618
// OCaml: val ( -- ) : int -> int -> int list = <fun>
// F#:    val ( -- ) : int -> int -> int list
let inline (--) (m : int) (n : int) = [m..n]

// pg.618
// OCaml: val ( --- ) : num -> num -> num list = <fun>
// F#:    val ( --- ) : num -> num -> num list
let inline (---) (m : num) (n : num) = [m..n]

// pg. 619
// OCaml: val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list = <fun>
// F#:    val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
// use List.map2
//    let rec map2 f l1 l2 =
//        match (l1,l2) with
//        | [],[] -> []
//        | (h1::t1),(h2::t2) -> let h = f h1 h2 in h::(map2 f t1 t2)
//        | _ -> failwith "map2: length mismatch"

// pg. 619
// OCaml: val rev : 'a list -> 'a list = <fun>
// F#:    val rev : 'a list -> 'a list
// use List.rev
//    let rev =
//        let rec rev_append acc l =
//            match l with
//            | [] -> acc
//            | h::t -> rev_append (h::acc) t
//        fun l -> rev_append [] l

// pg. 619
// OCaml: val hd :   'a list -> 'a = <fun>
// F#:    val head : 'a list -> 'a
//    let inline hd l =
//        List.head l
        
// pg. 619
// OCaml: val tl :   'a list -> 'a list = <fun>
// F#:    val tail : 'a list -> 'a list
//    let inline tl l =
//        match l with
//        | h::t -> t
//        | _ -> failwith "tl"

// pg. 619 - list iterator
// OCaml: val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b = <fun>
// F#:    val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
//    let inline itlist f l b =
//        List.foldBack f l b
        
// pg. 619
// OCaml: val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a = <fun>
// F#:    val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
let rec end_itlist f l =
    match l with
    | [] -> failwith "end_itlist"
    | [x] -> x
    | hd :: tl ->
        f hd (end_itlist f tl)
        
// pg. 619
// OCaml: val itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c = <fun>
// F#:    val itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
// F# : Use List.foldBack2
//    let inline itlist2 f l1 l2 b =
//        // TEMP : Leave this function as an alias for List.foldBack2 until
//        // all of the usages can be replaced.
//        List.foldBack2 f l1 l2 b
        
// pg. 619
// OCaml: val zip : 'a list -> 'b list -> ('a * 'b) list = <fun>
// F#:    val zip : 'a list -> 'b list -> ('a * 'b) list
// use List.zip
//    let rec zip l1 l2 =
//        match (l1,l2) with
//        | ([],[])         -> []
//        | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
//        | _               -> failwith "zip"

// pg. 619
// OCaml: val forall : ('a -> bool) -> 'a list -> bool = <fun>
// F#:    val forall : ('a -> bool) -> 'a list -> bool
// Use List.forall
//    let rec forall p l =
//        match l with
//        | []   -> true
//        | h::t -> p(h) && forall p t
        
// pg. 619
// OCaml: val exists : ('a -> bool) -> 'a list -> bool = <fun>
// F#:    val exists : ('a -> bool) -> 'a list -> bool
// Use List.exists
//    let rec exists p l =
//        match l with
//        | [] -> false
//        | h::t -> p(h) || exists p t
        
// pg. 619
// OCaml: val partition : ('a -> bool) -> 'a list -> 'a list * 'a list = <fun>
// F#:    val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
// Use List.partition
//    let partition p l =
//        itlist (fun a (yes,no) -> if p a then a::yes,no else yes,a::no) l ([],[])
        
// pg. 619
// OCaml: val filter : ('a -> bool) -> 'a list -> 'a list = <fun>
// F#:    val filter : ('a -> bool) -> 'a list -> 'a list
// Use List.filter
//    let filter p l = fst(partition p l)
    
// pg. 619
// OCaml: val length : 'a list -> int = <fun>
// F#:    val length : 'a list -> int
// Use List.length
//    let length =
//        let rec len k l =
//            if l = [] then k else len (k + 1) (List.tail l)
//        fun l -> len 0 l
        
// pg. 619
// OCaml: val last : 'a list -> 'a = <fun>
// F#:    val last : 'a list -> 'a
// val last : 'a list -> 'a
let rec last l =
    match l with
    | [] ->
        failwith "Cannot get the last element of an empty list."
    | [x] -> x
    | _ :: tl ->
        last tl
        
/// Private, recursive implementation of 'butlast' which
/// improves performance by using continuation-passing-style.
let rec private butlastImpl lst cont =
    match lst with
    | [] ->
        failwith "butlastImpl"
    | [_] ->
        cont []
    | hd :: tl ->
        butlastImpl tl <| fun lst' ->
            cont (hd :: lst')

// pg. 619
// OCaml: val butlast : 'a list -> 'a list = <fun>
// F#:    val butlast : 'a list -> 'a list
// val butlast : 'a list -> 'a list
let butlast l =
    butlastImpl l id
        
// pg. 619
// OCaml: val find : ('a -> bool) -> 'a list -> 'a = <fun>
// F#:    val find : ('a -> bool) -> 'a list -> 'a
//
// Use List.tryFind
// F#: List.tryFind : ('a -> bool) -> 'a list -> 'a option
//
// Note: In comparing exceptions in terms of computing time, 
// Ocaml's exceptions are inexpensive in comparison with F# exceptions.
// To avoid exceptions from F# List.find, use F# List.tryFind whcih
// does not return an exception if an item is not found.
//    let rec find p l =
//        match l with
//        | [] -> failwith "find"
//        | (h::t) -> if p(h) then h else find p t
        
// pg. 619
// OCaml: val el : int -> 'a list -> 'a = <fun>
// F#:    val el : int -> 'a list -> 'a
//    let inline el n l =
//        List.nth l n

// pg. 619
// OCaml: val map : ('a -> 'b) -> 'a list -> 'b list = <fun>
// F#:    val map : ('a -> 'b) -> 'a list -> 'b list
// Use List.map
//    let map f =
//        let rec mapf l =
//            match l with
//            | []     -> []
//            | (x::t) -> let y = f x in y::(mapf t)
//        mapf
        
// pg. 620
// OCaml: val allpairs : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list = <fun>
// F#:    val allpairs : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
let rec allpairs f l1 l2 =
    match l1 with
    | [] -> []
    | h1 :: t1 ->
        List.foldBack (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)

// pg. 620
// OCaml: val distinctpairs : 'a list -> ('a * 'a) list = <fun>
// F#:    val distinctpairs : 'a list -> ('a * 'a) list
/// Given a list, creates a new list containing all unique 2-combinations
/// of the list elements. (I.e., (x, y) and (y, x) are the same and
/// will only be included once.)
let rec distinctpairs l =
    match l with
    | [] -> []
    | x :: t ->
        List.foldBack (fun y a -> (x, y) :: a) t (distinctpairs t)
        
// pg. 619
// OCaml: val chop_list : int -> 'a list -> 'a list * 'a list = <fun>
// F#:    val chop_list : int -> 'a list -> 'a list * 'a list
let rec chop_list n l =
    if n = 0 then [], l
    else
        try
            let m, l' = chop_list (n - 1) (List.tail l) 
            (List.head l) :: m, l'
        with _ ->
            failwith "chop_list"
        
// pg. 619
// OCaml: val replicate : int -> 'a -> 'a list = <fun>
// F#:    val replicate : int -> 'a -> 'a list
// Use List.replicate
//    let replicate n a = List.map (fun x -> a) (1--n)
    
// pg. 619
// OCaml: val insertat : int -> 'a -> 'a list -> 'a list = <fun>
// F#:    val insertat : int -> 'a -> 'a list -> 'a list
let rec insertat i x l =
    if i = 0 then x :: l
    else
        match l with
        | [] -> failwith "insertat: list too short for position to exist"
        | h :: t ->
            h :: (insertat (i - 1) x t)
        
// pg. 619
// OCaml: val forall2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool = <fun>
// F#:    val forall2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
// Use List.forall2
//    let rec forall2 p l1 l2 =
//        match (l1,l2) with
//        | [],[] -> true
//        | (h1::t1,h2::t2) -> p h1 h2 && forall2 p t1 t2
//        | _ -> false
        
// pg. 619
// OCaml: val index : 'a -> 'a list -> int = <fun>
// F#:    val index : 'a -> ('a list -> int) when 'a : comparison
let inline index x xs = List.findIndex ((=) x) xs
        
// pg. 619
// OCaml: val unzip : ('a * 'b) list -> 'a list * 'b list = <fun>
// F#:    val unzip : ('a * 'b) list -> 'a list * 'b list
// Use List.unzip
//    let rec unzip l =
//        match l with
//        | [] -> [],[]
//        | (x,y)::t ->
//            let xs,ys = unzip t in x::xs,y::ys

// ------------------------------------------------------------------------- //
// Whether the first of two items comes earlier in the list.                 //
// ------------------------------------------------------------------------- //

// pg. 619
// OCaml: val earlier : 'a list -> 'a -> 'a -> bool = <fun>
// F#:    val earlier : 'a list -> 'a -> 'a -> bool when 'a : comparison
let rec earlier l x y =
    match l with
    | [] -> false
    | h :: t ->
        (compare h y <> 0) && (compare h x = 0 || earlier t x y)
        

// ------------------------------------------------------------------------- //
// Application of (presumably imperative) function over a list.              //
// ------------------------------------------------------------------------- //

// pg. 619
// OCaml: val do_list : ('a -> 'b) -> 'a list -> unit = <fun>
// F#:    val do_list : ('a -> unit) -> 'a list -> unit
// NOTE : 'do_list' has been replaced with the built-in F# function List.iter.

// ------------------------------------------------------------------------- //
// Association lists.                                                        //
// ------------------------------------------------------------------------- //

// pg. 620
// OCaml: val assoc : 'a -> ('a * 'b) list -> 'b = <fun>
// F#:    val assoc : 'a -> ('a * 'b) list -> 'b when 'a : comparison
let rec assoc a l =
    match l with
    | [] -> failwith "find"
    | (x, y) :: t ->
        if compare x a = 0 then y
        else assoc a t

// pg. ???
// OCaml: val rev_assoc : 'a -> ('b * 'a) list -> 'b = <fun>
// F#:    val rev_assoc : 'a -> ('b * 'a) list -> 'b when 'a : comparison
let rec rev_assoc a l =
    match l with
    | [] -> failwith "find"
    | (x, y) :: t ->
        if compare y a = 0 then x
        else rev_assoc a t
        

// ------------------------------------------------------------------------- //
// Merging of sorted lists (maintaining repetitions).                        //
// ------------------------------------------------------------------------- //

// pg. ???
// OCaml: val merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list = <fun>
// F#:    val merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
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
// OCaml: val sort : ('a -> 'a -> bool) -> 'a list -> 'a list = <fun>
// F#:    val sort : ('a -> 'a -> bool) -> ('a list -> 'a list) when 'a : equality
let rec mergepairs ord l1 l2 =
    match l1, l2 with
    | [s], [] -> s
    | l, [] ->
        mergepairs ord [] l
    | l, [s1] ->
        mergepairs ord (s1 :: l) []
    | l, s1 :: s2 :: ss ->
        mergepairs ord ((merge ord s1 s2) :: l) ss

let sort ord l =
    match l with
    | [] -> []
    | l ->
        mergepairs ord [] (List.map (fun x -> [x]) l)

// ------------------------------------------------------------------------- //
// Common measure predicates to use with "sort".                             //
// ------------------------------------------------------------------------- //

// pg. 619
// OCaml: val increasing : ('a -> 'b) -> 'a -> 'a -> bool = <fun>
// F#:    val increasing : ('a -> 'b) -> 'a -> 'a -> bool when 'b : comparison
let increasing f x y =
    compare (f x) (f y) < 0
    
// pg. 619
// OCaml: val decreasing : ('a -> 'b) -> 'a -> 'a -> bool = <fun>
// F#:    val decreasing : ('a -> 'b) -> 'a -> 'a -> bool when 'b : comparison
let decreasing f x y =
    compare (f x) (f y) > 0

// ------------------------------------------------------------------------- //
// Eliminate repetitions of adjacent elements, with and without counting.    //
// ------------------------------------------------------------------------- //

// pg. 619
// OCaml: val uniq : 'a list -> 'a list = <fun>
// F#:    val uniq : 'a list -> 'a list when 'a : comparison
let rec uniq l =
    match l with
    | x :: (y :: _ as t) -> 
        let t' = uniq t
        if compare x y = 0 then t' 
        else
            if t' = t then l 
            else x :: t'
    | _ -> l

// pg. ???
// OCaml: val repetitions : 'a list -> ('a * int) list = <fun>
// F#:    val repetitions : ('a list -> ('a * int) list) when 'a : comparison
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
// OCaml: val tryfind : ('a -> 'b) -> 'a list -> 'b = <fun>
// F#:    val tryFind : ('a -> 'b) -> 'a list -> 'b
let rec tryfind f l =
    match l with
    | [] ->
        failwith "tryfind"
    | h :: t ->
        try f h
        with Failure _ ->
            tryfind f t
        
// pg. 619
// OCaml: val mapfilter : ('a -> 'b) -> 'a list -> 'b list = <fun>
// F#:    val mapfilter : ('a -> 'b) -> 'a list -> 'b list
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

// pg. ???
// OCaml: val optimize : ('a -> 'a -> bool) -> ('b -> 'a) -> 'b list -> 'b =  <fun>
// F#:    val optimize : ('a -> 'a -> bool) -> ('b -> 'a) -> 'b list -> 'b
let optimize ord f lst =
    lst
    |> List.map (fun x -> x, f x)
    |> end_itlist (fun (_, y1 as p1) (_, y2 as p2) ->
        if ord y1 y2 then p1 else p2)
    |> fst
                        
// pg. 620
// OCaml: val maximize : ('a -> 'b) -> 'a list -> 'a = <fun>
// F#:    val maximize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
let maximize f l =
    optimize (>) f l
    
// pg. 620
// OCaml: val minimize : ('a -> 'b) -> 'a list -> 'a = <fun>
// F#:    val minimize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
let minimize f l =
    optimize (<) f l

// ------------------------------------------------------------------------- //
// Set operations on ordered lists.                                          //
// ------------------------------------------------------------------------- //

// pg. 620
// OCaml: val setify : 'a list -> 'a list = <fun>
// F#:    val setify : ('a list -> 'a list) when 'a : comparison
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
// OCaml: val union : 'a list -> 'a list -> 'a list = <fun>
// F#:    val union : ('a list -> 'a list -> 'a list) when 'a : comparison
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
// OCaml: val intersect : 'a list -> 'a list -> 'a list = <fun>
// F#:    val intersect : ('a list -> 'a list -> 'a list) when 'a : comparison
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
// OCaml: val subtract : 'a list -> 'a list -> 'a list = <fun>
// F#:    val subtract : ('a list -> 'a list -> 'a list) when 'a : comparison
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
// OCaml: val subset : 'a list -> 'a list -> bool = <fun>
// F#:    val subset : 'a list -> 'a list -> bool when 'a : comparison
// OCaml: val psubset : 'a list -> 'a list -> bool = <fun>
// F#:    val psubset : ('b list -> 'b list -> bool) when 'b : comparison
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
// OCaml: val set_eq : 'a list -> 'a list -> bool = <fun>
// F#:    val set_eq : 'a list -> 'a list -> bool when 'a : comparison
let rec set_eq s1 s2 =
    setify s1 = setify s2
    
// pg. 620
// OCaml: val insert : 'a -> 'a list -> 'a list = <fun>
// F#:    val insert : 'a -> 'a list -> 'a list when 'a : comparison
let insert x s =
    union [x] s
    
// pg. 620
// OCaml: val image : ('a -> 'b) -> 'a list -> 'b list = <fun>
// F#:    val image : ('a -> 'b) -> 'a list -> 'b list when 'b : comparison
let image f s =
    setify (List.map f s)

// ------------------------------------------------------------------------- //
// Union of a family of sets.                                                //
// ------------------------------------------------------------------------- //

// pg. 620
// OCaml: val unions : 'a list list -> 'a list = <fun>
// F#:    val unions : 'a list list -> 'a list when 'a : comparison
let unions s =
    List.foldBack (@) s []
    |> setify

// ------------------------------------------------------------------------- //
// List membership. This does *not* assume the list is a set.                //
// ------------------------------------------------------------------------- //

// pg. 620
// OCaml: val mem : 'a -> 'a list -> bool = <fun>
// F#:    val mem : 'a -> 'a list -> bool when 'a : equality
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
// OCaml: val allsets : int -> 'a list -> 'a list list = <fun>
// F#:    val allsets : int -> 'a list -> 'a list list when 'a : comparison
let rec allsets m l =
    if m = 0 then [[]]
    else
        match l with
        | [] -> []
        | h :: t ->
            union (image (fun g -> h :: g) (allsets (m - 1) t)) (allsets m t)
        
// pg. 620
// OCaml: val allsubsets : 'a list -> 'a list list = <fun>
// F#:    val allsubsets : 'a list -> 'a list list when 'a : comparison
let rec allsubsets s =
    match s with
    | [] -> [[]]
    | a :: t ->
        let res = allsubsets t
        union (image (fun b -> a :: b) res) res
                    
// pg. 620
// OCaml: val allnonemptysubsets : 'a list -> 'a list list = <fun>
// F#:    val allnonemptysubsets : 'a list -> 'a list list when 'a : comparison
let allnonemptysubsets s =
    subtract (allsubsets s) [[]]

// pg. 619
// ------------------------------------------------------------------------- //
// Explosion and implosion of strings.                                       //
// ------------------------------------------------------------------------- //

// pg. 619
// OCaml: val explode : string -> string list = <fun>
// F#:    val explode : string -> string list
let explode s =
    let mutable charList = []
    for i = (String.length s) - 1 downto 0 do
        charList <-
            s.[i].ToString() :: charList
    charList
        
// pg. 619
// OCaml: val implode : string list -> string = <fun>
// F#:    val implode : string list -> string
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
// OCaml: val time : ('a -> 'b) -> 'a -> 'b = <fun>
// F#:    val time : ('a -> 'b) -> 'a -> 'b
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
// OCaml: 
//   type ('a, 'b) func =
//     Empty
//   | Leaf of int * ('a * 'b) list
//   | Branch of int * int * ('a, 'b) func * ('a, 'b) func
// F#:    
type func<'a,'b> =
    | Empty
    | Leaf of int * ('a * 'b) list
    | Branch of int * int * func<'a,'b> * func<'a,'b>

// ------------------------------------------------------------------------- //
// Undefined function.                                                       //
// ------------------------------------------------------------------------- //

// pg. 621
// OCaml: val undefined : ('a, 'b) func = Empty
// F#:    val undefined : func<'a,'b>
let undefined = Empty

// ------------------------------------------------------------------------- //
// In case of equality comparison worries, better use this.                  //
// ------------------------------------------------------------------------- //

// pg. 621
// OCaml: val is_undefined : ('a, 'b) func -> bool = <fun>
// F#:    val is_undefined : func<'a,'b>   -> bool
let is_undefined = function
    | Empty -> true
    | _     -> false

// ------------------------------------------------------------------------- //
// Operation analogous to "map" for lists.                                   //
// ------------------------------------------------------------------------- //

// pg. 621
// OCaml: val mapf : ('a -> 'b)  -> ('c, 'a) func -> ('c, 'b) func = <fun>
// F#:    val mapf : (('a -> 'b) -> func<'c,'a>   -> func<'c,'b>)
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

// pg. ???
// OCaml: val foldl : ('a -> 'b -> 'c -> 'a) -> 'a -> ('b, 'c) func -> 'a = <fun>
// F#:    val foldl : (('a -> 'b -> 'c -> 'a) -> 'a -> func<'b,'c> -> 'a)
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
        
// pg. ???
// OCaml: val foldr :  ('a -> 'b -> 'c -> 'c) -> ('a, 'b) func -> 'c -> 'c = <fun>
// F#:    val foldr : (('a -> 'b -> 'c -> 'c) -> func<'a,'b>   -> 'c -> 'c)
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
// OCaml: val graph : ('a, 'b) func -> ('a * 'b) list = <fun>
// F#:    val graph : func<'a,'b>   -> ('a * 'b) list when 'a : comparison and 'b : comparison
let graph f =
    foldl (fun a x y -> (x, y) :: a) [] f
    |> setify
    
// pg. 621
// OCaml: val dom : ('a, 'b) func -> 'a list = <fun>
// F#:    val dom : func<'a,'b>   -> 'a list when 'a : comparison
let dom f =
    foldl (fun a x y -> x :: a) [] f
    |> setify
    
// pg. 621
// OCaml: val ran : ('a, 'b) func -> 'b list = <fun>
// F#:    val ran : func<'a,'b>   -> 'b list when 'b : comparison
let ran f =
    foldl (fun a x y -> y :: a) [] f
    |> setify

// ------------------------------------------------------------------------- //
// Application.                                                              //
// ------------------------------------------------------------------------- //

// pg. 621
// OCaml: val applyd :  ('a, 'b) func -> ('a -> 'b) -> 'a -> 'b = <fun>
// F#:    val applyd : (func<'a,'b>   -> ('a -> 'b) -> 'a -> 'b) when 'a : comparison
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
// OCaml: val apply : ('a, 'b) func -> 'a -> 'b = <fun>
// F#:    val apply : func<'a,'b>   -> ('a -> 'b) when 'a : comparison
let apply f =
    applyd f (fun _ -> failwith "apply")

// EGT
let apply_none f =
    applyd f (fun _ -> None)

// pg. 621
// OCaml: val tryapplyd : ('a, 'b) func -> 'a -> 'b -> 'b = <fun>
// F#:    val tryapplyd : func<'a,'b>   -> 'a -> 'b -> 'b when 'a : comparison
let tryapplyd f a d =
    applyd f (fun _ -> d) a

// pg. 621
// OCaml: val tryapplyl : ('a, 'b list) func -> 'a -> 'b list = <fun>
// F#:    val tryapplyl : func<'a,'b list>   -> 'a -> 'b list when 'a : comparison
let tryapplyl f x =
    tryapplyd f x []
    
// pg. 621
// OCaml: val defined : ('a, 'b) func -> 'a -> bool = <fun>
// F#:    val defined : func<'a,'b>   -> 'a -> bool when 'a : comparison
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
// OCaml: val undefine :  'a -> ('a, 'b) func -> ('a, 'b) func = <fun>
// F#:    val undefine : ('a -> func<'a,'b>   -> func<'a,'b>) when 'a : comparison and 'b : equality
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
// pg. 621
// OCaml: val ( |-> ) :  'a -> 'b -> ('a, 'b) func -> ('a, 'b) func = <fun>
// F#:    val ( |-> ) : ('a -> 'b -> func<'a,'b>   -> func<'a,'b>) when 'a : comparison
// OCaml: val combine :  ('a -> 'a -> 'a) -> ('a -> bool) -> ('b, 'a) func -> ('b, 'a) func -> ('b, 'a) func = <fun>
// F#:    val combine : (('c -> 'c -> 'c) -> ('c -> bool) -> func<'d,'c>   -> func<'d,'c>   -> func<'d,'c>) when 'c : equality and 'd : comparison
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
// OCaml: val ( |=> ) : 'a -> 'b -> ('a, 'b) func = <fun>
// F#:    val ( |=> ) : 'a -> 'b -> func<'a,'b> when 'a : comparison
let (|=>) x y = 
    (x |-> y) undefined

// ------------------------------------------------------------------------- //
// Idiom for a mapping zipping domain and range lists.                       //
// ------------------------------------------------------------------------- //

// pg. 621
// OCaml: val fpf : 'a list -> 'b list -> ('a, 'b) func = <fun>
// F#:    val fpf : 'a list -> 'b list -> func<'a,'b> when 'a : comparison
let fpf xs ys =
    List.foldBack2 (|->) xs ys undefined

// ------------------------------------------------------------------------- //
// Grab an arbitrary element.                                                //
// ------------------------------------------------------------------------- //

// pg. ???
// OCaml: val choose : ('a, 'b) func -> 'a * 'b = <fun>
// F#:    val choose : func<'a,'b>   -> 'a * 'b
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

// pg. ???
// OCaml: val print_fpf : ('a, 'b) func -> unit = <fun>
// F#:    val print_fpf : func<'a,'b>   -> unit
let print_fpf (f : func<'a,'b>) = printf "<func>"

// ------------------------------------------------------------------------- //
// Related stuff for standard functions.                                     //
// ------------------------------------------------------------------------- //

// pg. 618
// OCaml: val valmod : 'a -> 'b -> ('a -> 'b) -> 'a -> 'b = <fun>
// F#:    val valmod : 'a -> 'b -> ('a -> 'b) -> 'a -> 'b when 'a : equality
let valmod a y f x =
    if x = a then y
    else f x
    
// pg. 618
// OCaml: val undef : 'a -> 'b = <fun>
// F#:    val undef : 'a -> 'b
let undef x =
    failwith "undefined function"

// ------------------------------------------------------------------------- //
// Union-find algorithm.                                                     //
// ------------------------------------------------------------------------- //

// pg. ???
// OCaml: type 'a pnode = Nonterminal of 'a | Terminal of 'a * int
// F#:    
type pnode<'a> =
    | Nonterminal of 'a 
    | Terminal of 'a * int
    
// pg. 619
// OCaml: type 'a partition = Partition of ('a, 'a pnode) func
// F#:    type 'a partition = | Partition of func<'a,'a pnode>
type partition<'a> = Partition of func<'a, pnode<'a>>
    
// pg. ???
// OCaml: val terminus : 'a partition -> 'a -> 'a * int = <fun>
// F#:    val terminus : 'a partition -> 'a -> 'a * int when 'a : comparison
let rec terminus (Partition f as ptn) a =
    match apply f a with
    | Terminal (p, q) ->
        p, q
    | Nonterminal b ->
        terminus ptn b
        
// pg. ???
// OCaml: val tryterminus : 'a partition -> 'a -> 'a * int = <fun>
// F#:    val tryterminus : 'a partition -> 'a -> 'a * int when 'a : comparison
let tryterminus ptn a =
    try terminus ptn a
    with _ -> (a, 1)
        
// pg. ???
// OCaml: val canonize : 'a partition -> 'a -> 'a = <fun>
// F#:    val canonize : 'a partition -> 'a -> 'a when 'a : comparison
let canonize ptn a =
    fst <| tryterminus ptn a

// pg. 622
// OCaml: val equivalent : 'a partition -> 'a -> 'a -> bool = <fun>
// F#:    val equivalent : 'a partition -> 'a -> 'a -> bool when 'a : comparison
let equivalent eqv a b =
    canonize eqv a = canonize eqv b
    
// pg. 622
// OCaml: val equate : 'a * 'a -> 'a partition -> 'a partition = <fun>
// F#:    val equate : 'a * 'a -> 'a partition -> 'a partition when 'a : comparison
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
// OCaml: val unequal : 'a partition = Partition <func>
// F#:    val unequal : 'a partition
let unequal = Partition undefined
    
// pg. 622
// OCaml: val equated : 'a partition -> 'a list = <fun>
// F#:    val equated : 'a partition -> 'a list when 'a : comparison
let equated (Partition f) = dom f

// ------------------------------------------------------------------------- //
// First number starting at n for which p succeeds.                          //
// ------------------------------------------------------------------------- //

// pg. 618
// OCaml: val first : num -> (num -> bool) -> num = <fun>
// F#:    val first : num -> (num -> bool) -> num
let rec first n p =
    if p n then n
    else first (n + Int 1) p

// A general scheme to use StringWriter
let writeToString fn = 
    use sw = new System.IO.StringWriter()
    fn sw
    sw.ToString()
