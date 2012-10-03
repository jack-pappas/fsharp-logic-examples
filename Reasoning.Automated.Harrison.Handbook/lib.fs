// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

/// Misc library functions to set up a nice environment.
[<AutoOpen>]
module lib =
    open LanguagePrimitives
    open FSharpx.Compatibility.OCaml
    open Num

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
    // TODO : Optimize to use imperative loop instead of recursion.
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
        with _ -> false

    // pg. 618
    // OCaml: val repeat : ('a -> 'a) -> 'a -> 'a = <fun>
    // F#:    val repeat : ('a -> 'a) -> 'a -> 'a
    let rec repeat f x = 
        try repeat f (f x)
        with _ -> x

// ------------------------------------------------------------------------- //
// Handy list operations.                                                    //
// ------------------------------------------------------------------------- //
        
    // pg. 619
    // OCaml: val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a = <fun>
    // F#:    val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
    let inline end_itlist f l =
        List.reduceBack f l
        
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
        
    
    let rec private allpairsImpl f l1 l2 cont =
        match l1 with
        | [] ->
            cont []
        | h1 :: t1 ->
            allpairsImpl f t1 l2 <| fun result ->
                (l2, result)
                ||> List.foldBack (fun x a -> f h1 x :: a)
                |> cont
    
    // pg. 620
    // OCaml: val allpairs : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list = <fun>
    // F#:    val allpairs : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
    let allpairs f l1 l2 =
        allpairsImpl f l1 l2 id

    // pg. 620
    // OCaml: val distinctpairs : 'a list -> ('a * 'a) list = <fun>
    // F#:    val distinctpairs : 'a list -> ('a * 'a) list
    let rec private distinctpairsImpl l cont =
        match l with
        | [] ->
            cont []
        | x :: t ->
            distinctpairsImpl t <| fun result ->
                (t, result)
                ||> List.foldBack (fun y a -> (x, y) :: a)
                |> cont

    let distinctpairs l =
        distinctpairsImpl l id
        
    // pg. 619
    // OCaml: val chop_list : int -> 'a list -> 'a list * 'a list = <fun>
    // F#:    val chop_list : int -> 'a list -> 'a list * 'a list
    // Takes the first n items from a list. Returns those items as a list,
    // along with any items remaining in the original list.
    // TODO : Optimize using continuation-passing style.
    let rec chop_list n l =
        if n = 0 then [], l
        else
            try
                let m, l' = chop_list (n - 1) (List.tail l) 
                (List.head l) :: m, l'
            with _ ->
                failwith "chop_list"
    
    // pg. 619
    // OCaml: val insertat : int -> 'a -> 'a list -> 'a list = <fun>
    // F#:    val insertat : int -> 'a -> 'a list -> 'a list
    // TODO : Optimize using continuation-passing style.
    let rec insertat i x l =
        if i = 0 then x :: l
        else
            match l with
            | [] -> failwith "insertat: list too short for position to exist"
            | h :: t ->
                h :: (insertat (i - 1) x t)
        
    // pg. 619
    // OCaml: val index : 'a -> 'a list -> int = <fun>
    // F#:    val index : 'a -> ('a list -> int) when 'a : comparison
    let inline index x =
        List.findIndex ((=) x)

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

    //
    let rec private mergeImpl comparer l1 l2 cont =
        match l1, l2 with
        | [], x
        | x, [] ->
            cont x
        | h1 :: t1, h2 :: t2 ->
            if comparer h1 h2 then
                mergeImpl comparer t1 l2 <| fun lst ->
                    cont (h1 :: lst)
            else
                mergeImpl comparer l1 t2 <| fun lst ->
                    cont (h2 :: lst)

    // pg. ???
    // OCaml: val merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list = <fun>
    // F#:    val merge : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
    let merge comparer l1 l2 =
        mergeImpl comparer l1 l2 id

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

    //
    let rec private uniqImpl l cont =
        match l with
        | x :: (y :: _ as t) ->
            uniqImpl t <| fun t' ->
                if compare x y = 0 then t' 
                elif t' = t then l 
                else x :: t'
                |> cont
        | _ ->
            cont l

    // pg. 619
    // OCaml: val uniq : 'a list -> 'a list = <fun>
    // F#:    val uniq : 'a list -> 'a list when 'a : comparison
    // OPTIMIZE : Replace this (and the private implementation) with
    // a simpler implementation which folds over the list and uses an
    // F# set to track the "seen" values.
    let uniq l =
        uniqImpl l id

    //
    let rec private repcount n l cont =
        match l with
        | [] ->
            failwith "repcount"
        | [x] ->
            cont [x,n]
        |  x :: (y :: _ as ys) -> 
            if compare y x = 0 then
                repcount (n + 1) ys cont
            else
                repcount 1 ys <| fun lst ->
                    cont ((x, n) :: lst)

    // pg. ???
    // OCaml: val repetitions : 'a list -> ('a * int) list = <fun>
    // F#:    val repetitions : ('a list -> ('a * int) list) when 'a : comparison
    let repetitions l =
        match l with
        | [] -> []
        | l ->
            repcount 1 l id
        
    // pg. 619
    // OCaml: val tryfind : ('a -> 'b)   -> 'a list -> 'b = <fun>
    // F#:    val tryFind : ('a -> bool) -> 'a list -> 'a option
    // Use List.tryFind?
    // Note: Signature differences
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
    let mapfilter f l =
        l |> List.choose (fun el ->
            try Some <| f el
            with Failure _ -> None)

// ------------------------------------------------------------------------- //
// Find list member that maximizes or minimizes a function.                  //
// ------------------------------------------------------------------------- //

    // pg. 620
    // OCaml: val maximize : ('a -> 'b) -> 'a list -> 'a = <fun>
    // F#:    val maximize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
    let inline maximize f l =
        List.maxBy f l
    
    // pg. 620
    // OCaml: val minimize : ('a -> 'b) -> 'a list -> 'a = <fun>
    // F#:    val minimize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
    let inline minimize f l =
        List.minBy f l

// ------------------------------------------------------------------------- //
// Set operations on ordered lists.                                          //
// ------------------------------------------------------------------------- //

    // TODO: Should these be converted to F# Set
    // i.e. Set.union, Set.intersect, Set.difference

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
    // TODO: Use Set.union
    // F#:    val union : Set<'T> -> Set<'T> -> Set<'T> (requires comparison)
    let union =
        let rec union l1 l2 cont =
            match l1, l2 with
            | [], l2 ->
                cont l2
            | l1, [] ->
                cont l1
            | (h1 :: t1 as l1), (h2 :: t2 as l2) ->
                if h1 = h2 then
                    union t1 t2 <| fun lst ->
                        cont (h1 :: lst)
                elif h1 < h2 then
                    union t1 l2 <| fun lst ->
                        cont (h1 :: lst)
                else
                    union l1 t2 <| fun lst ->
                        cont (h2 :: lst)
        fun s1 s2 ->
            union (setify s1) (setify s2) id
        
    // pg. 620
    // OCaml: val intersect : 'a list -> 'a list -> 'a list = <fun>
    // F#:    val intersect : ('a list -> 'a list -> 'a list) when 'a : comparison
    // TODO: Use Set.intersect
    // F#:    val intersect : Set<'T> -> Set<'T> -> Set<'T> (requires comparison)
    let intersect =
        let rec intersect l1 l2 cont =
            match l1, l2 with
            | [], _
            | _, [] ->
                cont []
            | (h1 :: t1 as l1), (h2 :: t2 as l2) ->
                if h1 = h2 then
                    intersect t1 t2 <| fun lst ->
                        cont (h1 :: lst)
                elif h1 < h2 then
                    intersect t1 l2 cont
                else
                    intersect l1 t2 cont
        fun s1 s2 ->
            intersect (setify s1) (setify s2) id
        
    // pg. 620
    // OCaml: val subtract : 'a list -> 'a list -> 'a list = <fun>
    // F#:    val subtract : ('a list -> 'a list -> 'a list) when 'a : comparison
    // TODO: Use Set.Difference or (l1 - l2)
    // F#:    val difference : Set<'T> -> Set<'T> -> Set<'T> (requires comparison)
    let subtract =
        let rec subtract l1 l2 cont =
            match l1, l2 with
            | [], _ ->
                cont []
            | l1, [] ->
                cont l1
            | (h1 :: t1 as l1), (h2 :: t2 as l2) ->
                if h1 = h2 then
                    subtract t1 t2 cont
                elif h1 < h2 then
                    subtract t1 l2 <| fun lst ->
                        cont (h1 :: lst)
                else
                    subtract l1 t2 cont
        fun s1 s2 ->
            subtract (setify s1) (setify s2) id

    let rec private subsetImpl l1 l2 =
        match l1, l2 with
        | [], l2 -> true
        | l1, [] -> false
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then subsetImpl t1 t2
            elif h1 < h2 then false
            else subsetImpl l1 t2

    let rec private psubsetImpl l1 l2 =
        match l1, l2 with
        | l1, [] -> false
        | [], l2 -> true
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then psubsetImpl t1 t2
            elif h1 < h2 then false
            else subsetImpl l1 t2
        
    // pg. 620
    // OCaml: val subset : 'a list -> 'a list -> bool = <fun>
    // F#:    val subset : 'a list -> 'a list -> bool when 'a : comparison
    let subset s1 s2 =
        subsetImpl (setify s1) (setify s2)

    // OCaml: val psubset : 'a list -> 'a list -> bool = <fun>
    // F#:    val psubset : ('b list -> 'b list -> bool) when 'b : comparison
    let psubset s1 s2 =
        psubsetImpl (setify s1) (setify s2)

    // pg. 620
    // OCaml: val set_eq : 'a list -> 'a list -> bool = <fun>
    // F#:    val set_eq : 'a list -> 'a list -> bool when 'a : comparison
    // TODO: Can we use (s1 = s2) once they are converted to sets?
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

//    // TODO : Replace 'mem' with the equivalent code:
//    let inline mem x lis =
//        List.exists ((=) x) lis

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

    //
    let rec private allsetsImpl m l cont =
        if m = 0 then
            cont [[]]
        else
            match l with
            | [] ->
                cont []
            | h :: t ->
                allsetsImpl (m - 1) t <| fun result1 ->
                allsetsImpl m t <| fun result2 ->
                    cont (union (image (fun g -> h :: g) result1) result2)

    // pg. 620
    // OCaml: val allsets : int -> 'a list -> 'a list list = <fun>
    // F#:    val allsets : int -> 'a list -> 'a list list when 'a : comparison
    /// Produces all n-element subsets of l.
    let allsets n l =
        allsetsImpl n l id

    //
    let rec private allsubsetsImpl s cont =
        match s with
        | [] ->
            cont [[]]
        | a :: t ->
            allsubsetsImpl t <| fun res ->
                cont (union (image (fun b -> a :: b) res) res)

    (* TODO :   Perhaps switch to this more-efficient and succint
                implementation of the powerset function. It just
                needs to be modified to use CPS for efficiency. *)
    (*
    let rec allsubsets = function
        | [] -> [[]]
        | h::t ->
            [ for x in allsubsets t do
                for t in [x;h::x] -> t ]
    *)
        
    // pg. 620
    // OCaml: val allsubsets : 'a list -> 'a list list = <fun>
    // F#:    val allsubsets : 'a list -> 'a list list when 'a : comparison
    /// Produces all subsets of l.
    // NOTE : This is simply the powerset function.
    let allsubsets s =
        allsubsetsImpl s id
                    
    // pg. 620
    // OCaml: val allnonemptysubsets : 'a list -> 'a list list = <fun>
    // F#:    val allnonemptysubsets : 'a list -> 'a list list when 'a : comparison
    /// Produces all non-empty subsets of l.
    let allnonemptysubsets l =
        subtract (allsubsets l) [[]]

// pg. 619
// ------------------------------------------------------------------------- //
// Explosion and implosion of strings.                                       //
// ------------------------------------------------------------------------- //

    (* OPTIMIZE :   'explode' should return a 'char list' instead of a 'string list'
                    for efficiency. Ideally, we should optimize consuming code
                    to use a char[], at which point 'explode' could simply become
                    an alias for the String.ToCharArray(...) function. *)

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

(*  OPTIMIZE :  Can the 'func' type be replaced by the F# Map type? It seems
                to work in the same way, and it'd be simpler to use -- we could
                just redefine the functions below to work on Map instead. *)


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
        // TODO : Optimize using continuation-passing style.
        let rec map_list f l =
            match l with
            | [] -> []
            | (x, y) :: t ->
                (x, f y) :: (map_list f t)
        // TODO : Optimize using continuation-passing style.
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

        let rec foldl f a t cont =
            match t with
            | Empty ->
                cont a
            | Leaf (h, l) ->
                cont (foldl_list f a l)
            | Branch (p, b, l, r) ->
                foldl f a l <| fun leftResult ->
                    foldl f leftResult r cont

        fun f a t ->
            foldl f a t id
        
    // pg. ???
    // OCaml: val foldr :  ('a -> 'b -> 'c -> 'c) -> ('a, 'b) func -> 'c -> 'c = <fun>
    // F#:    val foldr : (('a -> 'b -> 'c -> 'c) -> func<'a,'b>   -> 'c -> 'c)
    let foldr =
        let rec foldr_list f l a cont =
            match l with
            | [] ->
                cont a
            | (x, y) :: t ->
                foldr_list f t a <| fun result ->
                    cont (f x y result)

        let rec foldr f t a cont =
            match t with
            | Empty ->
                cont a
            | Leaf (h, l) ->
                foldr_list f l a cont
            | Branch (p, b, l, r) ->
                foldr f r a <| fun rightResult ->
                    foldr f l rightResult cont

        fun f t a ->
            foldr f t a id

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

    //
    let rec private undefine_listImpl x l cont =
        match l with
        | [] ->
            cont []
        | (a, b as ab) :: t ->
            let c = compare x a
            if c = 0 then
                cont t
            elif c < 0 then
                cont l
            else
                undefine_listImpl x t <| fun t' ->
                    if t' = t then cont l
                    else cont (ab :: t')

    //
    let private undefine_list x l =
        undefine_listImpl x l id

    // pg. 621
    // OCaml: val undefine :  'a -> ('a, 'b) func -> ('a, 'b) func = <fun>
    // F#:    val undefine : ('a -> func<'a,'b>   -> func<'a,'b>) when 'a : comparison and 'b : equality
    let undefine x =
        let k = hash x
        let rec und t cont =
            match t with
            | Leaf (h, l) when h = k ->
                match undefine_list x l with
                | l' when l' = l ->
                    cont t
                | [] ->
                    cont Empty
                | l' ->
                    cont (Leaf (h, l'))

            | Branch (p, b, l, r) when k &&& (b - 1) = p ->
                if k &&& b = 0 then
                    und l <| function
                        | l' when l' = l ->
                            cont t
                        | Empty ->
                            cont r
                        | l' ->
                            cont (Branch (p, b, l', r))
                else
                    und r <| function
                        | r' when r' = r ->
                            cont t
                        | Empty ->
                            cont l
                        | r' ->
                            cont (Branch (p, b, l, r'))
            | _ ->
                cont t

        fun t ->
            und t id

// ------------------------------------------------------------------------- //
// Redefinition and combination.                                             //
// ------------------------------------------------------------------------- //

    let private newbranch p1 t1 p2 t2 =
        let zp = p1 ^^^ p2
        let b = zp &&& -zp
        let p = p1 &&& (b - 1)
        if p1 &&& b = 0 then
            Branch (p, b, t1, t2)
        else
            Branch (p, b, t2, t1)

    let rec private define_listImpl (x, y as xy) l cont =
        match l with
        | [] ->
            cont [xy]
        | (a, b as ab) :: t ->
            let c = compare x a
            if c = 0 then
                cont (xy :: t)
            elif c < 0 then
                cont (xy :: l)
            else
                define_listImpl xy t <| fun lst ->
                    cont (ab :: lst)

    and private combine_listImpl op z l1 l2 cont =
        match l1, l2 with
        | [], x
        | x, [] ->
            cont x
        | ((x1, y1 as xy1) :: t1, (x2, y2 as xy2) :: t2) ->
            let c = compare x1 x2
            if c < 0 then
                combine_listImpl op z t1 l2 <| fun lst ->
                    cont (xy1 :: lst)
            elif c > 0 then
                combine_listImpl op z l1 t2 <| fun lst ->
                    cont (xy2 :: lst)
            else
                let y = op y1 y2
                combine_listImpl op z t1 t2 <| fun l ->
                    cont (if z y then l else (x1, y) :: l)

    let private define_list xy l =
        define_listImpl xy l id

    let private combine_list op z l1 l2 =
        combine_listImpl op z l1 l2 id

    // Finite Partial Functions (FPF)
    // To update the FPF with a new mapping from x to y.
    // pg. 621
    // OCaml: val ( |-> ) :  'a -> 'b -> ('a, 'b) func -> ('a, 'b) func = <fun>
    // F#:    val ( |-> ) : ('a -> 'b -> func<'a,'b>   -> func<'a,'b>) when 'a : comparison
    let (|->) x y =
        let k = hash x
        let rec upd t cont =
            match t with
            | Empty ->
                cont (Leaf (k, [x, y]))
            | Leaf (h, l) ->
                if h = k then
                    cont (Leaf (h, define_list (x, y) l))
                else
                    cont (newbranch h t k (Leaf (k, [x, y])))
            | Branch (p, b, l, r) ->
                if k &&& (b - 1) <> p then
                    cont (newbranch p t k (Leaf (k, [x, y])))
                elif k &&& b = 0 then
                    upd l <| fun upd_l ->
                        cont (Branch (p, b, upd_l, r))
                else
                    upd r <| fun upd_r ->
                        cont (Branch (p, b, l, upd_r))

        fun t ->
            upd t id

    //
    let rec private combineImpl op z t1 t2 cont =
        match t1, t2 with
        | Empty, x
        | x, Empty ->
            cont x
        | Leaf (h1, l1), Leaf (h2, l2) ->
            if h1 = h2 then
                match combine_list op z l1 l2 with
                | [] ->
                    cont Empty
                | l ->
                    cont (Leaf (h1, l))
            else
                cont (newbranch h1 t1 h2 t2)

        | (Leaf (k, lis) as lf), (Branch (p, b, l, r) as br) ->
            if k &&& (b - 1) = p then
                if k &&& b = 0 then
                    combineImpl op z lf l <| function
                        | Empty ->
                            cont r
                        | l' ->
                            cont (Branch (p, b, l', r))
                else
                    combineImpl op z lf r <| function
                        | Empty ->
                            cont l
                        | r' ->
                            cont (Branch (p, b, l, r'))
            else
                cont (newbranch k lf p br)

        | (Branch (p, b, l, r) as br), (Leaf (k, lis) as lf) ->
            if k &&& (b - 1) = p then
                if k &&& b = 0 then
                    combineImpl op z l lf <| function
                        | Empty ->
                            cont r
                        | l' ->
                            cont (Branch (p, b, l', r))
                else
                    combineImpl op z r lf <| function
                        | Empty ->
                            cont l
                        | r' ->
                            cont (Branch (p, b, l, r'))
            else
                cont (newbranch p br k lf)

        | Branch (p1, b1, l1, r1), Branch (p2, b2, l2, r2) ->
            if b1 < b2 then
                if p2 &&& (b1 - 1) <> p1 then
                    cont (newbranch p1 t1 p2 t2)
                elif p2 &&& b1 = 0 then
                    combineImpl op z l1 t2 <| function
                        | Empty ->
                            cont r1
                        | l ->
                            cont (Branch (p1, b1, l, r1))
                else
                    combineImpl op z r1 t2 <| function
                        | Empty ->
                            cont l1
                        | r ->
                            cont (Branch (p1, b1, l1, r))

            elif b2 < b1 then
                if p1 &&& (b2 - 1) <> p2 then
                    cont (newbranch p1 t1 p2 t2)
                elif p1 &&& b2 = 0 then
                    combineImpl op z t1 l2 <| function
                        | Empty ->
                            cont r2
                        | l ->
                            cont (Branch (p2, b2, l, r2))
                else
                    combineImpl op z t1 r2 <| function
                        | Empty ->
                            cont l2
                        | r ->
                            cont (Branch (p2, b2, l2, r))

            elif p1 = p2 then
                combineImpl op z l1 l2 <| fun result1 ->
                combineImpl op z r1 r2 <| fun result2 ->
                    match result1, result2 with
                    | Empty, x
                    | x, Empty ->
                        cont x
                    | l, r ->
                        cont (Branch (p1, b1, l, r))
            else
                cont (newbranch p1 t1 p2 t2)

    // OCaml: val combine :  ('a -> 'a -> 'a) -> ('a -> bool) -> ('b, 'a) func -> ('b, 'a) func -> ('b, 'a) func = <fun>
    // F#:    val combine : (('c -> 'c -> 'c) -> ('c -> bool) -> func<'d,'c>   -> func<'d,'c>   -> func<'d,'c>) when 'c : equality and 'd : comparison
    let combine op z t1 t2 =
        combineImpl op z t1 t2 id

// ------------------------------------------------------------------------- //
// Special case of point function.                                           //
// ------------------------------------------------------------------------- //

    // Finite Partial Functions (FPF)
    // To create a new funtion in the FPF defined only for the value x and mapping it to y.
    // pg. 621
    // OCaml: val ( |=> ) : 'a -> 'b -> ('a, 'b) func = <fun>
    // F#:    val ( |=> ) : 'a -> 'b -> func<'a,'b> when 'a : comparison
    let inline (|=>) x y = 
        (x |-> y) undefined

// ------------------------------------------------------------------------- //
// Idiom for a mapping zipping domain and range lists.                       //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val fpf : 'a list -> 'b list -> ('a, 'b) func = <fun>
    // F#:    val fpf : 'a list -> 'b list -> func<'a,'b> when 'a : comparison
    let inline fpf xs ys =
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

// TODO: Convert to using fsi.AddPrinter()
// #install_printer print_fpf

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
    let undef _ =
        failwith "undefined function"

// ------------------------------------------------------------------------- //
// Union-find algorithm.                                                     //
// ------------------------------------------------------------------------- //

(*  TODO :  Replace with our much-more-efficient F# version of union-find,
            then modify the functions below to work with it. *)


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
