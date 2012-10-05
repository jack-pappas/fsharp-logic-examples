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
    open OptimizedClosures
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
    let funpow n f x =
        if n < 0 then
            failwith "A function cannot be executed a negative number of times."
        elif n = 0 then
            x
        else
            let mutable x = x
            for i = 1 to n do
                x <- f x
            x

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

    (* OPTIMIZE :   Implement a special version of allpairs which creates the
                    pairs as tuples; that is, it should work like this code which
                    is used in a number of places throughout the project:
                        allpairs (fun s1 s2 -> s1, s2) *)
    
    // pg. 620
    // OCaml: val allpairs : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list = <fun>
    // F#:    val allpairs : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
    // Produces the Cartesian product of two lists, then applies
    // a mapping function to each pair of elements in the product.
    let allpairs f l1 l2 =
        if List.isEmpty l1 then []
        elif List.isEmpty l2 then []
        else
            let f = FSharpFunc<_,_,_>.Adapt f
            let results =
                (List.length l1) * (List.length l2)
                |> Array.zeroCreate
            let mutable index = 0
            let mutable l1 = l1            
            while not <| List.isEmpty l1 do
                // Create a mutable *copy* of l2.
                let mutable l2 = l2

                while not <| List.isEmpty l2 do
                    results.[index] <-
                        let x = List.head l1
                        let y = List.head l2
                        f.Invoke (x, y)

                    // Update the loop counter
                    index <- index + 1

                    // Update the inner list
                    l2 <- List.tail l2

                // Update the outer list
                l1 <- List.tail l1

            // Convert the results into a list and return it.
            Array.toList results

    // pg. 620
    // OCaml: val distinctpairs : 'a list -> ('a * 'a) list = <fun>
    // F#:    val distinctpairs : 'a list -> ('a * 'a) list
    // Produces all distinct pairs of elements from a list.
    let distinctpairs l =
        let s = Set.ofList l
        (Set.empty, s)
        ||> Set.fold (fun pairs x ->
            (pairs, s)
            ||> Set.fold (fun pairs y ->
                // The pair is only added when
                // certain conditions are met.
                if x < y then
                    Set.add (x, y) pairs
                else
                    pairs))
        |> Set.toList
        
    // pg. 619
    // OCaml: val chop_list : int -> 'a list -> 'a list * 'a list = <fun>
    // F#:    val chop_list : int -> 'a list -> 'a list * 'a list
    // Takes the first n items from a list. Returns those items as a list,
    // along with any items remaining in the original list.
    let chop_list n l =
        if n > List.length l then
            failwith "chop_list"
        elif n = 0 then
            // Optimized case for n = 0.
            [], l
        else
            // Holds the chopped items.
            let choppedItems = Array.zeroCreate n

            let rec chopRec i lst =
                if i >= n then
                    (Array.toList choppedItems), lst
                else
                    choppedItems.[i] <- List.head lst
                    chopRec (i + 1) (List.tail lst)

            chopRec 0 l

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
        // OPTIMIZE : Re-implement 'butlast' using 'chop_list'.
        butlastImpl l id
    
    // pg. 619
    // OCaml: val insertat : int -> 'a -> 'a list -> 'a list = <fun>
    // F#:    val insertat : int -> 'a -> 'a list -> 'a list
    let insertat i x l =
        if i > List.length l then
            failwith "insertat: list too short for position to exist"
        elif i = 0 then
            // Optimized case for i = 0.
            x :: l
        else
            let rec insertRec (stack, lst) =
                if List.length stack = i then
                    (x :: lst, stack)
                    ||> List.fold (fun lst el ->
                        el :: lst)
                else
                    let stack = (List.head lst) :: stack
                    let lst = List.tail lst
                    insertRec (stack, lst)

            insertRec ([], l)
        
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
            compare h y <> 0
            && (compare h x = 0 || earlier t x y)

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
        // NOTE : 'comparer' returns bool, so it must implement either the
        // (<=) or (>=) operators.
    let merge comparer l1 l2 =
        mergeImpl comparer l1 l2 id

// ------------------------------------------------------------------------- //
// Bottom-up mergesort.                                                      //
// ------------------------------------------------------------------------- //

(* OPTIMIZE :   Replace with List.sortWith. *)

    // pg. 619
    // OCaml: val sort : ('a -> 'a -> bool) -> 'a list -> 'a list = <fun>
    // F#:    val sort : ('a -> 'a -> bool) -> ('a list -> 'a list) when 'a : equality
    let rec private mergepairs ord l1 l2 =
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
    // Like 'map', but removes elements of the list for which
    // the function fails (i.e., raises an exception).
    let mapfilter f l =
        l |> List.choose (fun el ->
            try Some <| f el
            with Failure _ -> None)

// ------------------------------------------------------------------------- //
// Set operations on ordered lists.                                          //
// ------------------------------------------------------------------------- //

(* OPTIMIZE :   Instead of using ordered lists to represent sets, use the
                built-in F# Set type -- it'll be easier to work with and is
                algorithmically faster.
                
                NOTE : The code below has already been modified to use functions
                from the Set module, but for compatibility with the existing code,
                we still input/output lists. *)

    // pg. 620
    // OCaml: val setify : 'a list -> 'a list = <fun>
    // F#:    val setify : ('a list -> 'a list) when 'a : comparison
    let setify lst =
        Set.ofList lst
        |> Set.toList

    // pg. 620
    // OCaml: val union : 'a list -> 'a list -> 'a list = <fun>
    // F#:    val union : ('a list -> 'a list -> 'a list) when 'a : comparison
    let union s1 s2 =
        Set.union (Set.ofList s1) (Set.ofList s2)
        |> Set.toList

    // pg. 620
    // OCaml: val intersect : 'a list -> 'a list -> 'a list = <fun>
    // F#:    val intersect : ('a list -> 'a list -> 'a list) when 'a : comparison
    let intersect s1 s2 =
        Set.intersect (Set.ofList s1) (Set.ofList s2)
        |> Set.toList

    // pg. 620
    // OCaml: val subtract : 'a list -> 'a list -> 'a list = <fun>
    // F#:    val subtract : ('a list -> 'a list -> 'a list) when 'a : comparison
    let subtract s1 s2 =
        Set.difference (Set.ofList s1) (Set.ofList s2)
        |> Set.toList
        
    // pg. 620
    // OCaml: val subset : 'a list -> 'a list -> bool = <fun>
    // F#:    val subset : 'a list -> 'a list -> bool when 'a : comparison
    // Determines if s1 is a subset of s2.
    let subset s1 s2 =
        Set.isSubset (Set.ofList s1) (Set.ofList s2)

    // OCaml: val psubset : 'a list -> 'a list -> bool = <fun>
    // F#:    val psubset : ('b list -> 'b list -> bool) when 'b : comparison
    // Determines if s1 is a proper subset of s2.
    let psubset s1 s2 =
        Set.isProperSubset (Set.ofList s1) (Set.ofList s2)

    // pg. 620
    // OCaml: val set_eq : 'a list -> 'a list -> bool = <fun>
    // F#:    val set_eq : 'a list -> 'a list -> bool when 'a : comparison
    let set_eq s1 s2 =
        (Set.ofList s1) = (Set.ofList s2)
    
    // pg. 620
    // OCaml: val insert : 'a -> 'a list -> 'a list = <fun>
    // F#:    val insert : 'a -> 'a list -> 'a list when 'a : comparison
    let insert x s =
        Set.ofList s
        |> Set.add x
        |> Set.toList
    
    // pg. 620
    // OCaml: val image : ('a -> 'b) -> 'a list -> 'b list = <fun>
    // F#:    val image : ('a -> 'b) -> 'a list -> 'b list when 'b : comparison
    let image f s =
        Set.ofList s
        |> Set.map f
        |> Set.toList

// ------------------------------------------------------------------------- //
// Union of a family of sets.                                                //
// ------------------------------------------------------------------------- //

    // pg. 620
    // OCaml: val unions : 'a list list -> 'a list = <fun>
    // F#:    val unions : 'a list list -> 'a list when 'a : comparison
    let unions s =
        (Set.empty, s)
        ||> List.fold (fun combined s ->
            Set.ofList s
            |> Set.union combined)
        |> Set.toList

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

    // TODO : Once we change over to use F# Set<_> instead of list to represent
    // sets, this function can be used directly (simply rename it to 'allsets').
    let private allsetsImpl n (s : Set<_>) : Set<Set<_>> =
        if n < 0 then
            failwith "Subset size cannot be negative."
        elif n = 0 then
            // Optimized case for n = 0.
            Set.singleton Set.empty
        elif n = 1 then
            // Optimized case for n = 1.
            Set.map Set.singleton s
        else
            let sizeOfSet = Set.count s
            if n = sizeOfSet then
                // Optimized case for getting the entire set.
                Set.singleton s
            elif n > sizeOfSet then
                failwith "Subset size cannot be greater than the size of the set."
            else
                // OPTIMIZE : Implement a fast binomial function or approximation
                // and use it to determine how many subsets of a given size there
                // are based on the number of elements in the original set.
                // Then, we can just use a normal array since we'll know the exact size.
                let mutable allSetsOfPrevSize = ResizeArray<_> (sizeOfSet)

                // Populate the ResizeArray with single-item sets to start with.
                s |> Set.iter (Set.singleton >> allSetsOfPrevSize.Add)

                for i = 2 to n do
                    allSetsOfPrevSize <-
                        let allSetsOfCurrentSize = ResizeArray<_> (sizeOfSet)

                        allSetsOfPrevSize
                        |> ResizeArray.iter (fun currentSet ->
                            s |> Set.iter (fun el ->
                                let currentSet = Set.add el currentSet
                                if Set.count currentSet = i then
                                    allSetsOfCurrentSize.Add currentSet))

                        allSetsOfCurrentSize

                // DEBUG : Make sure all of the sets have the
                // correct number of elements. 
                assert (allSetsOfPrevSize.Count > 0)
                assert (
                    allSetsOfPrevSize
                    |> ResizeArray.forall (fun x -> Set.count x = n))

                // Convert the ResizeArray to a Set<_> and return it.
                (Set.empty, allSetsOfPrevSize)
                ||> ResizeArray.fold (fun setOfSets el ->
                    Set.add el setOfSets)


    // pg. 620
    // OCaml: val allsets : int -> 'a list -> 'a list list = <fun>
    // F#:    val allsets : int -> 'a list -> 'a list list when 'a : comparison
    /// Produces all n-element subsets of l.
    // NOTE : 'allsets' creates combinations (not permutations!)
    let allsets n l =
        let subsets = allsetsImpl n (Set.ofList l)
        ([], subsets)
        ||> Set.fold (fun setList s ->
            (Set.toList s) :: setList)
        |> List.rev
        
    // pg. 620
    // OCaml: val allsubsets : 'a list -> 'a list list = <fun>
    // F#:    val allsubsets : 'a list -> 'a list list when 'a : comparison
    /// Produces all subsets of l.
    // NOTE : This is simply the powerset function.
    // NOTE : The produced subsets are combinations, not permutations.
    let allsubsets l =
        let subsetsBySize =
            let s = Set.ofList l
            Array.init (Set.count s + 1) <| fun n ->
                allsetsImpl n s

        ([], subsetsBySize)
        ||> Array.fold (
            Set.fold (fun subsetList subset ->
                (Set.toList subset) :: subsetList))
        |> List.sort
                    
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
// Polymorphic finite partial functions via F# Map type.                     //
// ------------------------------------------------------------------------- //

    // pg. 621
    type func<'a, 'b when 'a : comparison> = Map<'a, 'b>

// ------------------------------------------------------------------------- //
// Undefined function.                                                       //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val undefined : ('a, 'b) func = Empty
    // F#:    val undefined : func<'a,'b>
    let undefined : func<_,_> = Map.empty

// ------------------------------------------------------------------------- //
// In case of equality comparison worries, better use this.                  //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val is_undefined : ('a, 'b) func -> bool = <fun>
    // F#:    val is_undefined : func<'a,'b>   -> bool
    let inline is_undefined (f : func<_,_>) = Map.isEmpty f

// ------------------------------------------------------------------------- //
// Operation analogous to "map" for lists.                                   //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val mapf : ('a -> 'b)  -> ('c, 'a) func -> ('c, 'b) func = <fun>
    // F#:    val mapf : (('a -> 'b) -> func<'c,'a>   -> func<'c,'b>)
    let inline mapf mapping (f : func<_,_>) : func<_,_> =
        Map.map (fun _ v -> mapping v) f

// ------------------------------------------------------------------------- //
// Operations analogous to "fold" for lists.                                 //
// ------------------------------------------------------------------------- //

    // pg. ???
    // OCaml: val foldl : ('a -> 'b -> 'c -> 'a) -> 'a -> ('b, 'c) func -> 'a = <fun>
    // F#:    val foldl : (('a -> 'b -> 'c -> 'a) -> 'a -> func<'b,'c> -> 'a)
    let inline foldl folder state (f : func<_,_>) =
        Map.fold folder state f
        
    // pg. ???
    // OCaml: val foldr :  ('a -> 'b -> 'c -> 'c) -> ('a, 'b) func -> 'c -> 'c = <fun>
    // F#:    val foldr : (('a -> 'b -> 'c -> 'c) -> func<'a,'b>   -> 'c -> 'c)
    let inline foldr folder (f : func<_,_>) state =
        Map.foldBack folder f state

// ------------------------------------------------------------------------- //
// Mapping to sorted-list representation of the graph, domain and range.     //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val graph : ('a, 'b) func -> ('a * 'b) list = <fun>
    // F#:    val graph : func<'a,'b>   -> ('a * 'b) list when 'a : comparison and 'b : comparison
    let graph (f : func<_,_>) =
        // TODO : Replace with call to Map.toList
        // IMPORTANT : Make sure the values are returned in the same order
        // that they would be by 'setify'.
        foldl (fun a x y -> (x, y) :: a) [] f
        |> setify
    
    // pg. 621
    // OCaml: val dom : ('a, 'b) func -> 'a list = <fun>
    // F#:    val dom : func<'a,'b>   -> 'a list when 'a : comparison
    let dom (f : func<_,_>) =
        // TODO : Replace with Map.fold to create list of keys.
        // IMPORTANT : Make sure the values are returned in the same order
        // that they would be by 'setify'.
        foldl (fun a x y -> x :: a) [] f
        |> setify
    
    // pg. 621
    // OCaml: val ran : ('a, 'b) func -> 'b list = <fun>
    // F#:    val ran : func<'a,'b>   -> 'b list when 'b : comparison
    let ran (f : func<_,_>) =
        // TODO : Replace with Map.fold to create list of values.
        // IMPORTANT : Make sure the values are returned in the same order
        // that they would be by 'setify'.
        foldl (fun a x y -> y :: a) [] f
        |> setify

// ------------------------------------------------------------------------- //
// Application.                                                              //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val applyd :  ('a, 'b) func -> ('a -> 'b) -> 'a -> 'b = <fun>
    // F#:    val applyd : (func<'a,'b>   -> ('a -> 'b) -> 'a -> 'b) when 'a : comparison
    // Apply with default value.
    let applyd (f : func<_,_>) defaultValueGenerator value : 'b =
        match Map.tryFind value f with
        | Some x -> x
        | None ->
            // Return a default value.
            // NOTE : This value is _not_ added to the func/map.
            defaultValueGenerator value

    // pg. 621
    // OCaml: val apply : ('a, 'b) func -> 'a -> 'b = <fun>
    // F#:    val apply : func<'a,'b>   -> ('a -> 'b) when 'a : comparison
    let apply (f : func<_,_>) a =
        match Map.tryFind a f with
        | Some x -> x
        | None ->
            failwith "apply"

    // EGT
    let inline apply_none (f : func<_,_>) a =
        applyd f (fun _ -> None) a

    // pg. 621
    // OCaml: val tryapplyd : ('a, 'b) func -> 'a -> 'b -> 'b = <fun>
    // F#:    val tryapplyd : func<'a,'b>   -> 'a -> 'b -> 'b when 'a : comparison
    let tryapplyd (f : func<_,_>) a d =
        match Map.tryFind a f with
        | Some x -> x
        | None -> d

    // pg. 621
    // OCaml: val tryapplyl : ('a, 'b list) func -> 'a -> 'b list = <fun>
    // F#:    val tryapplyl : func<'a,'b list>   -> 'a -> 'b list when 'a : comparison
    let inline tryapplyl (f : func<_,_>) x =
        tryapplyd f x []
    
    // pg. 621
    // OCaml: val defined : ('a, 'b) func -> 'a -> bool = <fun>
    // F#:    val defined : func<'a,'b>   -> 'a -> bool when 'a : comparison
    let inline defined (f : func<_,_>) a =
        Map.containsKey a f

// ------------------------------------------------------------------------- //
// Undefinition.                                                             //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val undefine :  'a -> ('a, 'b) func -> ('a, 'b) func = <fun>
    // F#:    val undefine : ('a -> func<'a,'b>   -> func<'a,'b>) when 'a : comparison and 'b : equality
    let inline undefine x (f : func<_,_>) : func<_,_> =
        Map.remove x f

// ------------------------------------------------------------------------- //
// Redefinition and combination.                                             //
// ------------------------------------------------------------------------- //
(* NOTE :   The 'combine' function wasn't actually used anywhere, so it hasn't
            been re-implemented for the F# map type. If necessary, it should
            be fairly simple to re-implement. *)


    // Finite Partial Functions (FPF)
    // To update the FPF with a new mapping from x to y.
    // pg. 621
    // OCaml: val ( |-> ) :  'a -> 'b -> ('a, 'b) func -> ('a, 'b) func = <fun>
    // F#:    val ( |-> ) : ('a -> 'b -> func<'a,'b>   -> func<'a,'b>) when 'a : comparison
    let inline (|->) x y (f : func<_,_>) : func<_,_> =
        Map.add x y f

// ------------------------------------------------------------------------- //
// Special case of point function.                                           //
// ------------------------------------------------------------------------- //

    // Finite Partial Functions (FPF)
    // To create a new funtion in the FPF defined only for the value x and mapping it to y.
    // pg. 621
    // OCaml: val ( |=> ) : 'a -> 'b -> ('a, 'b) func = <fun>
    // F#:    val ( |=> ) : 'a -> 'b -> func<'a,'b> when 'a : comparison
    let inline (|=>) x y : func<_,_> =
        Map.add x y undefined

// ------------------------------------------------------------------------- //
// Idiom for a mapping zipping domain and range lists.                       //
// ------------------------------------------------------------------------- //

    // pg. 621
    // OCaml: val fpf : 'a list -> 'b list -> ('a, 'b) func = <fun>
    // F#:    val fpf : 'a list -> 'b list -> func<'a,'b> when 'a : comparison
    let inline fpf xs ys : func<_,_> =
        // OPTIMIZE : Use standard List.fold2
        List.foldBack2 (|->) xs ys undefined

// ------------------------------------------------------------------------- //
// Grab an arbitrary element.                                                //
// ------------------------------------------------------------------------- //

    // pg. ???
    // OCaml: val choose : ('a, 'b) func -> 'a * 'b = <fun>
    // F#:    val choose : func<'a,'b>   -> 'a * 'b
    let choose (t : func<_,_>) =
        Map.toSeq t
        |> Seq.head

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
    type partition<'a when 'a : comparison> = Partition of func<'a, pnode<'a>>
    
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
    let inline equated (Partition f) = dom f

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
