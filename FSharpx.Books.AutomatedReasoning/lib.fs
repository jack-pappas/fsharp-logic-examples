// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

/// Misc library functions to set up a nice environment.
[<AutoOpen>]
module FSharpx.Books.AutomatedReasoning.lib

open LanguagePrimitives
open OptimizedClosures
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

// pg. ???
let inline check p x =
    assert (p x)
    x

// ------------------------------------------------------------------------- //
// Repetition of a function.                                                 //
// ------------------------------------------------------------------------- //

// pg. 612
let funpow n f x =
    if n < 0 then
        invalidArg "n" "A function cannot be executed a negative number of times."
    elif n = 0 then
        x
    else
        let mutable x = x
        for i = 1 to n do
            x <- f x
        x

// pg. 618
let can f x = 
    try 
        f x |> ignore
        true
    with _ -> false

// pg. 618
let rec repeat f x = 
    try repeat f (f x)
    with _ -> x

// ------------------------------------------------------------------------- //
// Handy list operations.                                                    //
// ------------------------------------------------------------------------- //

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
        invalidArg "l" "Cannot get the last element of an empty list."
    | [x] -> x
    | _ :: tl ->
        last tl
        
// pg. 619
// NOTE: find has been replaced with the equivalent built-in F# function List.find.
        
// pg. 619
// NOTE: el has been replaced with the equivalent built-in F# function List.nth.

// pg. 619
// NOTE: map has been replaced with the equivalent built-in F# function List.map.
        
// pg. 620
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
/// Given a list, creates a new list containing all unique 2-combinations
/// of the list elements. (I.e., (x, y) and (y, x) are the same and
/// will only be included once.)
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
// Takes the first n items from a list. Returns those items as a list,
// along with any items remaining in the original list.
let chop_list n l =
    let len = List.length l
    if n > len then
        invalidArg "n" "Cannot chop the list at an index greater \
                        than the number of items in the list."
    elif n = 0 then
        // Optimized case for n = 0.
        [], l
    elif n = len then
        // Optimized case for when the entire
        // list is chopped.
        l, []
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

// pg. 619
// NOTE: replicate has been replaced with the equivalent built-in F# function List.replicate.

// pg. 619
let butlast l =
    chop_list (List.length l - 1) l
    |> fst
    
// pg. 619
let insertat i x l =
    if i > List.length l then
        invalidArg "i" "Cannot insert an item at an index greater \
                        than the number of items in the list."
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
// NOTE: forall2 has been replaced with the equivalent built-in F# function List.forall2.

// pg. 619
let inline index x =
    List.findIndex ((=) x)

// ------------------------------------------------------------------------- //
// Whether the first of two items comes earlier in the list.                 //
// ------------------------------------------------------------------------- //

// pg. 619
let rec earlier l x y =
    match l with
    | [] ->
        false
    | h :: t ->
        h <> y
        && (h = x || earlier t x y)

// ------------------------------------------------------------------------- //
// Application of (presumably imperative) function over a list.              //
// ------------------------------------------------------------------------- //

// pg. 619
// NOTE: do_list has been replaced with the built-in F# function List.iter.

// Association lists.                                                        //
// ------------------------------------------------------------------------- //

// pg. 620
let rec assoc a l =
    match l with
    | [] ->
        failwith "assoc"
    | (x, y) :: t ->
        if x = a then y
        else assoc a t

// pg. ???
let rec rev_assoc a l =
    match l with
    | [] ->
        failwith "rev_assoc"
    | (x, y) :: t ->
        if y = a then x
        else rev_assoc a t

// ------------------------------------------------------------------------- //
// List sorting.                                                             //
// ------------------------------------------------------------------------- //

// pg. 619
let sort ord l =
    l |> List.sortWith (fun x y ->
        if ord x y then -1 else 1)

// ------------------------------------------------------------------------- //
// Common measure predicates to use with "sort".                             //
// ------------------------------------------------------------------------- //

// pg. 619
let increasing f x y =
//    compare (f x) (f y) < 0
    (f x) < (f y)
    
// pg. 619
let decreasing f x y =
//    compare (f x) (f y) > 0
    (f x) > (f y)
    

// ------------------------------------------------------------------------- //
// Eliminate repetitions of adjacent elements, with and without counting.    //
// ------------------------------------------------------------------------- //
        
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
let setify lst =
    Set.ofList lst
    |> Set.toList

// pg. 620
let union s1 s2 =
    Set.union (Set.ofList s1) (Set.ofList s2)
    |> Set.toList

// pg. 620
let intersect s1 s2 =
    Set.intersect (Set.ofList s1) (Set.ofList s2)
    |> Set.toList

// pg. 620
let subtract s1 s2 =
    Set.difference (Set.ofList s1) (Set.ofList s2)
    |> Set.toList
        
// pg. 620
let subset s1 s2 =
    Set.isSubset (Set.ofList s1) (Set.ofList s2)

// pg. 620
let psubset s1 s2 =
    Set.isProperSubset (Set.ofList s1) (Set.ofList s2)

// pg. 620
let set_eq s1 s2 =
    (Set.ofList s1) = (Set.ofList s2)
    
// pg. 620
let insert x s =
    Set.ofList s
    |> Set.add x
    |> Set.toList
    
// pg. 620
let image f s =
    Set.ofList s
    |> Set.map f
    |> Set.toList

// ------------------------------------------------------------------------- //
// Union of a family of sets.                                                //
// ------------------------------------------------------------------------- //

// pg. 620
let unions s =
    (Set.empty, s)
    ||> List.fold (
        List.fold (fun combined el ->
            Set.add el combined))
    |> Set.toList

// ------------------------------------------------------------------------- //
// List membership. This does *not* assume the list is a set.                //
// ------------------------------------------------------------------------- //

// pg. 620
let inline mem x lis =
    List.exists ((=) x) lis

// ------------------------------------------------------------------------- //
// Finding all subsets or all subsets of a given size.                       //
// ------------------------------------------------------------------------- //

//
[<RequireQualifiedAccess>]
module private ResizeArray =
    (* From the F# PowerPack *)

    let length (arr: ResizeArray<'T>) =  arr.Count
    let get (arr: ResizeArray<'T>) (n: int) =  arr.[n]

    let iter f (arr: ResizeArray<_>) = 
        for i = 0 to arr.Count - 1 do
            f arr.[i]

    let forall f (arr: ResizeArray<_>) =
        let len = length arr
        let rec loop i = i >= len || (f arr.[i] && loop (i+1))
        loop 0

    let fold (f : 'State -> 'T -> 'State) (acc: 'State) (arr: ResizeArray<'T>) =
        let mutable res = acc 
        let len = length arr 
        for i = 0 to len - 1 do 
            res <- f res (get arr i)
        res

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
/// Produces all n-element subsets of l.
// NOTE : 'allsets' creates combinations (not permutations!)
let allsets n l =
    let subsets = allsetsImpl n (Set.ofList l)
    ([], subsets)
    ||> Set.fold (fun setList s ->
        (Set.toList s) :: setList)
    |> List.rev
        
// pg. 620
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
// Polymorphic finite partial functions via F# Map type.                     //
// ------------------------------------------------------------------------- //

// pg. 621
type func<'a, 'b when 'a : comparison> = Map<'a, 'b>

// ------------------------------------------------------------------------- //
// Undefined function.                                                       //
// ------------------------------------------------------------------------- //

// pg. 621
let undefined : func<_,_> = Map.empty

// ------------------------------------------------------------------------- //
// In case of equality comparison worries, better use this.                  //
// ------------------------------------------------------------------------- //

// pg. 621
let inline is_undefined (f : func<_,_>) = Map.isEmpty f

// ------------------------------------------------------------------------- //
// Operation analogous to "map" for lists.                                   //
// ------------------------------------------------------------------------- //

// pg. 621
let inline mapf mapping (f : func<_,_>) : func<_,_> =
    Map.map (fun _ v -> mapping v) f

// ------------------------------------------------------------------------- //
// Operations analogous to "fold" for lists.                                 //
// ------------------------------------------------------------------------- //

// pg. ???
let inline foldl folder state (f : func<_,_>) =
    Map.fold folder state f
        
// pg. ???
let inline foldr folder (f : func<_,_>) state =
    Map.foldBack folder f state

// ------------------------------------------------------------------------- //
// Mapping to sorted-list representation of the graph, domain and range.     //
// ------------------------------------------------------------------------- //

// pg. 621
let inline graph (f : func<_,_>) =
    Map.toList f
    
// pg. 621
let dom (f : func<_,_>) =
    (Set.empty, f)
    ||> Map.fold (fun dom x _ ->
        Set.add x dom)
    // TEMP : Convert the set to a list for compatibility with existing code.
    |> Set.toList
    
// pg. 621
let ran (f : func<_,_>) =
    (Set.empty, f)
    ||> Map.fold (fun range _ y ->
        Set.add y range)
    // TEMP : Convert the set to a list for compatibility with existing code.
    |> Set.toList

// ------------------------------------------------------------------------- //
// Application.                                                              //
// ------------------------------------------------------------------------- //

// pg. 621
// Apply with default value.
let applyd (f : func<_,_>) defaultValueGenerator value : 'b =
    match Map.tryFind value f with
    | Some x -> x
    | None ->
        // Return a default value.
        // NOTE : This value is _not_ added to the func/map.
        defaultValueGenerator value

// pg. 621
let apply (f : func<_,_>) a =
    match Map.tryFind a f with
    | Some x -> x
    | None ->
        failwith "apply"

// EGT
let inline apply_none (f : func<_,_>) a =
    applyd f (fun _ -> None) a

// pg. 621
let tryapplyd (f : func<_,_>) a d =
    match Map.tryFind a f with
    | Some x -> x
    | None -> d

// pg. 621
let inline tryapplyl (f : func<_,_>) x =
    tryapplyd f x []
    
// pg. 621
let inline defined (f : func<_,_>) a =
    Map.containsKey a f

// ------------------------------------------------------------------------- //
// Undefinition.                                                             //
// ------------------------------------------------------------------------- //

// pg. 621
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
let inline (|=>) x y : func<_,_> =
    Map.add x y undefined

// ------------------------------------------------------------------------- //
// Idiom for a mapping zipping domain and range lists.                       //
// ------------------------------------------------------------------------- //

// pg. 621
let inline fpf xs ys : func<_,_> =
    // OPTIMIZE : Use standard List.fold2
    List.foldBack2 (|->) xs ys undefined

// ------------------------------------------------------------------------- //
// Grab an arbitrary element.                                                //
// ------------------------------------------------------------------------- //

// pg. ???
let choose (t : func<_,_>) =
    Map.toSeq t
    |> Seq.head

// ------------------------------------------------------------------------- //
// Install a (trivial) printer for finite partial functions.                 //
// ------------------------------------------------------------------------- //

// pg. ???
let print_fpf (f : func<'a,'b>) = printf "<func>"

// ------------------------------------------------------------------------- //
// Related stuff for standard functions.                                     //
// ------------------------------------------------------------------------- //

// pg. 618
let valmod a y f x =
    if x = a then y
    else f x
    
// pg. 618
let undef _ =
    failwith "undefined function"

// ------------------------------------------------------------------------- //
// Union-find algorithm.                                                     //
// ------------------------------------------------------------------------- //

(*  TODO :  Replace with our much-more-efficient F# version of union-find,
            then modify the functions below to work with it. *)


type pnode<'a> =
    | Nonterminal of 'a 
    | Terminal of 'a * int
    
// pg. 619
type partition<'a when 'a : comparison> = Partition of func<'a, pnode<'a>>
    
// pg. ???
let rec terminus (Partition f as ptn) a =
    match apply f a with
    | Terminal (p, q) ->
        p, q
    | Nonterminal b ->
        terminus ptn b
        
// pg. ???
let tryterminus ptn a =
    try terminus ptn a
    with _ -> (a, 1)
        
// pg. ???
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
let inline equated (Partition f) = dom f

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
