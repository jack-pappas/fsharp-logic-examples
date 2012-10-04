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
        // OPTIMIZE : Change to Set.union
    let union s1 s2 =
        Set.union (Set.ofList s1) (Set.ofList s2)
        |> Set.toList

    // pg. 620
    // OCaml: val intersect : 'a list -> 'a list -> 'a list = <fun>
    // F#:    val intersect : ('a list -> 'a list -> 'a list) when 'a : comparison
        // OPTIMIZE : Use Set.intersect
    let intersect s1 s2 =
        Set.intersect (Set.ofList s1) (Set.ofList s2)
        |> Set.toList

    // pg. 620
    // OCaml: val subtract : 'a list -> 'a list -> 'a list = <fun>
    // F#:    val subtract : ('a list -> 'a list -> 'a list) when 'a : comparison
        // OPTIMIZE : Change to Set.difference 
    let subtract s1 s2 =
        Set.difference (Set.ofList s1) (Set.ofList s2)
        |> Set.toList
        
    // pg. 620
    // OCaml: val subset : 'a list -> 'a list -> bool = <fun>
    // F#:    val subset : 'a list -> 'a list -> bool when 'a : comparison
        // OPTIMIZE : Change to Set.isSubset
    let rec private subsetImpl l1 l2 =
        match l1, l2 with
        | [], l2 -> true
        | l1, [] -> false
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then subsetImpl t1 t2
            elif h1 < h2 then false
            else subsetImpl l1 t2
    let subset s1 s2 =
        subsetImpl (setify s1) (setify s2)

    // OCaml: val psubset : 'a list -> 'a list -> bool = <fun>
    // F#:    val psubset : ('b list -> 'b list -> bool) when 'b : comparison
        // OPTIMIZE : Change to Set.isProperSubset
    let rec private psubsetImpl l1 l2 =
        match l1, l2 with
        | l1, [] -> false
        | [], l2 -> true
        | h1 :: t1, h2 :: t2 ->
            if h1 = h2 then psubsetImpl t1 t2
            elif h1 < h2 then false
            else subsetImpl l1 t2
    let psubset s1 s2 =
        psubsetImpl (setify s1) (setify s2)

    // pg. 620
    // OCaml: val set_eq : 'a list -> 'a list -> bool = <fun>
    // F#:    val set_eq : 'a list -> 'a list -> bool when 'a : comparison
        // OPTIMIZE : This can be inlined and implemented as (s1 = s2).
    let set_eq s1 s2 =
        (Set.ofList s1) = (Set.ofList s2)
    
    // pg. 620
    // OCaml: val insert : 'a -> 'a list -> 'a list = <fun>
    // F#:    val insert : 'a -> 'a list -> 'a list when 'a : comparison
        // OPTMIZE : Change to Set.add
    let insert x s =
        Set.ofList s
        |> Set.add x
        |> Set.toList
    
    // pg. 620
    // OCaml: val image : ('a -> 'b) -> 'a list -> 'b list = <fun>
    // F#:    val image : ('a -> 'b) -> 'a list -> 'b list when 'b : comparison
        // OPTIMIZE : Change to Set.map
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
        // OPTIMIZE : Change to Set.unionMany
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
    let inline undefine x (f : func<_,_>) =
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
    let inline (|->) x y (f : func<_,_>) =
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
