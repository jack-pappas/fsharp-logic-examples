module TestSets001

    // Do not delete this code until the useful information is moved else where. e.g. print_fpf

    // See: http://foxthompson.dynalias.org/doc/libghc-logic-classes-doc/html/src/Data-Logic-Harrison-Lib.html for conversion to Haskell

    // Finite Partial Functions
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
    // Although association lists are simple and convenient, they can be inefficient with the list becomes long. In most cases we use a somewhat moreelaborate type of finite partial functions (FPFs);
    // the OCamltype of finite partial functions from a to b is just (a,b)func. For F# it is func<'a,'b>
    type func<'a,'b> =
        | Empty
        | Leaf of int * ('a * 'b) list
        | Branch of int * int * func<'a,'b> * func<'a,'b>

// ------------------------------------------------------------------------- //
// Application of (presumably imperative) function over a list.              //
// ------------------------------------------------------------------------- //

    // pg. 619
    let rec do_list f l =
        match l with
        | []   -> ()
        | h::t -> f(h); do_list f t

    // Finite Partial Functions
    // pg. 621
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Complete
    //    Description
    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
    //       may sometimes be preferable to ordinary functions since they permit more operations
    //       such as equality comparison, extraction of domain etc.
    //       The value undefined is the 'empty' finite partial function that is nowhere defined.
    //    Failure
    //       Not applicable.
    //    Uses
    //       Starting a function to be augmented pointwise.
    //    See also
    //       |->, |=>, apply, choose, combine, defined, dom, foldl, foldr, graph,
    //       is_undefined, mapf, ran, tryapplyd, undefine.
    //
    // val undefined : func<'a,'b>
    let undefined = Empty
    
    // Finite Partial Functions
    // pg. 621
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Applies a finite partial function, with a backup function for undefined points.
    //    Description
    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
    //       may sometimes be preferable to ordinary functions since they permit more operations
    //       such as equality comparison, extraction of domain etc.
    //       If f is a finite partial function, g
    //       a convetional function and x an argument, tryapply f g x tries to apply f to x as with
    //       apply f x, but instead returns g x is f is undefined on x
    //    Failure
    //       Can only fail if the backup function fails.
    //    See also
    //       |->, |=>, apply, choose, combine, defined, dom, foldl, foldr, graph,
    //       is_undefined, mapf, ran, tryapplyd, undefine, undefined.
    //
    // EGT Notes:
    //    This function understands func<'a,'b>
    //    It applies a function (which parameter) to a (???).
    //    If the application fails, then a defalt value passeed in as (which parameter) is returned.
    //
    // val applyd : (func<'a,'b> -> ('a -> 'b) -> 'a -> 'b) when 'a : comparison
    let applyd =
        // val apply_listd :  ('a * 'b) list -> ('a -> 'b) -> 'a -> 'b when 'a : comparison
        let rec apply_listd l d x =
            match l with
            | (a,b)::t -> 
                let c = compare x a
                if c = 0   then b 
                elif c > 0 then apply_listd t d x 
                else            d x
            | []             -> d x
        // val it : func<'a,'b> -> ('a -> 'b) -> 'a -> 'b when 'a : comparison = <fun:clo@44>
        fun f d x ->
            let k = hash x
            let rec look t =
                match t with
                | Leaf(h,l)       when h = k                     -> apply_listd l d x
                | Branch(p,b,l,r) when (k ^^^ p) &&& (b - 1) = 0 -> look (if k &&& b = 0 then l else r)
                | _                                              -> d x
            look f

    // val applyd_new : Map<'a,'b> -> 'a -> 'b -> Map<'a,'b> when 'a : comparison
    let applyd_new m k a = Map.add k a m

    // pg. 621
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Applies a finite partial functin, failing on undefined points.
    //    Description
    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
    //       may sometimes be preferable to ordinary functions since they permit more operations
    //       such as equality comparison, extraction of domain etc.
    //       If f is a finite partial function and
    //       x an argument, apply f x tries to apply f to x and fails if it is undefined.
    //    See also
    //       |->, |=>, apply, choose, combine, defined, dom, foldl, foldr, graph,
    //       is_undefined, mapf, ran, tryapplyd, undefine, undefined.
    //
    // val apply : func<'a,'b> -> ('a -> 'b) when 'a : comparison
    let apply f = applyd f (fun x -> failwith "apply")
//    let apply f = 
//        let fa = 
//            fun x -> failwith "apply"
//        applyd f fa

    // val apply_new : Map<'a,'b> -> 'a -> 'b when 'a : comparison
    let apply_new m k = Map.find k m

    // pg. 621
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Applies a finite partial functin, with a default for undefined points.
    //    Description
    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
    //       may sometimes be preferable to ordinary functions since they permit more operations
    //       such as equality comparison, extraction of domain etc.
    //       If f is a finite partial function,
    //       x an element of its domain type and y of its range type, the call tryapplyd f x y tries to
    //       apply f to the value x, as with apply f x, but if it is undefined, simply returns y
    //    Failure
    //       Never fails
    //    See also
    //       |->, |=>, apply, applyd, choose, combine, defined, dom, foldl, foldr, graph,
    //       is_undefined, mapf, ran, undefine, undefined.
    //
    // val tryapplyd : func<'a,'b> -> 'a -> 'b -> 'b when 'a : comparison
    let tryapplyd f a d = applyd f (fun x -> d) a

    // val tryapplyd_new : Map<'a,'b> -> 'a -> 'b -> 'b when 'a : comparison
    let tryapplyd_new m k d = 
        try 
            apply_new m k
        with 
        | Failure _ -> d

    // pg. 621
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Test if a finite partial function is defined on a certain domain value.
    //    Description
    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
    //       may sometimes be preferable to ordinary functions since they permit more operations
    //       such as equality comparison, extraction of domain etc.
    //       The call defined f x returns true
    //       if the finite partial function f is defined on domain value x, and false otherwise.
    //    Failure
    //       Never fails
    //    See also
    //       |->, |=>, apply, applyd, choose, combine, dom, foldl, foldr, graph,
    //       is_undefined, mapf, ran, tryapplyd, undefine, undefined.
    //
    // val defined : func<'a,'b> -> 'a -> bool when 'a : comparison
    let defined f x =
        try 
            apply f x |> ignore
            true 
        with 
        | Failure _ -> false

    
    let flip a b c = b a c

    // val defined_new : Map<'a,'b> -> 'a -> bool when 'a : comparison
    let defined_new f x =
//        try 
//            apply_new f x |> ignore
//            true 
//        with 
//        | Failure _ -> false
        Map.containsKey 

// ------------------------------------------------------------------------- //
// Undefinition.                                                             //
// ------------------------------------------------------------------------- //

//    // pg. 621
//    //
//    // HOL Light Reference :
//    //    Synopis : 
//    //       Remove definition of a finte partial function on specific domain value.
//    //    Description
//    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
//    //       may sometimes be preferable to ordinary functions since they permit more operations
//    //       such as equality comparison, extraction of domain etc.
//    //       The call undefine x f removes
//    //       a definition ofor the domain value x in the finite partial function  f; if there was none to
//    //       begin with the function is unchanged.
//    //    Failure
//    //       Never fails
//    //    See also
//    //       |->, |=>, apply, applyd, choose, combine, defined, dom, foldl, foldr, graph,
//    //       is_undefined, mapf, ran, tryapplyd, undefine, undefined.
//    //
//    // val undefine : ('a -> func<'a,'b> -> func<'a,'b>) when 'a : comparison and 'b : equality
//    let undefine =
//        let rec undefine_list x l =
//            match l with
//            | (a,b as ab)::t ->
//                  let c = compare x a
//                  if c = 0 then t
//                  elif c < 0 then l 
//                  else
//                      let t' = undefine_list x t
//                      if t' = t then l 
//                      else ab::t'
//            | [] -> []
//        fun x ->
//            let k = hash x
//            let rec und t =
//                match t with
//                | Leaf(h,l) when h = k ->
//                    let l' = undefine_list x l
//                    if l' = l then t
//                    elif l' = [] then Empty
//                    else Leaf(h,l')
//                | Branch(p,b,l,r) when k &&& (b - 1) = p ->
//                    if k &&& b = 0 then
//                        let l' = und l
//                        if l' = l then t
//                        else (
//                            match l' with 
//                            | Empty -> r 
//                            | _ -> Branch(p,b,l',r))
//                    else
//                        let r' = und r
//                        if r' = r then t
//                        else (
//                            match r' with 
//                            | Empty -> l 
//                            | _ -> Branch(p,b,l,r'))
//                | _ -> t
//            und

// ------------------------------------------------------------------------- //
// Redefinition and combination.                                             //
// ------------------------------------------------------------------------- //

    // Finite Partial Functions
    // pg. 621
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Combine together two finite partial functions using pointwise operation.
    //    Description
    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
    //       may sometimes be preferable to ordinary functions since they permit more operations
    //       such as equality comparison, extraction of domain etc.
    //       If f an g are finite partial functions,
    //       then combine op z f g will combine them together in the folloing somewhat complicated
    //       way. If just one of the functions f and g is defined at point x, that will give the value of
    //       the combined function. If both f and g are defined at x with values y1 and y2,  the value
    //       of the combined function will be op y1 y2. However, if the rsulting value y satisfies the 
    //       predicate z, the new function will be undefined at that point; the intuition is that the two
    //       values y1 and y2 cancel each other out.
    //    Failure
    //       Can only fail if the given operation fails.
    //    Uses
    //       When finite partial  functions are used to represent values with a numeric domian (e.g.
    //       matrices or polynomials), this can be used to perform addition pointwise by using addition
    //       for the op argument. Using a zero test as the predicate z will ensure that no zero values
    //       are included in the result, giving a canonical representation.
    //    See also
    //       |->, |=>, apply, applyd, choose, combine, defined, dom, foldl, foldr, graph,
    //       is_undefined, mapf, ran, tryapplyd, undefine, undefined.
    //
    // val ( |-> ) : ('a -> 'b -> func<'a,'b> -> func<'a,'b>) when 'a : comparison
    // val combine : (('c -> 'c -> 'c) -> ('c -> bool) -> func<'d,'c> -> func<'d,'c> -> func<'d,'c>) when 'c : equality and 'd : comparison
    let (|->),combine =
        // val newbranch : int -> func<'a,'b> -> int -> func<'a,'b> -> func<'a,'b>
        let newbranch p1 t1 p2 t2 =
            let zp = p1 ^^^ p2
            let b = zp &&& (-zp)
            let p = p1 &&& (b - 1)
            if p1 &&& b = 0 then Branch(p,b,t1,t2)
            else Branch(p,b,t2,t1)
        // val define_list : 'a * 'b -> ('a * 'b) list -> ('a * 'b) list when 'a : comparison
        let rec define_list (x,y as xy) l =
            match l with
            | (a,b as ab)::t ->
                let c = compare x a
                if c = 0 then xy::t
                elif c < 0 then xy::l
                else ab::(define_list xy t)
            | [] -> [xy]
        // val combine_list :  ('a -> 'a -> 'a) -> ('a -> bool) -> ('b * 'a) list -> ('b * 'a) list -> ('b * 'a) list when 'b : comparison
        let rec combine_list op z l1 l2 =
            match (l1,l2) with
            | [],_ -> l2
            | _,[] -> l1
            | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
                let c = compare x1 x2
                if c < 0 then xy1::(combine_list op z t1 l2)
                elif c > 0 then xy2::(combine_list op z l1 t2) 
                else
                    let y = op y1 y2 
                    let l = combine_list op z t1 t2
                    if z(y) then l 
                    else (x1,y)::l
        // val ( |-> ) : 'a -> 'b -> (func<'a,'b> -> func<'a,'b>) when 'a : comparison
        let (|->) x y =
            let k = hash x
            let rec upd t =
                match t with
                | Empty -> Leaf (k,[x,y])
                | Leaf(h,l) ->
                     if h = k then Leaf(h,define_list (x,y) l)
                     else newbranch h t k (Leaf(k,[x,y]))
                | Branch(p,b,l,r) ->
                    if k &&& (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
                    elif k &&& b = 0 then Branch(p,b,upd l,r)
                    else Branch(p,b,l,upd r)
            upd
        // val combine : ('a -> 'a -> 'a) -> ('a -> bool) -> func<'b,'a> -> func<'b,'a> -> func<'b,'a>  when 'a : equality and 'b : comparison
        let rec combine op z t1 t2 =
            match (t1,t2) with
            | Empty,_ -> t2
            | _,Empty -> t1
            | Leaf(h1,l1),Leaf(h2,l2) ->
                if h1 = h2 then
                    let l = combine_list op z l1 l2
                    if l = [] then Empty 
                    else Leaf(h1,l)
                else newbranch h1 t1 h2 t2
            | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
                if k &&& (b - 1) = p then
                    if k &&& b = 0 then (
                        match combine op z lf l with
                        | Empty -> r 
                        | l' -> Branch(p,b,l',r))
                    else (
                        match combine op z lf r with
                        | Empty -> l 
                        | r' -> Branch(p,b,l,r'))
                else
                    newbranch k lf p br
            | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
                  if k &&& (b - 1) = p then
                      if k &&& b = 0 then (
                           match combine op z l lf with
                           | Empty -> r 
                           | l' -> Branch(p,b,l',r))
                      else (
                           match combine op z r lf with
                           | Empty -> l 
                           | r' -> Branch(p,b,l,r'))
                  else
                      newbranch p br k lf
            | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
                  if b1 < b2 then
                      if p2 &&& (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
                      elif p2 &&& b1 = 0 then (
                          match combine op z l1 t2 with
                          | Empty -> r1 
                          | l -> Branch(p1,b1,l,r1))
                      else (
                          match combine op z r1 t2 with
                          | Empty -> l1 
                          | r -> Branch(p1,b1,l1,r))
                  elif b2 < b1 then
                      if p1 &&& (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
                      elif p1 &&& b2 = 0 then (
                           match combine op z t1 l2 with
                           | Empty -> r2 
                           | l -> Branch(p2,b2,l,r2))
                      else (
                           match combine op z t1 r2 with
                           | Empty -> l2 
                           | r -> Branch(p2,b2,l2,r))
                  elif p1 = p2 then (
                      match (combine op z l1 l2,combine op z r1 r2) with
                      | (Empty,r) -> r 
                      | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
                  else
                      newbranch p1 t1 p2 t2
        (|->),combine
         
// ------------------------------------------------------------------------- //
// Special case of point function.                                           //
// ------------------------------------------------------------------------- //

    // pg. 621
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Gives a one-point finite partial function.
    //    Description
    //       This is one of a suite of operations onf finite partial functions, type ('a,b')func. These
    //       may sometimes be preferable to ordinary functions since they permit more operations
    //       such as equality comparison, extraction of domain etc.
    //       The call x |=> y gives a finite
    //       partial function that maps x to y and is undefined for all arguments other than x.
    //    See also
    //       |->, |=>, apply, applyd, choose, combine, defined, dom, foldl, foldr, graph,
    //       is_undefined, mapf, ran, tryapplyd, undefine, undefined.
    //
    // val ( |=> ) : 'a -> 'b -> func<'a,'b> when 'a : comparison
    let (|=>) = 
        fun x y -> 
            (x |-> y) undefined

    // val ( |=>* ) : 'a -> 'b -> Map<'a,'b> when 'a : comparison
    let (|=>*) x y = Map.ofList [(x,y)]

    // val ( |->* ) : 'a -> 'b -> Map<'a,'b> -> Map<'a,'b> when 'a : comparison
    let (|->*) a b m = Map.add a b m

// ------------------------------------------------------------------------- //
// Handy list operations.                                                    //
// ------------------------------------------------------------------------- //

//    // pg. 619 - list iterator
//    // f - accumulator function
//    // l - list
//    // b - initial value
//    // use List.fold f b l
//    // val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
//    let rec itlist f l b =
//        match l with
//        | []     -> b
//        | (h::t) -> f h (itlist f t b)

// pg. 619
// ------------------------------------------------------------------------- //
// Explosion and implosion of strings.                                       //
// ------------------------------------------------------------------------- //

    // pg. 619
    // val explode : string -> string list
    let explode (s : string) =
        let rec exap n l =
            if n < 0 then l
            else exap (n - 1) ((s.Substring(n,1))::l)
        exap ((String.length s) - 1) []
        
//    // pg. 619
//    // val implode : string list -> string
//    let implode l = itlist (+) l ""

// ------------------------------------------------------------------------- //
// List membership. This does *not* assume the list is a set.                //
// ------------------------------------------------------------------------- //

    // pg. 620
    // val mem : 'a -> 'a list -> bool when 'a : comparison
    //
    // HOL Light Reference :
    //    Synopis : 
    //       Tests whether a list contains a certain member.
    //    Description
    //       mem x [x1;...;xn] return true if some xi in the list is equal to x.
    //       Otherwise it returns false.
    //    Failure
    //       Never fails.
    //    See also
    //       find, tryfind, exists, forall, assoc, rev_assoc
    //
    let rec mem x lis =
        match lis with
        | []     -> false
        | (h::t) -> (compare x h = 0) || (mem x t)

// pg. 623
// ------------------------------------------------------------------------- //
// General parsing of iterated infixes.                                      //
// ------------------------------------------------------------------------- //

    // val parse_ginfix :
    //   'a ->
    //     (('b -> 'c) -> 'b -> 'b -> 'c) ->
    //       ('b -> 'c) -> ('a list -> 'b * 'a list) -> 'a list -> 'c * 'a list
    //     when 'a : equality
    let rec parse_ginfix opsym opupdate sof subparser inp =
        let e1,inp1 = subparser inp
        if (inp1 <> []) && (List.head inp1 = opsym) then parse_ginfix opsym opupdate (opupdate sof e1) subparser (List.tail inp1)
        else sof e1,inp1

    // val parse_left_infix :
    //   'a ->
    //     ('b * 'b -> 'b) -> (('a list -> 'b * 'a list) -> 'a list -> 'b * 'a list)
    //     when 'a : equality
    let parse_left_infix opsym opcon =
        parse_ginfix opsym (fun f e1 e2 -> opcon(f e1,e2)) (fun x -> x)

    // val parse_right_infix :
    //   'a ->
    //     ('b * 'b -> 'b) -> (('a list -> 'b * 'a list) -> 'a list -> 'b * 'a list)
    //     when 'a : equality
    let parse_right_infix opsym opcon =
        parse_ginfix opsym (fun f e1 e2 -> f(opcon(e1,e2))) (fun x -> x)

    // val parse_list :
    //   'a -> (('a list -> 'b * 'a list) -> 'a list -> 'b list * 'a list)
    //     when 'a : equality
    let parse_list opsym =
        parse_ginfix opsym (fun f e1 e2 -> (f e1)@[e2]) (fun x -> [x])

// pg. 624
// ------------------------------------------------------------------------- //
// Other general parsing combinators.                                        //
// ------------------------------------------------------------------------- //

    // val papply : ('a -> 'b) -> 'a * 'c -> 'b * 'c
    let papply f (ast,rest) = 
        (f ast,rest)

    // val nextin : 'a list -> 'a -> bool when 'a : equality
    let nextin inp tok = 
        (inp <> []) && (List.head inp = tok)

    // val parse_bracketed :
    //   ('a -> 'b * 'c list) -> 'c -> 'a -> 'b * 'c list when 'c : equality
    let parse_bracketed subparser cbra inp =
        let ast,rest = subparser inp
        if nextin rest cbra then ast,List.tail rest
        else failwith "Closing bracket expected"

// pg. 119
// ------------------------------------------------------------------------- //
// Terms.                                                                    //
// ------------------------------------------------------------------------- //

    // Terms are intended to denote 'objects' in the domain being reasoned about (numbers, people, sets or whatever).
    // Terms are built up from (object-denoting) variables using functions.
    // Functions can have nay number of arguments, this number being known as the arity of the function.
    type term = 
        | Var of string
        | Fn of string * term list


// pg. 119
// ------------------------------------------------------------------------- //
// Abbreviation for FOL formula.                                             //
// ------------------------------------------------------------------------- //

    // Each atomic proposition is now analyzed into a named predicate or relation applied to any finite number of terms.
    type fol = 
        | R of string * term list

// pg. 26
// ========================================================================= //
// Polymorphic type of formulas.                     //
// ========================================================================= //

    // Formulas are intuitively intended to be trure or false
    type formula<'a> = 
        | False
        | True
        | Atom   of 'a
        | Not    of formula<'a>
        | And    of formula<'a> * formula<'a>
        | Or     of formula<'a> * formula<'a>
        | Imp    of formula<'a> * formula<'a>
        | Iff    of formula<'a> * formula<'a>
        | Forall of string * formula<'a>
        | Exists of string * formula<'a>

// pg. 625
// ------------------------------------------------------------------------- //
// Parsing of formulas, parametrized by atom parser "pfn".                   //
// ------------------------------------------------------------------------- //

    // val parse_atomic_formula :
    //   (string list -> string list -> 'a formula * string list) *
    //   (string list -> string list -> 'a formula * string list) ->
    //     string list -> string list -> 'a formula * string list
    let rec parse_atomic_formula (ifn,afn) vs inp =
        match inp with
        | []                                    -> failwith "formula expected"
        | "false"::rest                         -> False,rest
        | "true"::rest                          -> True,rest
        | "("::rest -> 
            (try ifn vs inp with Failure _      -> parse_bracketed (parse_formula (ifn,afn) vs) ")" rest)
        | "~"::rest                             -> papply (fun p -> Not p) (parse_atomic_formula (ifn,afn) vs rest)
        | "forall"::x::rest                     -> parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Forall(x,p)) x rest
        | "exists"::x::rest                     -> parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Exists(x,p)) x rest
        | _                                     -> afn vs inp
    // val parse_quant :
    //   (string list -> string list -> 'a formula * string list) *
    //   (string list -> string list -> 'a formula * string list) ->
    //     string list ->
    //       (string * 'a formula -> 'a formula) ->
    //         string -> string list -> 'a formula * string list
    and parse_quant (ifn,afn) vs qcon x inp =
        match inp with
        | []      -> failwith "Body of quantified term expected"
        | y::rest -> papply (fun fm -> qcon(x,fm)) (if y = "." then parse_formula (ifn,afn) vs rest else parse_quant (ifn,afn) (y::vs) qcon y rest)
    // val parse_formula :
    //   (string list -> string list -> 'a formula * string list) *
    //   (string list -> string list -> 'a formula * string list) ->
    //     string list -> string list -> 'a formula * string list
    and parse_formula (ifn,afn) vs inp =
        parse_right_infix "<=>" (fun (p,q) -> Iff(p,q))
            (parse_right_infix "==>" (fun (p,q) -> Imp(p,q))
                (parse_right_infix "\\/" (fun (p,q) -> Or(p,q))
                    (parse_right_infix "/\\" (fun (p,q) -> And(p,q))
                        (parse_atomic_formula (ifn,afn) vs)))) inp

// pg. 17
// ------------------------------------------------------------------------- //
// Lexical analysis.                                                         //
// ------------------------------------------------------------------------- //

    // val matches : string -> (string -> bool)
    let matches s = 
        let chars = explode s
        fun c -> mem c chars

    // val space : (string -> bool)
    let space = matches " \t\n\r"

    // val punctuation : (string -> bool)
    let punctuation = matches "()[]{},"

    // val symbolic : (string -> bool)
    let symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"

    // val numeric : (string -> bool)
    let numeric = matches "0123456789"

    // val alphanumeric : (string -> bool)
    let alphanumeric = matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

    // val lexwhile : (string -> bool) -> string list -> string * string list
    let rec lexwhile prop inp =
        match inp with
        | c::cs when prop c -> 
            let tok,rest = lexwhile prop cs
            c+tok,rest
        | _ -> "",inp

    // val lex : string list -> string list
    let rec lex inp =
        match snd(lexwhile space inp) with
        | []    -> []
        | c::cs -> 
            let prop = 
                if alphanumeric(c) then alphanumeric
                else if symbolic(c) then symbolic
                else fun c -> false
            let toktl,rest = lexwhile prop cs
            (c+toktl)::lex rest

// pg. 20
// ------------------------------------------------------------------------- //
// Generic function to impose lexing and exhaustion checking on a parser.    //
// ------------------------------------------------------------------------- //

    // val make_parser : (string list -> 'a * 'b list) -> string -> 'a
    let make_parser pfn s =
        let expr,rest = 
            pfn (lex(explode s))
        match rest with
        | [] -> expr
        | _  -> failwith "Unparsed input"

// pg. 628
// ------------------------------------------------------------------------- //
// Parsing of terms.                                                         //
// ------------------------------------------------------------------------- //

    // val is_const_name : string -> bool
    let is_const_name s = List.forall numeric (explode s) || s = "nil"

    // val parse_atomic_term : string list -> string list -> term * string list
    let rec parse_atomic_term vs inp =
        match inp with
        | [] -> failwith "term expected"
        | "("::rest -> parse_bracketed (parse_term vs) ")" rest
        | "-"::rest -> papply (fun t -> Fn("-",[t])) (parse_atomic_term vs rest)
        | f::"("::")"::rest -> Fn(f,[]),rest
        | f::"("::rest ->
            papply (fun args -> Fn(f,args))
                    (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
        | a::rest ->
            (if is_const_name a && not(mem a vs) then Fn(a,[]) else Var a),rest

    // val parse_term : string list -> string list -> term * string list
    and parse_term vs inp =
        parse_right_infix "::" (fun (e1,e2) -> Fn("::",[e1;e2]))
            (parse_right_infix "+" (fun (e1,e2) -> Fn("+",[e1;e2]))
                (parse_left_infix "-" (fun (e1,e2) -> Fn("-",[e1;e2]))
                    (parse_right_infix "*" (fun (e1,e2) -> Fn("*",[e1;e2]))
                        (parse_left_infix "/" (fun (e1,e2) -> Fn("/",[e1;e2]))
                        (parse_left_infix "^" (fun (e1,e2) -> Fn("^",[e1;e2]))
                            (parse_atomic_term vs)))))) inp

    // val parset : (string -> term)
    let parset = make_parser (parse_term [])

// pg. 628
// ------------------------------------------------------------------------- //
// Parsing of formulas.                                                      //
// ------------------------------------------------------------------------- //

    // val parse_infix_atom : string list -> string list -> fol formula * string list
    let parse_infix_atom vs inp =       
        let tm,rest = parse_term vs inp
        if List.exists (nextin rest) ["="; "<"; "<="; ">"; ">="] then                     
            papply (fun tm' -> Atom(R(List.head rest,[tm;tm'])))                          
                    (parse_term vs (List.tail rest))                                       
        else failwith ""
                             
    // val parse_atom : string list -> string list -> fol formula * string list                                  
    let parse_atom vs inp =
        try parse_infix_atom vs inp with Failure _ ->                                
        match inp with                                                               
        | p::"("::")"::rest -> Atom(R(p,[])),rest                                    
        | p::"("::rest ->
            papply (fun args -> Atom(R(p,args)))
                    (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
        | p::rest when p <> "(" -> Atom(R(p,[])),rest
        | _ -> failwith "parse_atom"
                                     
    // val parse : (string -> fol formula)                                          
    let parse = make_parser (parse_formula (parse_infix_atom,parse_atom) [])  

// pg. 131
// ------------------------------------------------------------------------- //
// Substitution within terms.                                                //
// ------------------------------------------------------------------------- //

    // val tsubst : func<string,term> -> term -> term
    let rec tsubst sfn tm =
        match tm with
        | Var x      -> tryapplyd sfn x tm
        | Fn(f,args) -> Fn(f,List.map (tsubst sfn) args)
        
// pg. 187
// ------------------------------------------------------------------------- //
// Matching of terms and literals.                                           //
// ------------------------------------------------------------------------- //

    // val term_match000 : func<string,term> -> (term * term) list -> 'a
    let rec term_match000 env eqs =
        match eqs with
        | (Fn(f,fa),Fn(g,ga))::oth when f = g && List.length fa = List.length ga ->
            term_match000 env (List.zip fa ga @ oth)
        | (Var x,t)::oth ->
            if not (defined env x) then term_match000 ((x |-> t) env) oth
            elif apply env x = t then term_match000 env oth
            else failwith "term_match000"
        | _ -> failwith "term_match000"
        
    // val rewrite1000 : fol formula list -> term -> term
    let rec rewrite1000 eqs t =
        match eqs with
        | Atom(R("=",[l;r]))::oeqs ->
            try tsubst (term_match000 undefined [l,t]) r with 
            | Failure _ -> rewrite1000 oeqs t
        | _ -> failwith "rewrite1000"

    // val rewrite000 : fol formula list -> term -> term
    let rec rewrite000 eqs tm =
        try rewrite000 eqs (rewrite1000 eqs tm) with 
        | Failure _ ->
            match tm with
            | Var x -> tm
            | Fn(f,args) -> 
                let tm' = Fn(f,List.map (rewrite000 eqs) args)
                if tm' = tm then tm 
                else rewrite000 eqs tm'

// pg. 629
// ------------------------------------------------------------------------- //
// Printing of terms.                                                        //
// ------------------------------------------------------------------------- //

    let rec print_term prec fm =
        match fm with
        | Var x -> printf "%s" x
        | Fn("^",[tm1;tm2]) -> print_infix_term true prec 24 "^" tm1 tm2
        | Fn("/",[tm1;tm2]) -> print_infix_term true prec 22 " /" tm1 tm2
        | Fn("*",[tm1;tm2]) -> print_infix_term false prec 20 " *" tm1 tm2
        | Fn("-",[tm1;tm2]) -> print_infix_term true prec 18 " -" tm1 tm2
        | Fn("+",[tm1;tm2]) -> print_infix_term false prec 16 " +" tm1 tm2
        | Fn("::",[tm1;tm2]) -> print_infix_term false prec 14 "::" tm1 tm2
        | Fn(f,args) -> print_fargs f args

    and print_fargs f args =
        printf "%s" f
        if args = [] then () else
        (printf "(";
//        open_box 0;
        print_term 0 (List.head args); 
//        print_break 0 0;
        do_list (
                fun t -> 
                    printf ","
    //                print_break 0 0;
                    print_term 0 t)
            (List.tail args);
//        close_box();
        printf ")")

    and print_infix_term isleft oldprec newprec sym p q =
        if oldprec > newprec then 
            printf "(";
//             open_box 0
        else ();
        print_term (if isleft then newprec else newprec+1) p;
        printf "%s" sym;
//        print_break (if String.sub sym 0 1 = " " then 1 else 0) 0;
        print_term (if isleft then newprec+1 else newprec) q;
        if oldprec > newprec then 
//            close_box()
            printf ")"
        else ()

    // TODO: Add this to a library, possibly lib.fs
    let rec print_fpf_list l =
        match l with
        | (a,b)::t -> 
            printf "fpf key: %A " a;
            printf "fpf value: ";
//            print_term 0 b;
            printf "value: %A " b;
            print_fpf_list t
        | [] -> ()

    let rec print_fpf (f:func<'a,'b>) = 
      match f with
      | Empty -> printf "Empty"
      | Leaf(h,l) -> 
          Printf.printf "Leaf: %i " h;
          print_fpf_list l
      | Branch(p,b,l,r) ->
          Printf.printf "Branch: p: %i, b: %i " p b;
          Printf.printf "\n";
          print_fpf l;
          Printf.printf "\n";
          print_fpf r;
          Printf.printf "\n"

// =============================================================================================
                    
    let test000 () =
        printfn "%s" "test000"
        let result = rewrite000 [(parse "0 + x = x"); (parse "S(x) + y = S(x + y)");
                        (parse "0 * x = 0"); (parse "S(x) * y = y + x * y")]
                        (parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))")
        printfn "%A" result

    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_32\mscorlib\v4.0_4.0.0.0__b77a5c561934e089\mscorlib.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook.Tests\bin\Debug\Reasoning.Automated.Harrison.Handbook.Tests.exe', Symbols loaded.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook.Tests\bin\Debug\Reasoning.Automated.Harrison.Handbook.dll', Symbols loaded.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_MSIL\FSharp.Core\v4.0_4.0.0.0__b03f5f7f11d50a3a\FSharp.Core.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_MSIL\System\v4.0_4.0.0.0__b77a5c561934e089\System.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll 

    // Fn
    //   ("+",
    //    [Fn
    //       ("*",
    //        [Fn ("S",[Fn ("S",[Fn ("S",[Fn ("0",[])])])]);
    //         Fn ("S",[Fn ("S",[Fn ("0",[])])])]);
    //     Fn ("S",[Fn ("S",[Fn ("S",[Fn ("S",[Fn ("0",[])])])])])])

// =============================================================================================

    // val term_match000 : func<string,term> -> (term * term) list -> 'a
    // val term_match001 : func<string,term> -> (term * term) list -> 'a option
    let rec term_match001 env eqs =
        match eqs with
        | (Fn(f,fa),Fn(g,ga))::oth when f = g && List.length fa = List.length ga ->
            let a = term_match001 env (List.zip fa ga @ oth)
            match a with
            | Some(a) -> Some(a)
            | None -> None
        | (Var x,t)::oth ->
            if not (defined env x) then 
                let a = term_match001 ((x |-> t) env) oth
                match a with
                | Some(a) -> Some(a)
                | None -> None
            elif apply env x = t then 
                let a = term_match001 env oth
                match a with
                | Some(a) -> Some(a)
                | None -> None
            else None
        | _ -> None
        
    // val rewrite1000 :    fol formula list -> term -> term
    // val rewrite1001 : fol formula list -> term -> term option
    let rec rewrite1001 eqs t =
        match eqs with
        | Atom(R("=",[l;r]))::oeqs ->
            let x = (term_match001 undefined [l,t])
            match x with 
            | Some(y) -> Some(tsubst y r)
            | None    -> 
                let a = rewrite1001 oeqs t
                match a with
                | Some(a) -> Some(a)
                | None -> None
        | _ -> None

    // val rewrite000 : fol formula list -> term -> term
    // val rewrite001 : fol formula list -> term -> term
    let rec rewrite001 eqs tm =
        let x = rewrite1001 eqs tm
        match x with
        | Some(y) -> y
        | None -> 
            match tm with
            | Var x -> tm
            | Fn(f,args) -> 
                let tm' = Fn(f,List.map (rewrite001 eqs) args)
                if tm' = tm then tm 
                else rewrite001 eqs tm'
                    
    let test001 () =
        printfn "%s" "test001"
        let result = rewrite001 [(parse "0 + x = x"); (parse "S(x) + y = S(x + y)");
                        (parse "0 * x = 0"); (parse "S(x) * y = y + x * y")]
                        (parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))")
        printfn "%A" result

    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_32\mscorlib\v4.0_4.0.0.0__b77a5c561934e089\mscorlib.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook.Tests\bin\Debug\Reasoning.Automated.Harrison.Handbook.Tests.exe', Symbols loaded.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook.Tests\bin\Debug\Reasoning.Automated.Harrison.Handbook.dll', Symbols loaded.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_MSIL\FSharp.Core\v4.0_4.0.0.0__b03f5f7f11d50a3a\FSharp.Core.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_MSIL\System\v4.0_4.0.0.0__b77a5c561934e089\System.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll
    // A first chance exception of type 'System.Exception' occurred in FSharp.Core.dll

    // n
    //  ("+",
    //   [Fn
    //      ("*",
    //       [Fn ("S",[Fn ("S",[Fn ("S",[Fn ("0",[])])])]);
    //        Fn ("S",[Fn ("S",[Fn ("0",[])])])]);
    //    Fn ("S",[Fn ("S",[Fn ("S",[Fn ("S",[Fn ("0",[])])])])])])

// =============================================================================================
  
    // val apply    : func<'a,'b>          -> ('a -> 'b)          when 'a : comparison  // failwith "apply"
    // val apply002 : func<'a,'b option>   -> ('a -> 'b option)   when 'a : comparison  // None
    // val apply002 : func<'a,func<'b,'c>> -> ('a -> func<'b,'c>) when 'a : comparison  // Empty
    // val apply002 : func<'a,unit>        -> ('a -> unit)        when 'a : comparison  // ()
    // val apply002 : func<'a,'a>          -> ('a -> 'a)          when 'a : comparison  // x
    // val apply002 : func<'a,unit>        -> ('a -> unit)        when 'a : comparison  // printfn "fail"
    // val apply002 : func<'a,bool>        -> ('a -> bool)        when 'a : comparison  // false
    // val apply002 : func<'a,int>         -> ('a -> int)         when 'a : comparison  // 1
    // val apply002 : func<'a,term>        -> ('a -> term)        when 'a : comparison  // Var("fail")
    let apply002 fOption = 
        let fResult = 
//            fun x -> failwith "apply"
//            fun x -> None
//            fun x -> Empty
//            fun x -> ()
//            fun x -> x
//            fun x -> printfn "fail"
//            fun x -> false
            fun x -> Var("fail")
        applyd fOption fResult

    // val defined :    func<'a,'b>        -> 'a -> bool when 'a : comparison
    // val defined002 : func<'a,'b option> -> 'a -> bool when 'a : comparison
    let defined002 f x =
        let result = apply002 f x
        match result with 
        | Var("fail") -> false
        | _           -> true
            
    // val term_match000 : func<string,term> -> (term * term) list -> 'a
    // val term_match001 : func<string,term> -> (term * term) list -> 'a option
    // val term_match002 : func<string,term> -> (term * term) list -> 'a option
    let rec term_match002 env eqs =
        match eqs with
        | (Fn(f,fa),Fn(g,ga))::oth when f = g && List.length fa = List.length ga ->
            let a = term_match002 env (List.zip fa ga @ oth)
            match a with
            | Some(a)                            -> Some(a)
            | None                               -> None
        | (Var x,t)::oth ->
            if not (defined002 env x) then 
                let b = (x |-> t)
                let c = b env
                let a = term_match002 c oth
                match a with
                | Some(a)                        -> Some(a)
                | None                           -> None
            elif apply env x = t then 
                let a = term_match002 env oth
                match a with
                | Some(a)                        -> Some(a)
                | None                           -> None
            else None
        | _                                      -> None
        
    // val rewrite1000 : fol formula list -> term -> term
    // val rewrite1001 : fol formula list -> term -> term option
    // val rewrite1002 : fol formula list -> term -> term option
    let rec rewrite1002 eqs t =
        match eqs with
        | Atom(R("=",[l;r]))::oeqs ->
            let x = (term_match002 undefined [l,t])
            match x with 
            | Some(y) -> Some(tsubst y r)
            | None    -> 
                let a = rewrite1002 oeqs t
                match a with
                | Some(a) -> Some(a)
                | None -> None
        | _ -> None
        
    // val rewrite000 : fol formula list -> term -> term
    // val rewrite001 : fol formula list -> term -> term
    // val rewrite002 : fol formula list -> term -> term
    let rec rewrite002 eqs tm =
        let x = rewrite1002 eqs tm
        match x with
        | Some(y) -> y
        | None -> 
            match tm with
            | Var x -> tm
            | Fn(f,args) -> 
                let tm' = Fn(f,List.map (rewrite002 eqs) args)
                if tm' = tm then tm 
                else rewrite002 eqs tm'

    let test002 () =
        printfn "%s" "test002"
        let result = rewrite002 [(parse "0 + x = x"); (parse "S(x) + y = S(x + y)");
                        (parse "0 * x = 0"); (parse "S(x) * y = y + x * y")]
                        (parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))")
        printfn "%A" result

    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_32\mscorlib\v4.0_4.0.0.0__b77a5c561934e089\mscorlib.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook.Tests\bin\Debug\Reasoning.Automated.Harrison.Handbook.Tests.exe', Symbols loaded.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook.Tests\bin\Debug\Reasoning.Automated.Harrison.Handbook.dll', Symbols loaded.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_MSIL\FSharp.Core\v4.0_4.0.0.0__b03f5f7f11d50a3a\FSharp.Core.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.
    // 'Reasoning.Automated.Harrison.Handbook.Tests.exe' (Managed (v4.0.30319)): Loaded 'C:\Windows\Microsoft.Net\assembly\GAC_MSIL\System\v4.0_4.0.0.0__b77a5c561934e089\System.dll', Skipped loading symbols. Module is optimized and the debugger option 'Just My Code' is enabled.

    // Fn
    //   ("+",
    //    [Fn
    //       ("*",
    //        [Fn ("S",[Fn ("S",[Fn ("S",[Fn ("0",[])])])]);
    //         Fn ("S",[Fn ("S",[Fn ("0",[])])])]);
    //     Fn ("S",[Fn ("S",[Fn ("S",[Fn ("S",[Fn ("0",[])])])])])])

// =============================================================================================
  
    // val apply    : func<'a,'b>          -> ('a -> 'b)          when 'a : comparison  failwith "apply"
    let apply003 fOption = 
        let fResult = 
//            fun x -> failwith "apply"
//            fun x -> None
//            fun x -> Empty
//            fun x -> ()
//            fun x -> x
//            fun x -> printfn "fail"
//            fun x -> false
            fun x -> Var("fail")
        applyd fOption fResult

    // val defined :    func<'a,'b>        -> 'a -> bool when 'a : comparison
    // val defined002 : func<'a,'b option> -> 'a -> bool when 'a : comparison
    let defined003 f x =
        let result = apply003 f x
        match result with 
        | Var("fail") -> false
        | _           -> true
            
    // val term_match000 : func<string,term> -> (term * term) list -> 'a
    // val term_match001 : func<string,term> -> (term * term) list -> 'a option
    // val term_match002 : func<string,term> -> (term * term) list -> 'a option
    let rec term_match003 env eqs =
        match eqs with
        | (Fn(f,fa),Fn(g,ga))::oth when f = g && List.length fa = List.length ga ->
            let a = term_match003 env (List.zip fa ga @ oth)
            match a with
            | Some(a)                            -> Some(a)
            | None                               -> None
        | (Var x,t)::oth ->
            if not (defined003 env x) then 
                let b = (x |-> t)
                let c = b env
                let a = term_match003 c oth
                match a with
                | Some(a)                        -> Some(a)
                | None                           -> None
            elif apply003 env x = t then 
                let a = term_match003 env oth
                match a with
                | Some(a)                        -> Some(a)
                | None                           -> None
            else None
        | _                                      -> None
        
    // val rewrite1000 : fol formula list -> term -> term
    // val rewrite1001 : fol formula list -> term -> term option
    // val rewrite1002 : fol formula list -> term -> term option
    let rec rewrite1003 eqs t =
        match eqs with
        | Atom(R("=",[l;r]))::oeqs ->
            let x = (term_match003 undefined [l,t])
            match x with 
            | Some(y) -> Some(tsubst y r)
            | None    -> 
                let a = rewrite1003 oeqs t
                match a with
                | Some(a) -> Some(a)
                | None -> None
        | _ -> None
        
    // val rewrite000 : fol formula list -> term -> term
    // val rewrite001 : fol formula list -> term -> term
    // val rewrite002 : fol formula list -> term -> term
    let rec rewrite003 eqs tm =
        let x = rewrite1003 eqs tm
        match x with
        | Some(y) -> y
        | None -> 
            match tm with
            | Var x -> tm
            | Fn(f,args) -> 
                let tm' = Fn(f,List.map (rewrite003 eqs) args)
                if tm' = tm then tm 
                else rewrite003 eqs tm'

    let test003 () =
        printfn "%s" "test003"
        let result = rewrite003 [(parse "0 + x = x"); (parse "S(x) + y = S(x + y)");
                        (parse "0 * x = 0"); (parse "S(x) * y = y + x * y")]
                        (parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))")
        printfn "%A" result

// =============================================================================================

    // val apply004 : Map<'a,'b> -> 'a -> 'b when 'a : comparison
    let apply004 m k =
        Map.find k m

    // val flip004 : 'a -> ('a -> 'b -> 'c) -> 'b -> 'c
    let flip004 a b c = b a c
    
    // val defined004 :
    //   'a -> 'b -> ((('c -> Map<'c,'d> -> bool) -> 'e -> 'f) -> 'e -> 'f)
    //     when 'c : comparison
    let defined004 f x =
        flip004 Map.containsKey 
            
    // val term_match000 : func<string,term> -> (term * term) list -> 'a
    // val term_match001 : func<string,term> -> (term * term) list -> 'a option
    // val term_match002 : func<string,term> -> (term * term) list -> 'a option
    let rec term_match004 env eqs =
//        printfn "env: %A" env
//        printfn "eqs: %A" eqs
        match eqs with
        | (Fn(f,fa),Fn(g,ga))::oth when f = g && List.length fa = List.length ga ->
            let a = term_match004 env (List.zip fa ga @ oth)
//            printfn "   term_match004: %A" a
            match a with
            | Some(a)                            -> Some(a)
            | None                               -> None
        | (Var x,t)::oth ->
            if not (Map.containsKey x env) then 
                let b = (x |->* t)
                let c = b env
                let a = term_match004 c oth
//                printfn "   term_match004: %A" a
                match a with
                | Some(a)                        -> Some(a)
                | None                           -> None
            elif apply004 env x = t then 
                let a = term_match004 env oth
//                printfn "   term_match004: %A" a
                match a with
                | Some(a)                        -> Some(a)
                | None                           -> None
            else None
        | _                                      -> None

    let term_match004_out env eqs = 
        let result = term_match004 env eqs in
        match result with
        | Some(a) -> 
            print_fpf a;
            printfn ""
        | None -> printfn "term_match004 %s" "None"
        result;;
        
    // val rewrite1000 : fol formula list -> term -> term
    // val rewrite1001 : fol formula list -> term -> term option
    // val rewrite1002 : fol formula list -> term -> term option
    let rec rewrite1004 eqs t =
        match eqs with
        | Atom(R("=",[l;r]))::oeqs ->
            let x = (term_match004_out Map.empty [l,t])
//            printfn "   term_match004: %A" x
            match x with 
            | Some(y) -> Some(tsubst y r)
            | None    -> 
                let a = rewrite1004 oeqs t
                match a with
                | Some(a) -> Some(a)
                | None -> None
        | _ -> None

    let rewrite1004_out eqs t =
        let result = rewrite1004 eqs t
        match result with
        | Some(a) -> 
            print_term 0 a
        | _ -> printfn "rewrite1004 %s" "None"
        result
        
    // val rewrite000 : fol formula list -> term -> term
    // val rewrite001 : fol formula list -> term -> term
    // val rewrite002 : fol formula list -> term -> term
    let rec rewrite004 eqs tm =
        let x = rewrite1004_out eqs tm
        match x with
        | Some(y) -> y
        | None -> 
            match tm with
            | Var x -> tm
            | Fn(f,args) -> 
                let tm' = Fn(f,List.map (rewrite004 eqs) args)
                if tm' = tm then tm 
                else rewrite004 eqs tm'

    let test004 () =
        printfn "%s" "test004"
        let eq1 = parse "0 + x = x"
        let eq2 = parse "S(x) + y = S(x + y)"
        let eq3 = parse "0 * x = 0"
        let eq4 = parse "S(x) * y = y + x * y"
        let tm1 = parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))"
        let result = rewrite004 [eq1; eq2; eq3; eq4] tm1
        printfn "%A" result

// =============================================================================================



// =============================================================================================
  
//    // val term_match000 : func<string,term> -> (term * term) list -> 'a
//    // val term_match001 : func<string,term> -> (term * term) list -> 'a option
//    // val term_match002 : func<string,term> -> (term * term) list -> 'a option
//    let rec term_match004 (env : func<string,term>) eqs =
//        match eqs with
//        | (Fn(f,fa),Fn(g,ga))::oth when f = g && List.length fa = List.length ga ->
//            let a = term_match004 env (List.zip fa ga @ oth)
//            match a with
//            | Some(a)                            -> Some(a)
//            | None                               -> None
//        | (Var x,t)::oth ->
//            let fResult = fun x -> Var("Fail")
//            let test = applyd env fResult x
//            match test with
//            | Var(str) when str = "fail" -> 
//                let b = (x |-> t)
//                let c = b env
//                let a = term_match004 c oth
//                match a with
//                | Some(a)                        -> Some(a)
//                | None                           -> None
//            | _ ->
//                if apply env x = t then 
//                    let a = term_match004 env oth
//                    match a with
//                    | Some(a)                    -> Some(a)
//                    | None                       -> None
//                else None
//        | _                                      -> None
//        
//    // val rewrite1000 : fol formula list -> term -> term
//    // val rewrite1001 : fol formula list -> term -> term option
//    // val rewrite1002 : fol formula list -> term -> term option
//    let rec rewrite1004 eqs t =
//        match eqs with
//        | Atom(R("=",[l;r]))::oeqs ->
//            let x = (term_match004 undefined [l,t])
//            match x with 
//            | Some(y) -> Some(tsubst y r)
//            | None    -> 
//                let a = rewrite1004 oeqs t
//                match a with
//                | Some(a) -> Some(a)
//                | None -> None
//        | _ -> None
//        
//    // val rewrite000 : fol formula list -> term -> term
//    // val rewrite001 : fol formula list -> term -> term
//    // val rewrite002 : fol formula list -> term -> term
//    let rec rewrite004 eqs tm =
//        let x = rewrite1004 eqs tm
//        match x with
//        | Some(y) -> y
//        | None -> 
//            match tm with
//            | Var x -> tm
//            | Fn(f,args) -> 
//                let tm' = Fn(f,List.map (rewrite004 eqs) args)
//                if tm' = tm then tm 
//                else rewrite004 eqs tm'
//
//    let test004 () =
//        printfn "%s" "test004"
//        let result = rewrite004 [(parse "0 + x = x"); (parse "S(x) + y = S(x + y)");
//                        (parse "0 * x = 0"); (parse "S(x) * y = y + x * y")]
//                        (parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))")
//        printfn "%A" result

// =============================================================================================

    let test100 () =
        printfn "%s" "test100"
        let result = applyd undefined (fun x -> x) 1
        printfn "%A" result
        // val result : int = 1

    let test101 () =
        printfn "%s" "test101"
        let result = applyd (1 |=> 2) (fun x -> x) 1
        printfn "%A" result
        // val result : int = 2

// =============================================================================================


    let rec istriv005 env x t =
        match t with
        | Var y -> y = x || defined env y && istriv005 env x (apply env y)
        | Fn(f,args) -> List.exists (istriv005 env x) args && failwith "cyclic"

    let rec unify005 (env : func<string, term>) eqs =
        match eqs with
        | [] -> env
        | (Fn(f,fargs),Fn(g,gargs))::oth ->
            if f = g && List.length fargs = List.length gargs
            then unify005 env (List.zip fargs gargs @ oth)
            else failwith "impossible unification"
        | (Var x,t)::oth | (t,Var x)::oth ->
            if defined env x then unify005 env ((apply env x,t)::oth)
            else unify005 (if istriv005 env x t then env else (x |-> t) env) oth
    
    // pg. 186
    // In order to implement a subsumption test, we first want a procedure for
    // matching, which is a cut-down version of unification allowing instantiation
    // of variable in only the first of each pair of terms. Note theat in contrast to
    // unification we treat the variables in the two terms of a pair as distinct even
    // if their names coincide, and maintain the left-right distinction in recursive
    // calls. This means that we won't need to rename variables first, and won't
    // need to check for cycles. On the other hand, we must remember that apparently
    // 'trivial' mappings  x |-> x are in general necessary, so if x des not have
    // a mapping already and we need to match it to t, we always andd x |-> t to
    // the function enve if t = x. But, stylistically, the definition is very close to
    // that of unify.
    //

    // val term_match000 : func<string,term> -> (term * term) list -> 'a
    let rec term_match005 env eqs =
        match eqs with
        | [] -> env
        | (Fn(f,fa),Fn(g,ga))::oth when (f = g) && ((List.length fa) = (List.length ga)) ->
            term_match005 env (List.zip fa ga @ oth)
        | (Var x,t)::oth ->
            if not (defined env x) then term_match005 ((x |-> t) env) oth
            elif apply env x = t then term_match005 env oth
            else failwith "term_match005"
        | _ -> failwith "term_match005"

    let test500 () =
        let tm1 = parset "x"
        printfn "tm1: %A" tm1
        let tm2 = parset "x"
        printfn "tm2: %A" tm2
        let result = term_match005 Empty [tm1, tm2]
        printfn "term_match005 result: %A" result
        printfn ""

    let test501 () =
        let tm1 = parset "x"
        printfn "tm1: %A" tm1
        let tm2 = parset "y"
        printfn "tm2: %A" tm2
        let result = term_match005 Empty [tm1, tm2]
        printfn "term_match005 result: %A" result
        printfn ""

    let test502 () =
        let tm1 = parset "y"
        printfn "tm1: %A" tm1
        let tm2 = parset "x"
        printfn "tm2: %A" tm2
        let result = term_match005 Empty [tm1, tm2]
        printfn "term_match005 result: %A" result
        printfn ""

    let test503 () =
        let tm1 = parset "x"
        printfn "tm1: %A" tm1
        let tm2 = parset "0"
        printfn "tm2: %A" tm2
        let result = term_match005 Empty [tm1, tm2]
        printfn "term_match005 result: %A" result
        printfn ""

    let test504 () =
        let tm1 = parset "0"
        printfn "tm1: %A" tm1
        let tm2 = parset "x"
        printfn "tm2: %A" tm2
        let result = term_match005 Empty [tm1, tm2]
        printfn "term_match005 result: %A" result
        printfn ""