// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.propexamples

open formulas
open prop

// ========================================================================= //
// Some propositional formulas to test, and functions to generate classes.   //
// ========================================================================= //

// pg. 63
// ------------------------------------------------------------------------- //
// Generate assertion equivalent to R(s,t) <= n for the Ramsey number R(s,t) //
// ------------------------------------------------------------------------- //

let ramsey s t n =
    let vertices = 1 -- n
    let yesgrps = List.map (allsets 2) (allsets s vertices)
    let nogrps = List.map (allsets 2) (allsets t vertices)
    let e [m;n] = Atom(P("p_" + (string m) + "_" + (string n)))
    Or (list_disj (List.map (list_conj << List.map e) yesgrps),
        list_disj (List.map (list_conj << List.map (fun p -> Not (e p))) nogrps))

// pg. 66
// ------------------------------------------------------------------------- //
// Half adder.                                                               //
// ------------------------------------------------------------------------- //

let halfsum x y = Iff (x, Not y)

let halfcarry x y = And (x, y)

let ha x y s c = And (Iff (s, halfsum x y), Iff (c, halfcarry x y))

// pg. 66
// ------------------------------------------------------------------------- //
// Full adder.                                                               //
// ------------------------------------------------------------------------- //

let carry x y z = Or (And (x, y), And (Or (x, y), z))

let sum x y z = halfsum (halfsum x y) z

let fa x y z s c = And (Iff (s, sum x y z), Iff (c, carry x y z))

// pg. 67
// ------------------------------------------------------------------------- //
// Useful idiom.                                                             //
// ------------------------------------------------------------------------- //

let conjoin f l = list_conj (List.map f l)
    
// pg. 67
// ------------------------------------------------------------------------- //
// n-bit ripple carry adder with carry c(0) propagated in and c(n) out.      //
// ------------------------------------------------------------------------- //

let ripplecarry x y c out n =
    conjoin (fun i -> fa (x i) (y i) (c i) (out i) (c (i + 1)))
            (0 -- (n - 1))

// pg. 67
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// Note: Added type for int parameter
let mk_index x (i : int) = Atom (P (x + "_" + (string i)))
let mk_index2 x i j =
    Atom (P (x + "_" + (string i) + "_" + (string j)))

// pg. 67
// ------------------------------------------------------------------------- //
// Special case with 0 instead of c(0).                                      //
// ------------------------------------------------------------------------- //

let ripplecarry0 x y c out n =
    psimplify (ripplecarry x y (fun i -> if i = 0 then False else c i) out n)

// pg. 68
// ------------------------------------------------------------------------- //
// Carry-select adder                                                        //
// ------------------------------------------------------------------------- //

let ripplecarry1 x y c out n =
    psimplify (ripplecarry x y (fun i -> if i = 0 then True else c i) out n)

let mux sel in0 in1 = Or (And (Not sel, in0), And (sel, in1))
    
let offset n x i = x (n + i)

let rec carryselect x y c0 c1 s0 s1 c s n k =
    let k' = min n k
    let fm =
        And (And (ripplecarry0 x y c0 s0 k', ripplecarry1 x y c1 s1 k'),
            And (Iff (c k', mux (c 0) (c0 k') (c1 k')),
                conjoin (fun i -> Iff (s i, mux (c 0) (s0 i) (s1 i)))
                    (0 -- (k' - 1))))
    if k' < k then fm else
        And (fm, carryselect
            (offset k x) (offset k y) (offset k c0) (offset k c1)
            (offset k s0) (offset k s1) (offset k c) (offset k s)
            (n - k) k)

// pg. 69
// ------------------------------------------------------------------------- //
// Equivalence problems for carry-select vs ripple carry adders.             //
// ------------------------------------------------------------------------- //

let mk_adder_test n k =
    let l = List.map mk_index ["x"; "y"; "c"; "s"; "c0"; "s0"; "c1"; "s1"; "c2"; "s2"]
    match l with
    | [x; y; c; s; c0; s0; c1; s1; c2; s2] -> 
        Imp (And (And (carryselect x y c0 c1 s0 s1 c s n k, Not(c 0)), ripplecarry0 x y c2 s2 n), And (Iff (c n,c2 n), conjoin (fun i -> Iff (s i, s2 i)) (0 -- (n - 1))))
    | _ -> failwith "mk_adder_test"
        
// pg. 70
// ------------------------------------------------------------------------- //
// Ripple carry stage that separates off the final result.                   //
//                                                                           //
//       UUUUUUUUUUUUUUUUUUUU  (u)                                           //
//    +  VVVVVVVVVVVVVVVVVVVV  (v)                                           //
//                                                                           //
//    = WWWWWWWWWWWWWWWWWWWW   (w)                                           //
//    +                     Z  (z)                                           //
// ------------------------------------------------------------------------- //

let rippleshift u v c z w n =
    ripplecarry0 u v (fun i -> if i = n then w (n - 1) else c (i + 1))
                    (fun i -> if i = 0 then z else w (i - 1)) n

// pg. 70
// ------------------------------------------------------------------------- //
// Naive multiplier based on repeated ripple carry.                          //
// ------------------------------------------------------------------------- //

let multiplier x u v out n =
    if n = 1 then And (Iff (out 0, x 0 0), Not (out 1)) else
    psimplify (
        And (Iff (out 0, x 0 0),
            And (rippleshift (fun i -> 
                    if i = n - 1 then False
                    else x 0 (i + 1)) (x 1) (v 2) (out 1) (u 2) n, 
                    if n = 2 then And (Iff (out 2, u 2 0), Iff(out 3, u 2 1)) 
                    else conjoin (fun k ->
                        rippleshift (u k) (x k) (v(k + 1)) (out k) (
                            if k = n - 1 then fun i -> out (n + i) 
                            else u (k + 1)) n) (2 -- (n - 1)))))

// pg. 71
// ------------------------------------------------------------------------- //
// Primality examples.                                                       //
// For large examples, should use "num" instead of "int" in these functions. //
// ------------------------------------------------------------------------- //

let rec bitlength x = if x = 0 then 0 else 1 + bitlength (x / 2)

let rec bit n x = if n = 0 then x % 2 = 1 else bit (n - 1) (x / 2)

let congruent_to x m n =
    conjoin (fun i -> if bit i m then x i else Not (x i))
            (0 -- (n - 1))

let prime p =
    let l1 = List.map mk_index ["x"; "y"; "out"]
    match l1 with
    | [x; y; out] ->
        let m i j = And (x i,y j)
        let l2 = List.map mk_index2 ["u"; "v"]
        match l2 with
        | [u; v] ->
            let n = bitlength p
            Not (And (multiplier m u v out (n - 1), congruent_to out p (max n (2 * n - 2))))
        | _ -> failwith "prime"
    | _ -> failwith "prime"
