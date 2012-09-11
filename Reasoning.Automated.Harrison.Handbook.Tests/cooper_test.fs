module cooper_test

open System                                       // Console
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.cooper

let pause () =
    Console.WriteLine ""
    Console.WriteLine("Press any key to continue. ")
    Console.ReadKey () |> ignore


// pg.349
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// In the following example the left side of the equation: 2 * x + 1 is always odd
// while the right side of the equation: 2 * y is always even
// since an even can never equal an odd: (2 * x + 1 = 2 * y) is false
// Since (2 * x + 1 = 2 * y) is negated, i.e. ~, the result is true.

let example001 = integer_qelim (parse "forall x y. ~(2 * x + 1 = 2 * y)")

printf "example 001: " 
print_fol_formula example001

let example002 = integer_qelim (parse "forall x. exists y. 2 * y <= x /\ x < 2 * (y + 1)")
printf "example 002: " 
print_fol_formula example002

let example003 = integer_qelim (parse "exists x y. 4 * x - 6 * y = 1")
printf "example 003: " 
print_fol_formula example003

let example004 = integer_qelim (parse "forall x. ~divides(2,x) /\ divides(3,x-1) <=>
                          divides(12,x-1) \/ divides(12,x-7)")
printf "example 004: " 
print_fol_formula example004

let example005 = integer_qelim (parse "forall x. b < x ==> a <= x")
printf "example 005: " 
print_fol_formula example005

let example006 = natural_qelim (parse "forall d. exists x y. 3 * x + 5 * y = d")
printf "example 006: " 
print_fol_formula example006

let example007 = integer_qelim (parse "forall d. exists x y. 3 * x + 5 * y = d")
printf "example 007: " 
print_fol_formula example007

let example008 = natural_qelim (parse "forall d. d >= 8 ==> exists x y. 3 * x + 5 * y = d")
printf "example 008: " 
print_fol_formula example008

let example009 = natural_qelim (parse "forall d. exists x y. 3 * x - 5 * y = d")
printf "example 009: " 
print_fol_formula example009
pause ()
