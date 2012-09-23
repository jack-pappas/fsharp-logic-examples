// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples

// pg. 63
// ------------------------------------------------------------------------- //
// Some currently tractable examples.                                        //
// ------------------------------------------------------------------------- //

print_prop_formula ( ramsey 3 3 4 );;

tautology(ramsey 3 3 5);;

tautology(ramsey 3 3 6);;

// pg. 67
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

let [x; y; out; c] = List.map mk_index ["X"; "Y"; "OUT"; "C"];;
let pfn = (fun prec p -> print_propvar prec p);;
print_formula pfn ( ripplecarry x y c out 2 );;

// pg. 72
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

tautology(prime 7);;

tautology(prime 9);;

tautology(prime 11);;

