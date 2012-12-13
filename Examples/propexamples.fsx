// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.propexamples

fsi.AddPrinter sprint_prop_formula

// pg. 63
// ------------------------------------------------------------------------- //
// Some currently tractable examples.                                        //
// ------------------------------------------------------------------------- //

// propexamples.p001
ramsey 3 3 4;;

// propexamples.p002
tautology(ramsey 3 3 5);;

// propexamples.p003
tautology(ramsey 3 3 6);;

// pg. 67
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

let [x; y; out; c] = List.map mk_index ["X"; "Y"; "OUT"; "C"];;
// propexamples.p004
ripplecarry x y c out 2;;

// pg. 72
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// propexamples.p005
tautology(prime 7);;

// propexamples.p006
tautology(prime 9);;

// propexamples.p007
tautology(prime 11);;
