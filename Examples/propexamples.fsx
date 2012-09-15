
#I @"E:\Projects\visual studio 2010\Reasoning.Automated.Harrison.Handbook\bin\Debug"
#r @"Reasoning.Automated.Harrison.Handbook.dll"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples

// pg. 63
// ------------------------------------------------------------------------- //
// Some currently tractable examples.                                        //
// ------------------------------------------------------------------------- //
//
//ramsey 3 3 4;;
//
//tautology(ramsey 3 3 5);;
//
//tautology(ramsey 3 3 6);;
//

// pg. 67
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

    // ((OUT_0 <=> (X_0 <=> ~Y_0) <=> ~C_0) /\ (C_1 <=> X_0 /\ Y_0 \/ (X_0 \/ Y_0) /\ C_0)) /\ (OUT_1 <=> (X_1 <=> ~Y_1) <=> ~C_1) /\ (C_2 <=> X_1 /\ Y_1 \/ (X_1 \/ Y_1) /\ C_1)
    // val it : unit = ()
    let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"];;
    let x = funcs.[0];;
    let y = funcs.[1];;
    let out = funcs.[2];;
    let c = funcs.[3];;
    let f = ripplecarry x y c out 2;;
    let pfn = (fun prec p -> print_propvar prec p);;
    print_formula pfn f;;
    
// pg. 72
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

    // val it : bool = true
    tautology(prime 7);;

    // val it : bool = false
    tautology(prime 9);;

    // val it : bool = true
    tautology(prime 11);;

