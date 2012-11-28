// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol

// pg. 119
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// fol.p001
Fn("sqrt",[Fn("-",[Fn("1",[]);
                   Fn("power",[Fn("cos",[Fn("+",[Var "x"; Var "y"])]);
                               Fn("2",[])])])]);; // From errata

// pg. 119
// ------------------------------------------------------------------------- //
// Trivial example of "x + y < z".                                           //
// ------------------------------------------------------------------------- //

// fol.p002
Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"]));;

// Not in book
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// fol.p003
// TODO: Why does this fail to parse?
//parse @"forall x. x < 2 ==> 2 * x <= 3) \/ false";;

// fol.p004
parset ("2 * x");;

fsi.AddPrinter sprint_term
fsi.AddPrinter sprint_fol_formula

// pg. 123
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// fol.p005
(parse @"forall x y. exists z. x < z /\ y < z");;

// fol.p006
(parse @"~(forall x. P(x)) <=> exists y. ~P(y)");;

// pg. 126
// fol.p007
// Harrison #06 
holds bool_interp undefined (parse @"forall x. (x = 0) \/ (x = 1)");;

// fol.p008
// Harrison #06 
holds (mod_interp 2) undefined (parse @"forall x. (x = 0) \/ (x = 1)");;

// fol.p009
// Harrison #06 
holds (mod_interp 3) undefined (parse @"forall x. (x = 0) \/ (x = 1)");;

let fm = (parse @"forall x. ~(x = 0) ==> exists y. x * y = 1");;

// fol.p010
List.filter (fun n -> holds (mod_interp n) undefined fm) (1--45);;

// pg. 129
// fol.p011
holds (mod_interp 3) undefined (parse @"(forall x. x = 0) ==> 1 = 0");;

// fol.p012
holds (mod_interp 3) undefined (parse @"forall x. x = 0 ==> 1 = 0");;

// pg. 133
// ------------------------------------------------------------------------- //
// Variant function and examples.                                            //
// ------------------------------------------------------------------------- //

// fol.p013
variant "x" ["y"; "z"];;

// fol.p014
variant "x" ["x"; "y"];;

// fol.p015
variant "x" ["x"; "x'"];;

// pg. 134
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// fol.p016
(subst ("y" |=> Var "x") (parse @"forall x. x = y"));;

// fol.p017
(subst ("y" |=> Var "x") (parse @"forall x x'. x = y ==> x = x'"));;
