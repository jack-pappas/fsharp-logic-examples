// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.fol

fsi.AddPrinter sprint_fol_formula

// pg. 119
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

Fn("sqrt",[Fn("-",[Fn("1",[]);
                   Fn("cos",[Fn("power",[Fn("+",[Var "x"; Var "y"]);
                                        Fn("2",[])])])])]);;

// pg. 119
// ------------------------------------------------------------------------- //
// Trivial example of "x + y < z".                                           //
// ------------------------------------------------------------------------- //

Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"]));;

// pg. 123
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

(parse @"forall x y. exists z. x < z /\ y < z");;

(parse @"~(forall x. P(x)) <=> exists y. ~P(y)");;

// pg. 126

holds bool_interp undefined (parse @"forall x. (x = 0) \/ (x = 1)");;

holds (mod_interp 2) undefined (parse @"forall x. (x = 0) \/ (x = 1)");;

holds (mod_interp 3) undefined (parse @"forall x. (x = 0) \/ (x = 1)");;

let fm = (parse @"forall x. ~(x = 0) ==> exists y. x * y = 1");;

List.filter (fun n -> holds (mod_interp n) undefined fm) (1--45);;

// pg. 129
holds (mod_interp 3) undefined (parse @"(forall x. x = 0) ==> 1 = 0");;

holds (mod_interp 3) undefined (parse @"forall x. x = 0 ==> 1 = 0");;

// pg. 133
// ------------------------------------------------------------------------- //
// Variant function and examples.                                            //
// ------------------------------------------------------------------------- //

variant "x" ["y"; "z"];;

variant "x" ["x"; "y"];;

variant "x" ["x"; "x'"];;

// pg. 134
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

(subst ("y" |=> Var "x") (parse @"forall x. x = y"));;

(subst ("y" |=> Var "x") (parse @"forall x x'. x = y ==> x = x'"));;
