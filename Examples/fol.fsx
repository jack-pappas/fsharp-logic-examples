// IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
// By downloading, copying, installing or using the software you agree
// to this license.  If you do not agree to this license, do not
// download, install, copy or use the software.
// 
// Copyright (c) 2003-2007, John Harrison
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
// By downloading, copying, installing or using the software you agree
// to this license.  If you do not agree to this license, do not
// download, install, copy or use the software.
// 
// Copyright (c) 2003-2007, John Harrison
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of John Harrison may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
// USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.
//
// ===================================================================
//
// Converted to F# 2.0
//
// Copyright (c) 2012, Eric Taucher
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the previous disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the previous disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of Eric Taucher may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
//
// ===================================================================

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod

// pg. 630
// TODO: Make this work
//fsi.AddPrinter print_fol_formula

// pg. 119
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : term =
//   Fn
//     ("sqrt",
//      [Fn
//         ("-",
//          [Fn ("1",[]);
//           Fn ("cos",[Fn ("power",[Fn ("+",[Var "x"; Var "y"]); Fn ("2",[])])])])])
Fn("sqrt",[Fn("-",[Fn("1",[]);
                   Fn("cos",[Fn("power",[Fn("+",[Var "x"; Var "y"]);
                                        Fn("2",[])])])])]);;

// pg. 119
// ------------------------------------------------------------------------- //
// Trivial example of "x + y < z".                                           //
// ------------------------------------------------------------------------- //

// val it : fol formula = Atom (R ("<",[Fn ("+",[Var "x"; Var "y"]); Var "z"]))
Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"]));;

// pg. 123
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : fol formula =
//   Forall
//     ("x",
//      Forall
//        ("y",
//         Exists
//           ("x",
//            And
//              (Atom (R ("<",[Var "x"; Var "x"])),
//               Atom (R ("<",[Var "y"; Var "z"]))))))
(parse "forall x y. exists x. x < x /\ y < z")

// <<forall x y. exists x. x <x /\ y <z>>
// val it : unit = ()
print_fol_formula (parse "forall x y. exists x. x < x /\ y < z")

// Note: '|' is removed by quotexpander in OCaml version
// i.e. "|2 * x|"  become "2 * x"
//<<|2 *x|>>val it : unit = ()
printert (parset "2 * x")

// pg. 126

// val it : bool = true
holds bool_interp undefined (parse "forall x. (x = 0) \/ (x = 1)");;

// val it : bool = true
holds (mod_interp 2) undefined (parse "forall x. (x = 0) \/ (x = 1)");;

// val it : bool = false
holds (mod_interp 3) undefined (parse "forall x. (x = 0) \/ (x = 1)");;

// val fm : fol formula =
//   Forall
//     ("x",
//      Imp
//        (Not (Atom (R ("=",[Var "x"; Fn ("0",[])]))),
//         Exists ("y",Atom (R ("=",[Fn ("*",[Var "x"; Var "y"]); Fn ("1",[])])))))
let fm = (parse "forall x. ~(x = 0) ==> exists y. x * y = 1");;

// val it : int list = [1; 2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43]
List.filter (fun n -> holds (mod_interp n) undefined fm) (1--45);;

// pg. 129
// val it : bool = true
holds (mod_interp 3) undefined (parse "(forall x. x = 0) ==> 1 = 0");;

// val it : bool = false
holds (mod_interp 3) undefined (parse "forall x. x = 0 ==> 1 = 0");;

// pg. ???
// ------------------------------------------------------------------------- //
// Examples in the main text.                                                //
// ------------------------------------------------------------------------- //

// TODO: What was this for?
(parse "forall x y. exists z. x < z /\ y < z");;

// TODO: What was this for?
(parse "~(forall x. P(x)) <=> exists y. ~P(y)");;

// pg. 133
// ------------------------------------------------------------------------- //
// Variant function and examples.                                            //
// ------------------------------------------------------------------------- //

// val it : string = "x"
variant "x" ["y"; "z"];;

// val it : string = "x"
variant "x" ["x"; "y"];;

// val it : string = "x"
variant "x" ["x"; "x'"];;

// pg. 134
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// <<forall x'. x' =x>>
// val it : unit = ()
print_fol_formula (subst ("y" |=> Var "x") (parse "forall x. x = y"));;

// <<forall x' x''. x' =x ==> x' =x''>>
print_fol_formula (subst ("y" |=> Var "x") (parse "forall x x'. x = y ==> x = x'"));;


