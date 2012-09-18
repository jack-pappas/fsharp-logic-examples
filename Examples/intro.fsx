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
open Reasoning.Automated.Harrison.Handbook.intro

// pg. 14
// ------------------------------------------------------------------------- //
// Trivial example of using the type constructors.                           //
// ------------------------------------------------------------------------- //

// val it : expression = Add (Mul (Const 2,Var "x"),Var "y")
Add (Mul (Const 2, Var "x"), Var "y");;

// pg. 16
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val e : expression =
//   Add (Mul (Add (Mul (Const 0,Var "x"),Const 1),Const 3),Const 12)
let e = Add (Mul (Add (Mul (Const 0, Var "x"), Const 1), Const 3), Const 12);;

// val it : expression = Const 15
simplify e;;

// pg. 18
// val it : string list =
//   ["2"; "*"; "("; "("; "var_1"; "+"; "x'"; ")"; "+"; "11"; ")"]
lex (explode "2*((var_1 + x') + 11)");;

// val it : string list =
//   ["if"; "//"; "p1"; "--"; "=="; "*"; "p2"; "++"; ")"; "then"; "f"; "("; ")";
//    "else"; "g"; "("; ")"]
lex (explode "if //p1-- == *p2++) then f() else g()");;

// pg. 20
// ------------------------------------------------------------------------- //
// Our parser.                                                               //
// ------------------------------------------------------------------------- //

// val it : expression = Add (Var "x",Const 1)
default_parser "x + 1";;

// pg. 21
// ------------------------------------------------------------------------- //
// Demonstrate automatic installation.                                       //
// ------------------------------------------------------------------------- //

// <<(x1 + x2 + x3) * (1 + 2 + 3 * x + y)>>
// Note: Since F# does not support the OCaml compiler directive quotation.add
// nor does F# support quotation expander,
// the French-style <<quotation>> can not be used for automatic installation.
// Instead the input will be converted to a string and
// the parser will be set manually.

// val it : expression =
//   Mul
//     (Add (Var "x1",Add (Var "x2",Var "x3")),
//      Add (Const 1,Add (Const 2,Add (Mul (Const 3,Var "x"),Var "y"))))
default_parser "(x1 + x2 + x3) * (1 + 2 + 3 * x + y)";;

// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// val it : string = "(x + (3 * y))"
string_of_exp (default_parser "x + 3 * y");;

// TODO add fsi.AddPrinter. Need to convert add toString method to expression so that AddPrinter can recognize type

// val it : string = "x + 3 * y"
print_exp (default_parser "x + 3 * y");;

// val it : string = "(x + 3) * y"
print_exp (default_parser "(x + 3) * y");;

// val it : string = "1 + 2 + 3"
print_exp (default_parser "1 + 2 + 3");;

// val it : string = "((1 + 2) + 3) + 4"
print_exp (default_parser "((1 + 2) + 3) + 4");;

// ------------------------------------------------------------------------- //
// Example shows the problem.                                                //
// ------------------------------------------------------------------------- //

// val it : string =
//   "(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)"
print_exp (default_parser "(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) * (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)" );;