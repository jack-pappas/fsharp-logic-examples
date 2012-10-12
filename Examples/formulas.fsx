// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas

// pg. 28
// val it :
//   ((string list -> string list -> 'a formula * string list) *
//    (string list -> string list -> 'a formula * string list) -> string list ->
//      string list -> 'a formula * string list) = <fun:clo@14-1>
parse_formula;;

// val it : (int -> 'a formula -> unit) = <fun:clo@16-5>
print_qformula;;

