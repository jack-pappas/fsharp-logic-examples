// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib

// pg. 621

let smallsqs = fpf [1;2;3] [1;4;9];;

graph smallsqs;;

graph (undefine 2 smallsqs);;

graph ((3 |-> 0) smallsqs);;

apply smallsqs 3;;