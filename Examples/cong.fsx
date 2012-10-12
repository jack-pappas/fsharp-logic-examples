// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.stal
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.cong

fsi.AddPrinter sprint_fol_formula

// pg. 253
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

ccvalid (parse
    @"f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c 
    ==> f(c) = c \/ f(g(c)) = g(f(c))");;

ccvalid (parse
    @"f(f(f(f(c)))) = c /\ f(f(c)) = c ==> f(c) = c");;

// ------------------------------------------------------------------------- //
// For debugging. Maybe I will incorporate into a prettyprinter one day.     //
// ------------------------------------------------------------------------- //

let showequiv ptn =
    let fn = reverseq (equated ptn) ptn
    List.map (apply fn) (dom fn);;