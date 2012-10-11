// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.stal
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.cong

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