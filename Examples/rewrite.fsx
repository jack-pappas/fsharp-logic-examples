// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
//open Reasoning.Automated.Harrison.Handbook.formulas
//open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
//open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
open Reasoning.Automated.Harrison.Handbook.rewrite

//
// pg. 263
// ------------------------------------------------------------------------- //
// Example: 3 * 2 + 4 in successor notation.                                 //
// ------------------------------------------------------------------------- //

// <<|S(S(S(S(S(S(S(S(S(S(0))))))))))|>>val it : unit = ()
printert (rewrite [parse "0 + x = x";
                    parse "S(x) + y = S(x + y)";
                    parse "0 * x = 0";
                    parse "S(x) * y = y + x * y"; ]
                   (parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))"));;


