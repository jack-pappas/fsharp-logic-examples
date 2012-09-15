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
open Reasoning.Automated.Harrison.Handbook.defcnf

// pg. 74
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : prop formula =
//   And
//     (Or (Atom (P "p"),Or (Atom (P "q"),Atom (P "r"))),
//      And
//        (Or (Atom (P "p"),Or (Not (Atom (P "q")),Not (Atom (P "r")))),
//         And
//           (Or (Atom (P "q"),Or (Not (Atom (P "p")),Not (Atom (P "r")))),
//            Or (Atom (P "r"),Or (Not (Atom (P "p")),Not (Atom (P "q")))))))
cnf (parse_prop_formula "p <=> (q <=> r)");;

// Added by EGT
// <<(p \/ q \/ r) /\ (p \/ ~q \/ ~r) /\ (q \/ ~p \/ ~r) /\ (r \/ ~p \/ ~q)>>
// val it : unit = ()
print_prop_formula (cnf (parse_prop_formula "p <=> (q <=> r)"));;

// pg. 77
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : prop formula =
//   And
//     (Or (Atom (P "p"),Or (Atom (P "p_1"),Not (Atom (P "p_2")))),
//      And
//        (Or (Atom (P "p_1"),Or (Atom (P "r"),Not (Atom (P "q")))),
//         And
//           (Or (Atom (P "p_2"),Not (Atom (P "p"))),
//            And
//              (Or (Atom (P "p_2"),Not (Atom (P "p_1"))),
//               And
//                 (Or (Atom (P "p_2"),Not (Atom (P "p_3"))),
//                  And
//                    (Atom (P "p_3"),
//                     And
//                       (Or
//                          (Atom (P "p_3"),
//                           Or (Not (Atom (P "p_2")),Not (Atom (P "s")))),
//                        And
//                          (Or (Atom (P "q"),Not (Atom (P "p_1"))),
//                           And
//                             (Or (Atom (P "s"),Not (Atom (P "p_3"))),
//                              Or (Not (Atom (P "p_1")),Not (Atom (P "r"))))))))))))
defcnfOrig (parse_prop_formula "(p \/ (q /\ ~r)) /\ s");;

// Added by EGT
// <<(p \/ p_1 \/ ~p_2) /\
//   (p_1 \/ r \/ ~q) /\
//   (p_2 \/ ~p) /\
//   (p_2 \/ ~p_1) /\
//   (p_2 \/ ~p_3) /\
//   p_3 /\
//   (p_3 \/ ~p_2 \/ ~s) /\ (q \/ ~p_1) /\ (s \/ ~p_3) /\ (~p_1 \/ ~r)>>
// val it : unit = ()
print_prop_formula (defcnfOrig (parse_prop_formula "(p \/ (q /\ ~r)) /\ s"));;

// pg. 78
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// val it : prop formula =
//   And
//     (Or (Atom (P "p"),Atom (P "p_1")),
//      And
//        (Or (Atom (P "p_1"),Or (Atom (P "r"),Not (Atom (P "q")))),
//         And
//           (Or (Atom (P "q"),Not (Atom (P "p_1"))),
//            And (Atom (P "s"),Or (Not (Atom (P "p_1")),Not (Atom (P "r")))))))
defcnf (parse_prop_formula "(p \/ (q /\ ~r)) /\ s");;

// Added by EGT
// <<(p \/ p_1) /\ (p_1 \/ r \/ ~q) /\ (q \/ ~p_1) /\ s /\ (~p_1 \/ ~r)>>
// val it : unit = ()
print_prop_formula (defcnf (parse_prop_formula "(p \/ (q /\ ~r)) /\ s"));;
