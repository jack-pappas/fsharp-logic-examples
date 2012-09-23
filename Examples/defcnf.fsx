// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

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
