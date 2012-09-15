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
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop

// pg. 29
// ------------------------------------------------------------------------- //
// Testing the parser and printer.                                           //
// ------------------------------------------------------------------------- //

// <<p\/q==>r>>val it : unit = ()
print_prop_formula (parse_prop_formula "p \/ q ==> r");;

// val fmString : string = "p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)"
let fmString = "p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)";;

// val fm : prop formula =
//   Iff
//     (Imp (Atom (P "p"),Atom (P "q")),
//      Or
//        (And (Atom (P "r"),Atom (P "s")),
//         Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v")))))
let fm = parse_prop_formula fmString;;

// <<p==>q<=>r/\s\/(t<=>~(~u)/\v)>>val it : unit = ()
print_prop_formula (parse_prop_formula fmString);;

// pg. 30
// val it : prop formula =
//   And
//     (Iff
//        (Imp (Atom (P "p"),Atom (P "q")),
//         Or
//           (And (Atom (P "r"),Atom (P "s")),
//            Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v"))))),
//      Iff
//        (Imp (Atom (P "p"),Atom (P "q")),
//         Or
//           (And (Atom (P "r"),Atom (P "s")),
//            Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v"))))))
And(fm,fm);;

// val it : prop formula =
//   And
//     (Or
//        (Iff
//           (Imp (Atom (P "p"),Atom (P "q")),
//            Or
//              (And (Atom (P "r"),Atom (P "s")),
//               Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v"))))),
//         Iff
//           (Imp (Atom (P "p"),Atom (P "q")),
//            Or
//              (And (Atom (P "r"),Atom (P "s")),
//               Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v")))))),
//      Iff
//        (Imp (Atom (P "p"),Atom (P "q")),
//         Or
//           (And (Atom (P "r"),Atom (P "s")),
//            Iff (Atom (P "t"),And (Not (Not (Atom (P "u"))),Atom (P "v"))))))
And(Or(fm,fm),fm);;

// pg. 33

// val it : bool = false
false && false;;

// val it : bool = false
false && true;;

// val it : bool = false
true && false;;

// val it : bool = true
true && true;;

// pg. 33
// ------------------------------------------------------------------------- //
// Example of use.                                                           //
// ------------------------------------------------------------------------- //

// Note: function is a simplified form of match

// val it : bool = true
eval (parse_prop_formula "p /\ q ==> q /\ r") (function | P"p" -> true | P"q" -> false | P"r" -> true | _ -> failwith "Invalid property name");;

// val it : bool = false
eval (parse_prop_formula "p /\ q ==> q /\ r") (function | P"p" -> true | P"q" -> true | P"r" -> false | _ -> failwith "Invalid property name");;

// pg. 35
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : prop list = [P "p"; P "q"; P "r"; P "s"]
atoms (parse_prop_formula "p /\ q \/ s ==> ~p \/ (r <=> s)");;

// pg. 36
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// p     q     r     | formula
// ---------------------------
// false false false | true  
// false false true  | true  
// false true  false | true  
// false true  true  | true  
// true  false false | true  
// true  false true  | true  
// true  true  false | false 
// true  true  true  | true  
// ---------------------------
// 
// val it : unit = ()
print_truthtable (parse_prop_formula "p /\ q ==> q /\ r");;

// Note: Need to change name from fm to fm2 to avoid duplicate defimintion error
// val fm2 : prop formula =
//   Imp (And (Atom (P "p"),Atom (P "q")),And (Atom (P "q"),Atom (P "r")))
let fm2 = parse_prop_formula "p /\ q ==> q /\ r";;

// p     q     r     | formula
// ---------------------------
// false false false | true  
// false false true  | true  
// false true  false | true  
// false true  true  | true  
// true  false false | true  
// true  false true  | true  
// true  true  false | false 
// true  true  true  | true  
// ---------------------------
//
// val it : unit = ()
print_truthtable fm2;;

// pg. 39
// ------------------------------------------------------------------------- //
// Additional examples illustrating formula classes.                         //
// ------------------------------------------------------------------------- //

// p     q     | formula
// ---------------------
// false false | true  
// false true  | true  
// true  false | true  
// true  true  | true  
// ---------------------
// 
// val it : unit = ()
print_truthtable (parse_prop_formula "((p ==> q) ==> p) ==> p");;

// p     | formula
// ---------------
// false | false 
// true  | false 
// ---------------
// 
// val it : unit = ()
print_truthtable (parse_prop_formula "p /\ ~p");;

// pg. 41
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// val it : bool = true
tautology (parse_prop_formula "p \/ ~p");;

// val it : bool = false
tautology (parse_prop_formula "p \/ q ==> p");;

// val it : bool = false
tautology (parse_prop_formula "p \/ q ==> q \/ (p <=> q)");;

// val it : bool = true
tautology (parse_prop_formula "(p \/ q) /\ ~(p /\ q) ==> (~p <=> q)");;

// pg. 41
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

let f1 = (parse_prop_formula "p /\ q");;
// val f1 : prop formula = And (Atom (P "p"),Atom (P "q"))

print_truthtable f1;;
// p     q     | formula
// ---------------------
// false false | false 
// false true  | false 
// true  false | false 
// true  true  | true  
// ---------------------
//
// val it : unit = ()

let f2 = (parse_prop_formula "p /\ q /\ p /\ q");;
// val f2 : prop formula =
//   And (Atom (P "p"),And (Atom (P "q"),And (Atom (P "p"),Atom (P "q"))))

print_truthtable f2;;
// p     q     | formula
// ---------------------
// false false | false 
// false true  | false 
// true  false | false 
// true  true  | true  
// ---------------------
//
// val it : unit = ()

let f3 = (P"p");;
// val f3 : prop = P "p"

//let f4 = (P"p") (|=>) f1 f2;;

//psubst ((P"p") |=> f1 f2);;

// TODO: Figure out why this does not work
//psubst ((P"p") |=> (parse_prop_formula "p /\ q")) (parse_prop_formula "p /\ q /\ p /\ q");;

// pg. 43
// ------------------------------------------------------------------------- //
// Surprising tautologies including Dijkstra's "Golden rule".                //
// ------------------------------------------------------------------------- //

// val it : bool = true
tautology (parse_prop_formula "(p ==> q) \/ (q ==> p)");;

// val it : bool = true
tautology (parse_prop_formula "p \/ (q <=> r) <=> (p \/ q <=> p \/ r)");;

// val it : bool = true
tautology (parse_prop_formula "p /\ q <=> ((p <=> q) <=> p \/ q)");;

// val it : bool = true
tautology (parse_prop_formula "(p ==> q) <=> (~q ==> ~p)");;

// val it : bool = true
tautology (parse_prop_formula "(p ==> ~q) <=> (q ==> ~p)");;

// val it : bool = true
tautology (parse_prop_formula "(p ==> q) <=> (q ==> p)");;

// pg. 47
// ------------------------------------------------------------------------- //
// Some logical equivalences allowing elimination of connectives.            //
// ------------------------------------------------------------------------- //

// val it : bool = true
List.forall tautology
    [(parse_prop_formula "true <=> false ==> false");
    (parse_prop_formula "~p <=> p ==> false");
    (parse_prop_formula "p /\ q <=> (p ==> q ==> false) ==> false");
    (parse_prop_formula "p \/ q <=> (p ==> false) ==> q");
    (parse_prop_formula "(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false")];;


// pg. 49.
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : prop formula = And (Atom (P "p"),Not (Atom (P "p")))
dual (parse_prop_formula ("p \/ ~p"));;

// pg. 51
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : prop formula = Imp (Not (Atom (P "x")),Not (Atom (P "y")))
psimplify (parse_prop_formula ("(true ==> (x <=> false)) ==> ~(y \/ false /\ z)"));;

// val it : prop formula = True
psimplify (parse_prop_formula ("((x ==> y) ==> true) \/ ~false"));;

// pg. 53
// ------------------------------------------------------------------------- //
// Example of NNF function in action.                                        //
// ------------------------------------------------------------------------- //

// Note: Changed named from fm to fm1 to avoid F# compiiler error
// val fm1 : prop formula =
//   Iff (Iff (Atom (P "p"),Atom (P "q")),Not (Imp (Atom (P "r"),Atom (P "s"))))
let fm1 = (parse_prop_formula ("(p <=> q) <=> ~(r ==> s)"));;

// Note: Changed named from fm' to fm1' to avoid F# compiiler error
// val fm1' : prop formula =
//   Or
//     (And
//        (Or
//           (And (Atom (P "p"),Atom (P "q")),
//            And (Not (Atom (P "p")),Not (Atom (P "q")))),
//         And (Atom (P "r"),Not (Atom (P "s")))),
//      And
//        (Or
//           (And (Atom (P "p"),Not (Atom (P "q"))),
//            And (Not (Atom (P "p")),Atom (P "q"))),
//         Or (Not (Atom (P "r")),Atom (P "s"))))
let fm1' = nnf fm1;;

// val it : bool = true
tautology(Iff(fm1,fm1'));;

// pg. 54
// ------------------------------------------------------------------------- //
// Some tautologies remarked on.                                             //
// ------------------------------------------------------------------------- //

// val it : bool = true
tautology (parse_prop_formula ("(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')"));;

// val it : bool = true
tautology (parse_prop_formula ("(p ==> p') /\ (q ==> q') ==> (p \/ q ==> p' \/ q')"));;

// pg. 56
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //


// Note: Changed named from fm to fm3 to avoid F# compiiler error
// val fm3 : prop formula =
//   And
//     (Or (Atom (P "p"),And (Atom (P "q"),Atom (P "r"))),
//      Or (Not (Atom (P "p")),Not (Atom (P "r"))))
let fm3 = (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)"));;

// val it : prop formula =
//   Or
//     (And (Not (Atom (P "p")),And (Atom (P "q"),Atom (P "r"))),
//      Or
//        (And (Atom (P "p"),And (Not (Atom (P "q")),Not (Atom (P "r")))),
//         And (Atom (P "p"),And (Atom (P "q"),Not (Atom (P "r"))))))
dnfOrig fm3;;

// p     q     r     | formula
// ---------------------------
// false false false | false 
// false false true  | false 
// false true  false | false 
// false true  true  | true  
// true  false false | true  
// true  false true  | false 
// true  true  false | true  
// true  true  true  | false 
// ---------------------------
//
// val it : unit = ()
print_truthtable fm3;;

// Output not show because it is so long.
dnfOrig (parse_prop_formula ("p /\ q /\ r /\ s /\ t /\ u \/ u /\ v"));;

// pg. 58
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //
//

// val it : prop formula =
//   Or
//     (Or
//        (And (Atom (P "p"),Not (Atom (P "p"))),
//         And (And (Atom (P "q"),Atom (P "r")),Not (Atom (P "p")))),
//      Or
//        (And (Atom (P "p"),Not (Atom (P "r"))),
//         And (And (Atom (P "q"),Atom (P "r")),Not (Atom (P "r")))))
rawdnf (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)"));;

// Added by EGT
// <<(p /\ ~p \/ (q /\ r) /\ ~p) \/ p /\ ~r \/ (q /\ r) /\ ~r>>
// val it : unit = ()
print_prop_formula (rawdnf (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)")));;

// pg. 58
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : prop formula list list =
//   [[Atom (P "p"); Not (Atom (P "p"))]; [Atom (P "p"); Not (Atom (P "r"))];
//    [Atom (P "q"); Atom (P "r"); Not (Atom (P "p"))];
//    [Atom (P "q"); Atom (P "r"); Not (Atom (P "r"))]]
purednf (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)"));;

// TODO: Make this work if reasonable to do so.
//print_prop_formula (purednf (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)")));;

// pg. 59
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : prop formula list list =
//   [[Atom (P "p"); Not (Atom (P "r"))];
//    [Atom (P "q"); Atom (P "r"); Not (Atom (P "p"))]]
List.filter (non trivial) (purednf (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)")));;

// TODO: Make this work if reasonable to do so.
//print_prop_formula (List.filter (non trivial) (purednf (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)"))));;

// pg. 59
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //
//

// Note: Changed named from fm to fm4 to avoid F# compiiler error
// val fm4 : prop formula =
//   And
//     (Or (Atom (P "p"),And (Atom (P "q"),Atom (P "r"))),
//      Or (Not (Atom (P "p")),Not (Atom (P "r"))))
let fm4 = (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)"));;

// val it : prop formula =
//   Or
//     (And (Not (Atom (P "p")),And (Atom (P "q"),Atom (P "r"))),
//      Or
//        (And (Atom (P "p"),And (Not (Atom (P "q")),Not (Atom (P "r")))),
//         And (Atom (P "p"),And (Atom (P "q"),Not (Atom (P "r"))))))
dnf fm4;;

// Added by EGT
// <<p /\ ~r \/ q /\ r /\ ~p>>
// val it : unit = ()
print_prop_formula (dnf fm4);;

// val it : bool = true
tautology(Iff(fm4,dnf fm4));;

// pg. 61
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// Note: Changed named from fm to fm5 to avoid F# compiiler error
// val fm5 : prop formula =
//   And
//     (Or (Atom (P "p"),And (Atom (P "q"),Atom (P "r"))),
//      Or (Not (Atom (P "p")),Not (Atom (P "r"))))
let fm5 = (parse_prop_formula ("(p \/ q /\ r) /\ (~p \/ ~r)"));;

// val fm5 : prop formula =
//   And
//     (Or (Atom (P "p"),And (Atom (P "q"),Atom (P "r"))),
//      Or (Not (Atom (P "p")),Not (Atom (P "r"))))
cnf fm5;;

// Added by EGT
// <<(p \/ q) /\ (p \/ r) /\ (~p \/ ~r)>>
// val it : unit = ()
print_prop_formula (cnf fm5);;

// val it : bool = true
tautology(Iff(fm5,cnf fm5));;
