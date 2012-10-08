// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop

// pg. 29
// ------------------------------------------------------------------------- //
// Testing the parser and printer.                                           //
// ------------------------------------------------------------------------- //

let fm001 = parse_prop_formula @"p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)";;
print_prop_formula fm001;;

// pg. 30
print_prop_formula (And (fm001, fm001));;

print_prop_formula (And (Or (fm001, fm001), fm001));;

// pg. 33
false && false;;

false && true;;

true && false;;

true && true;;

// pg. 33
// ------------------------------------------------------------------------- //
// Example of use.                                                           //
// ------------------------------------------------------------------------- //

eval (parse_prop_formula @"p /\ q ==> q /\ r") <| function
    | P "p" -> true
    | P "q" -> false
    | P "r" -> true
    | _ -> failwith "Invalid property name";;

eval (parse_prop_formula @"p /\ q ==> q /\ r") <| function
    | P "p" -> true
    | P "q" -> true
    | P "r" -> false
    | _ -> failwith "Invalid property name";;

// pg. 35
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

atoms (parse_prop_formula @"p /\ q \/ s ==> ~p \/ (r <=> s)");;

// pg. 36
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

print_truthtable (parse_prop_formula @"p /\ q ==> q /\ r");;

let fm002 = parse_prop_formula @"p /\ q ==> q /\ r";;
print_prop_formula fm002;;

print_truthtable fm002;;

// pg. 39
// ------------------------------------------------------------------------- //
// Additional examples illustrating formula classes.                         //
// ------------------------------------------------------------------------- //

print_truthtable (parse_prop_formula @"((p ==> q) ==> p) ==> p");;

print_truthtable (parse_prop_formula @"p /\ ~p");;

// pg. 41
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

tautology (parse_prop_formula @"p \/ ~p");;

tautology (parse_prop_formula @"p \/ q ==> p");;

tautology (parse_prop_formula @"p \/ q ==> q \/ (p <=> q)");;

tautology (parse_prop_formula @"(p \/ q) /\ ~(p /\ q) ==> (~p <=> q)");;

// pg. 41
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

print_prop_formula (psubst ((P"p") |=> (parse_prop_formula @"p /\ q")) (parse_prop_formula @"p /\ q /\ p /\ q"));;

// pg. 43
// ------------------------------------------------------------------------- //
// Surprising tautologies including Dijkstra's "Golden rule".                //
// ------------------------------------------------------------------------- //

tautology (parse_prop_formula @"(p ==> q) \/ (q ==> p)");;

tautology (parse_prop_formula @"p \/ (q <=> r) <=> (p \/ q <=> p \/ r)");;

tautology (parse_prop_formula @"p /\ q <=> ((p <=> q) <=> p \/ q)");;

tautology (parse_prop_formula @"(p ==> q) <=> (~q ==> ~p)");;

tautology (parse_prop_formula @"(p ==> ~q) <=> (q ==> ~p)");;

tautology (parse_prop_formula @"(p ==> q) <=> (q ==> p)");;

// pg. 47
// ------------------------------------------------------------------------- //
// Some logical equivalences allowing elimination of connectives.            //
// ------------------------------------------------------------------------- //

List.forall tautology [
    parse_prop_formula @"true <=> false ==> false";
    parse_prop_formula @"~p <=> p ==> false";
    parse_prop_formula @"p /\ q <=> (p ==> q ==> false) ==> false";
    parse_prop_formula @"p \/ q <=> (p ==> false) ==> q";
    parse_prop_formula @"(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false"; ];;

// pg. 49.
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

print_prop_formula (dual (parse_prop_formula @"p \/ ~p"));;

// pg. 51
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

print_prop_formula (psimplify (parse_prop_formula @"(true ==> (x <=> false)) ==> ~(y \/ false /\ z)"));;

print_prop_formula (psimplify (parse_prop_formula @"((x ==> y) ==> true) \/ ~false"));;

// pg. 53
// ------------------------------------------------------------------------- //
// Example of NNF function in action.                                        //
// ------------------------------------------------------------------------- //

let fm003 = (parse_prop_formula (@"(p <=> q) <=> ~(r ==> s)"));;
print_prop_formula fm003;;

let fm003' = nnf fm003;;
print_prop_formula fm003';;

tautology(Iff(fm003,fm003'));;

// pg. 54
// ------------------------------------------------------------------------- //
// Some tautologies remarked on.                                             //
// ------------------------------------------------------------------------- //

tautology (parse_prop_formula (@"(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')"));;

tautology (parse_prop_formula (@"(p ==> p') /\ (q ==> q') ==> (p \/ q ==> p' \/ q')"));;

// pg. 56
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

let fm004 = (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)"));;
print_prop_formula fm004;;

print_prop_formula (dnfOrig fm004);;

print_truthtable fm004;;

print_prop_formula (dnfOrig (parse_prop_formula (@"p /\ q /\ r /\ s /\ t /\ u \/ u /\ v")));;

// pg. 58
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //
//

print_prop_formula (rawdnf (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)")));;

// pg. 58
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

purednf (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)"));;

// pg. 59
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

List.filter (non trivial) (purednf (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)")));;

// pg. 59
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

let fm005 = (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)"));;
print_prop_formula fm005;;

print_prop_formula (dnf fm005);;

tautology(Iff(fm005,dnf fm005));;

// pg. 61
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

let fm006 = (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)"));;
print_prop_formula fm006;;

print_prop_formula (cnf fm006);;

tautology(Iff(fm006,cnf fm006));;
