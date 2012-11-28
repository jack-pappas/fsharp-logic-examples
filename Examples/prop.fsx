// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop

fsi.AddPrinter sprint_prop_formula

// pg. 29
// ------------------------------------------------------------------------- //
// Testing the parser and printer.                                           //
// ------------------------------------------------------------------------- //

let fm001 = parse_prop_formula @"p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)";;

// pg. 30
// prop.p001
And (fm001, fm001);;

// prop.p002
And (Or (fm001, fm001), fm001);;

// pg. 33
// prop.p003
false && false;;

// prop.p004
false && true;;

// prop.p005
true && false;;

// prop.p006
true && true;;

// pg. 33
// ------------------------------------------------------------------------- //
// Example of use.                                                           //
// ------------------------------------------------------------------------- //

// prop.p007
// Harrison #01
eval (parse_prop_formula @"p /\ q ==> q /\ r") <| function
    | P "p" -> true
    | P "q" -> false
    | P "r" -> true
    | _ -> failwith "Invalid property name";;

// prop.p008
// Harrison #01
eval (parse_prop_formula @"p /\ q ==> q /\ r") <| function
    | P "p" -> true
    | P "q" -> true
    | P "r" -> false
    | _ -> failwith "Invalid property name";;

// pg. 35
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// prop.p009
atoms (parse_prop_formula @"p /\ q \/ s ==> ~p \/ (r <=> s)");;

// pg. 36
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// prop.p010
// Harrison #01
print_truthtable (parse_prop_formula @"p /\ q ==> q /\ r");;

// prop.p011
// Harrison #01
let fm002 = parse_prop_formula @"p /\ q ==> q /\ r";;
print_truthtable fm002;;

// pg. 39
// ------------------------------------------------------------------------- //
// Additional examples illustrating formula classes.                         //
// ------------------------------------------------------------------------- //

// prop.p012
// Pelletier #08
print_truthtable (parse_prop_formula @"((p ==> q) ==> p) ==> p");;

// prop.p013
print_truthtable (parse_prop_formula @"p /\ ~p");;

// pg. 41
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// prop.p014
// Pelletier #06
tautology (parse_prop_formula @"p \/ ~p");;

// prop.p015
tautology (parse_prop_formula @"p \/ q ==> p");;

// prop.p016
tautology (parse_prop_formula @"p \/ q ==> q \/ (p <=> q)");;

// prop.p017
tautology (parse_prop_formula @"(p \/ q) /\ ~(p /\ q) ==> (~p <=> q)");;

// pg. 41
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// prop.p018
(psubst ((P"p") |=> (parse_prop_formula @"p /\ q")) (parse_prop_formula @"p /\ q /\ p /\ q"));;

// pg. 43
// ------------------------------------------------------------------------- //
// Surprising tautologies including Dijkstra's "Golden rule".                //
// ------------------------------------------------------------------------- //

// prop.p019
// Pelletier #16
tautology (parse_prop_formula @"(p ==> q) \/ (q ==> p)");;

// prop.p020
tautology (parse_prop_formula @"p \/ (q <=> r) <=> (p \/ q <=> p \/ r)");;

// prop.p021
// Harrison #02 - Equations within equations
tautology (parse_prop_formula @"p /\ q <=> ((p <=> q) <=> p \/ q)");;

// prop.p022
// Harrison #03 - Equations within equations
tautology (parse_prop_formula @"(p ==> q) <=> (~q ==> ~p)");;

// prop.p023
tautology (parse_prop_formula @"(p ==> ~q) <=> (q ==> ~p)");;

// prop.p024
tautology (parse_prop_formula @"(p ==> q) <=> (q ==> p)");;

// pg. 47
// ------------------------------------------------------------------------- //
// Some logical equivalences allowing elimination of connectives.            //
// ------------------------------------------------------------------------- //

// prop.p025
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

// prop.p026
// Pelletier #06
dual (parse_prop_formula @"p \/ ~p");;

// pg. 51
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// prop.p027
psimplify (parse_prop_formula @"(true ==> (x <=> false)) ==> ~(y \/ false /\ z)");;

// prop.p028
psimplify (parse_prop_formula @"((x ==> y) ==> true) \/ ~false");;

// pg. 53
// ------------------------------------------------------------------------- //
// Example of NNF function in action.                                        //
// ------------------------------------------------------------------------- //

let fm003 = parse_prop_formula (@"(p <=> q) <=> ~(r ==> s)");;

let fm003' = nnf fm003;;

// prop.p029
tautology(Iff(fm003,fm003'));;

// pg. 54
// ------------------------------------------------------------------------- //
// Some tautologies remarked on.                                             //
// ------------------------------------------------------------------------- //

// prop.p030
tautology (parse_prop_formula (@"(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')"));;

// prop.p031
tautology (parse_prop_formula (@"(p ==> p') /\ (q ==> q') ==> (p \/ q ==> p' \/ q')"));;

// pg. 56
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// Harrison #04 - dnf
let fm004 = parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)");;

// prop.p032
dnfOrig fm004;;

// prop.p033
print_truthtable fm004;;

// prop.p034
dnfOrig (parse_prop_formula (@"p /\ q /\ r /\ s /\ t /\ u \/ u /\ v"));;

// pg. 58
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //
//

// prop.p035
// Harrison #04 - dnf
rawdnf (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)"));;

// pg. 58
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// prop.p036
// Harrison #04 - dnf
purednf (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)"));;

// pg. 59
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// prop.p037
// Harrison #04 - dnf
List.filter (non trivial) (purednf (parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)")));;

// pg. 59
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// Harrison #04 - dnf
let fm005 = parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)");;

// prop.p038
dnf fm005;;

// prop.p039
tautology(Iff(fm005,dnf fm005));;

// pg. 61
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// Harrison #04 - dnf
let fm006 = parse_prop_formula (@"(p \/ q /\ r) /\ (~p \/ ~r)");;

// prop.p040
cnf fm006;;

// prop.p041
tautology(Iff(fm006,cnf fm006));;
