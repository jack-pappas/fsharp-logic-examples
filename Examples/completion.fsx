// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.rewrite
open Reasoning.Automated.Harrison.Handbook.order
open Reasoning.Automated.Harrison.Handbook.completion

fsi.AddPrinter sprint_term
fsi.AddPrinter sprint_fol_formula

// pg. 277
// ------------------------------------------------------------------------- //
// Simple example.                                                           //
// ------------------------------------------------------------------------- //

let eq = (parse @"f(f(x)) = g(x)");;
critical_pairs eq eq;;
  
// pg. 280
// ------------------------------------------------------------------------- //
// A simple "manual" example, before considering packaging and refinements.  //
// ------------------------------------------------------------------------- //

let eqs =
    [parse @"1 * x = x";
    parse @"i(x) * x = 1";
    parse @"(x * y) * z = x * y * z"; ];;

let ord = lpo_ge (weight ["1"; "*"; "i"]);;
// Real: 00:00:32.964, CPU: 00:00:32.937, GC gen0: 165, gen1: 4, gen2: 0
let eqs' = complete ord (eqs, [], unions (allpairs critical_pairs eqs eqs));;

// Real: 00:00:00.017, CPU: 00:00:00.015, GC gen0: 0, gen1: 0, gen2: 0
rewrite eqs' (parset @"i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))");;

// pg. 283
// ------------------------------------------------------------------------- //
// This does indeed help a lot.                                              //
// ------------------------------------------------------------------------- //

interreduce [] eqs';;

// pg. 284
// ------------------------------------------------------------------------- //
// Inverse property (K&B example 4).                                         //
// ------------------------------------------------------------------------- //

complete_and_simplify ["1"; "*"; "i"] [parse @"i(a) * (a * b) = b"];;
  
// pg. 284
// ------------------------------------------------------------------------- //
// Auxiliary result used to justify extension of language for cancellation.  //
// ------------------------------------------------------------------------- //

(meson002 << equalitize) (parse @"
    (forall x y z. x * y = x * z ==> y = z) <=> 
    (forall x z. exists w. forall y. z = x * y ==> w = y)");;

skolemize (parse @"
    forall x z. exists w. forall y. z = x * y ==> w = y");;

// Not in book
// ------------------------------------------------------------------------- //
// The commutativity example (of course it fails...).                        //
// ------------------------------------------------------------------------- //

// long running
//complete_and_simplify ["1"; "*"; "i"]
//    [parse @"(x * y) * z = x * (y * z)";
//    parse @"1 * x = x"; parse @"x * 1 = x"; parse @"x * x = 1"]

// Not in book
// ------------------------------------------------------------------------- //
// Central groupoids (K&B example 6).                                        //
// ------------------------------------------------------------------------- //

let eqs001 =  [parse @"(a * b) * (b * c) = b"];;
complete_and_simplify ["*"] eqs001;;

// ------------------------------------------------------------------------- //
// (l,r)-systems (K&B example 12).                                           //
// ------------------------------------------------------------------------- //

let eqs002 =
    [(parse @"(x * y) * z = x * y * z"); 
    (parse @"1 * x = x"); 
    (parse @"x * i(x) = 1")];;
// long running but will finish.
// Real: 02:37:35.586, CPU: 02:37:31.718, GC gen0: 50200, gen1: 1376, gen2: 98
complete_and_simplify ["1"; "*"; "i"] eqs002;;

// ------------------------------------------------------------------------- //
// Auxiliary result used to justify extension for example 9.                 //
// ------------------------------------------------------------------------- //

(meson002 << equalitize) (parse @"
    (forall x y z. x * y = x * z ==> y = z) <=> (forall x z. exists w. forall y. z = x * y ==> w = y)");;

skolemize (parse @"
    forall x z. exists w. forall y. z = x * y ==> w = y");;

let eqs003 =
    [parse @"f(a,a*b) = b";
    parse @"g(a*b,b) = a";
    parse @"1 * a = a";
    parse @"a * 1 = a"; ];;
complete_and_simplify ["1"; "*"; "f"; "g"] eqs003;;

// ------------------------------------------------------------------------- //
// K&B example 7, where we need to divide through.                           //
// ------------------------------------------------------------------------- //

let eqs004 =  [(parse @"f(a,f(b,c,a),d) = c")];;

//********** Can't orient
//complete_and_simplify ["f"] eqs004;;

let eqs005 =
    [parse @"f(a,f(b,c,a),d) = c";
    parse @"f(a,b,c) = g(a,b)";
    parse @"g(a,b) = h(b)"; ];;
complete_and_simplify ["h"; "g"; "f"] eqs005;;

// ------------------------------------------------------------------------- //
// Other examples not in the book, mostly from K&B                           //
// ------------------------------------------------------------------------- //

// ------------------------------------------------------------------------- //
// Group theory I (K & B example 1).                                         //
// ------------------------------------------------------------------------- //

let eqs006 =
    [parse @"1 * x = x";
    parse @"i(x) * x = 1";
    parse @"(x * y) * z = x * y * z"; ];;
// Real: 00:00:31.855, CPU: 00:00:31.843, GC gen0: 168, gen1: 4, gen2: 0
complete_and_simplify ["1"; "*"; "i"] eqs006;;

// ------------------------------------------------------------------------- //
// However, with the rules in a different order, things take longer.         //
// At least we don't need to defer any critical pairs...                     //
// ------------------------------------------------------------------------- //

let eqs007 =
    [parse @"(x * y) * z = x * y * z";
    parse @"1 * x = x";
    parse @"i(x) * x = 1"; ];;
// Real: 00:00:34.519, CPU: 00:00:34.453, GC gen0: 181, gen1: 4, gen2: 0
complete_and_simplify ["1"; "*"; "i"] eqs007;;

// ------------------------------------------------------------------------- //
// Example 2: if we orient i(x) * i(y) -> i(x * y), things diverge.          //
// ------------------------------------------------------------------------- //

let eqs008 =
    [(parse @"1 * x = x"); 
    (parse @"i(x) * x = 1"); 
    (parse @"(x * y) * z = x * y * z")];;

// long running
//complete_and_simplify ["1"; "i"; "*"] eqs008;;

// ------------------------------------------------------------------------- //
// Group theory III, with right inverse and identity (K&B example 3).        //
// ------------------------------------------------------------------------- //

let eqs009 =
    [parse @"(x * y) * z = x * y * z";
    parse @"x * 1 = x";
    parse @"x * i(x) = 1"; ];;

// long running
//complete_and_simplify ["1"; "*"; "i"] eqs009;;

// ------------------------------------------------------------------------- //
// Inverse property (K&B example 4).                                         //
// ------------------------------------------------------------------------- //

let eqs010 = [parse @"i(a) * (a * b) = b"];;
complete_and_simplify ["1"; "*"; "i"] eqs010;;

let eqs011 = [parse @"a * (i(a) * b) = b"];;
complete_and_simplify ["1"; "*"; "i"] eqs011;;

// ------------------------------------------------------------------------- //
// Group theory IV (K&B example 5).                                          //
// ------------------------------------------------------------------------- //

let eqs012 =
    [parse @"(x * y) * z = x * y * z";
    parse @"1 * x = x";
    parse @"11 * x = x";
    parse @"i(x) * x = 1";
    parse @"j(x) * x = 11"; ];;

// Real: 00:02:21.755, CPU: 00:02:21.656, GC gen0: 718, gen1: 15, gen2: 2
complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs012;;

// ------------------------------------------------------------------------- //
// Central groupoids (K&B example 6).                                        //
// ------------------------------------------------------------------------- //

let eqs013 = [parse @"(a * b) * (b * c) = b"];;
complete_and_simplify ["*"] eqs013;;

// ------------------------------------------------------------------------- //
// Random axiom (K&B example 7).                                             //
// ------------------------------------------------------------------------- //

let eqs014 = [(parse @"f(a,f(b,c,a),d) = c")];;

// Can't orient
//complete_and_simplify ["f"] eqs014;;

let eqs015 =  [
    parse @"f(a,f(b,c,a),d) = c";
    parse @"f(a,b,c) = g(a,b)";
    parse @"g(a,b) = h(b)"; ];;
complete_and_simplify ["h"; "g"; "f"] eqs015;;

// ------------------------------------------------------------------------- //
// Another random axiom (K&B example 8).                                     //
// ------------------------------------------------------------------------- //

let eqs016 =  [(parse @"(a * b) * (c * b * a) = b")];;

// Can't orient
//complete_and_simplify ["*"] eqs016;;

// ------------------------------------------------------------------------- //
// The cancellation law (K&B example 9).                                     //
// ------------------------------------------------------------------------- //

let eqs017 =
    [parse @"f(a,a*b) = b";
    parse @"g(a*b,b) = a"; ];;

complete_and_simplify ["*"; "f"; "g"] eqs017;;

let eqs018 =
    [parse @"f(a,a*b) = b";
    parse @"g(a*b,b) = a";
    parse @"1 * a = a";
    parse @"a * 1 = a"; ];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs018;;

//*** Just for fun; these aren't tried by Knuth and Bendix

let eqs019 =
    [(parse @"(x * y) * z = x * y * z"); 
    (parse @"f(a,a*b) = b"); 
    (parse @"g(a*b,b) = a"); 
    (parse @"1 * a = a"); 
    (parse @"a * 1 = a")];;

// long running
//complete_and_simplify ["1"; "*"; "f"; "g"] eqs019;;

let eqs020 = [(parse @"(x * y) * z = x * y * z"); (parse @"f(a,a*b) = b"); (parse @"g(a*b,b) = a")];;

// long running
//complete_and_simplify ["*"; "f"; "g"] eqs020;;
// long running
//complete_and_simplify ["f"; "g"; "*"] eqs020;;

// ------------------------------------------------------------------------- //
// Loops (K&B example 10).                                                   //
// ------------------------------------------------------------------------- //

let eqs021 =
    [parse @"a * \(a,b) = b";
    parse @"/(a,b) * b = a";
    parse @"1 * a = a";
    parse @"a * 1 = a"; ];;

complete_and_simplify ["1"; "*"; "\\"; "/"] eqs021;;

let eqs022 =
    [parse @"a * \(a,b) = b";
    parse @"/(a,b) * b = a";
    parse @"1 * a = a";
    parse @"a * 1 = a";
    parse @"f(a,a*b) = b";
    parse @"g(a*b,b) = a"; ];;

complete_and_simplify ["1"; "*"; "\\"; "/"; "f"; "g"] eqs022;;

// ------------------------------------------------------------------------- //
// Another variant of groups (K&B example 11).                               //
// ------------------------------------------------------------------------- //

let eqs023 =
    [(parse @"(x * y) * z = x * y * z");
    (parse @"1 * 1 = 1");
    (parse @"a * i(a) = 1");
    (parse @"f(1,a,b) = a");
    (parse @"f(a*b,a,b) = g(a*b,b)")];;

//******* this is not expected to terminate
//complete_and_simplify ["1"; "g"; "f"; "*"; "i"] eqs023;;

// ------------------------------------------------------------------------- //
// (l,r)-systems (K&B example 12).                                           //
// ------------------------------------------------------------------------- //

let eqs024 =
    [(parse @"(x * y) * z = x * y * z"); 
    (parse @"1 * x = x"); 
    (parse @"x * i(x) = 1")];;

//******* This works, but takes a long time
//complete_and_simplify ["1"; "*"; "i"] eqs024;;

// ------------------------------------------------------------------------- //
// (r,l)-systems (K&B example 13).                                           //
// ------------------------------------------------------------------------- //

let eqs025 =
    [parse @"(x * y) * z = x * y * z";
    parse @"x * 1 = x";
    parse @"i(x) * x = 1"; ];;

// Note that here the simple LPO approach works, whereas K&B need
// some additional hacks.
//complete_and_simplify ["1"; "*"; "i"] eqs025);;

// ------------------------------------------------------------------------- //
// (l,r) systems II (K&B example 14).                                        //
// ------------------------------------------------------------------------- //

let eqs026 =
    [(parse @"(x * y) * z = x * y * z"); 
    (parse @"1 * x = x"); 
    (parse @"11 * x = x"); 
    (parse @"x * i(x) = 1"); 
    (parse @"x * j(x) = 11")];;

// This seems to be too slow. K&B encounter a similar problem
//complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs026;;

// ------------------------------------------------------------------------- //
// (l,r) systems III (K&B example 15).                                       //
// ------------------------------------------------------------------------- //

let eqs027 =
    [(parse @"(x * y) * z = x * y * z"); 
    (parse @"1 * x = x");  
    (parse @"prime(a) * a = star(a)"); 
    (parse @"star(a) * b = b")];;
//********* According to KB, this wouldn't be expected to work
// Real: 00:00:32.586, CPU: 00:00:32.640, GC gen0: 167, gen1: 4, gen2: 0
complete_and_simplify ["1"; "*"; "star"; "prime"] eqs027;;

//********** These seem too slow too. Maybe just a bad ordering?
let eqs028 =
    [(parse @"(x * y) * z = x * y * z"); 
    (parse @"1 * x = x");  
    (parse @"hash(a) * dollar(a) * a = star(a)"); 
    (parse @"star(a) * b = b"); 
    (parse @"a * hash(a) = 1"); 
    (parse @"a * 1 = hash(hash(a))"); 
    (parse @"hash(hash(hash(a))) = hash(a)")];;
// long running
//complete_and_simplify ["1"; "hash"; "star"; "*"; "dollar"] eqs028;;

let eqs029 =
    [(parse @"(x * y) * z = x * y * z"); 
    (parse @"1 * x = x"); 
    (parse @"hash(a) * dollar(a) * a = star(a)"); 
    (parse @"star(a) * b = b"); 
    (parse @"a * hash(a) = 1"); 
    (parse @"hash(hash(a)) = a * 1"); 
    (parse @"hash(hash(hash(a))) = hash(a)")];;
// long running
//complete_and_simplify ["1"; "star"; "*"; "hash"; "dollar"] eqs029;;

// ------------------------------------------------------------------------- //
// Central groupoids II. (K&B example 16).                                   //
// ------------------------------------------------------------------------- //

let eqs030 =
    [parse @"(a * a) * a = one(a)";
    parse @"a * (a * a) = two(a)";
    parse @"(a * b) * (b * c) = b";
    parse @"two(a) * b = a * b"; ];;
// Real: 00:01:37.253, CPU: 00:01:37.156, GC gen0: 478, gen1: 12, gen2: 1
complete_and_simplify ["one"; "two"; "*"] eqs030;;

// ------------------------------------------------------------------------- //
// Central groupoids II. (K&B example 17).                                   //
// ------------------------------------------------------------------------- //

let eqs031 =
    [(parse @"(a*a * a) = one(a)");
    (parse @"(a * a*a) = two(a)");
    (parse @"(a*b * b*c) = b")];;
//******* Not ordered right...
//complete_and_simplify ["*"; "one"; "two"] eqs031;;

// ------------------------------------------------------------------------- //
// Simply congruence closure.                                                //
// ------------------------------------------------------------------------- //

let eqs032 =
    [parse @"f(f(f(f(f(1))))) = 1";
    parse @"f(f(f(1))) = 1"; ];;
complete_and_simplify ["1"; "f"] eqs032;;

// ------------------------------------------------------------------------- //
// Bill McCune's and Deepak Kapur's single axioms for groups.                //
// ------------------------------------------------------------------------- //

let eqs033 = [(parse @"x * i(y * (((z * i(z)) * i(u * y)) * x)) = u")];;
// long running
//complete_and_simplify ["1"; "*"; "i"] eqs033;;

let eqs034 = [(parse @"((1 / (x / (y / (((x / x) / x) / z)))) / z) = y")];;
//******* Not ordered right?
//complete_and_simplify ["1"; "/"] eqs034;;

let eqs035 = [(parse @"i(x * i(x)) * (i(i((y * z) * u) * y) * i(u)) = z")];;
// long running
//complete_and_simplify ["*"; "i"] eqs035;;

// ------------------------------------------------------------------------- //
// A rather simple example from Baader & Nipkow, p. 141.                     //
// ------------------------------------------------------------------------- //

let eqs036 =  [parse @"f(f(x)) = g(x)"];;
complete_and_simplify ["g"; "f"] eqs036;;

let eqs1,def1,crits1 = funpow 122 (complete1 ord) (eqs036,def,crits);;

let eqs2,def2,crits2 = funpow 123 (complete1 ord) (eqs036,def,crits);;

// ------------------------------------------------------------------------- //
// Some of the exercises (these are taken from Baader & Nipkow).             //
// ------------------------------------------------------------------------- //

let eqs037 =
    [parse @"f(f(x)) = f(x)";
    parse @"g(g(x)) = f(x)";
    parse @"f(g(x)) = g(x)";
    parse @"g(f(x)) = f(x)"; ];;
complete_and_simplify ["f"; "g"] eqs037;;

let eqs038 =  [parse @"f(g(f(x))) = g(x)"];;
complete_and_simplify ["f"; "g"] eqs038;;

// ------------------------------------------------------------------------- //
// Inductive theorem proving example.                                        //
// ------------------------------------------------------------------------- //

let eqs039 =
    [parse @"0 + y = y";
    parse @"SUC(x) + y = SUC(x + y)";
    parse @"append(nil,l) = l";
    parse @"append(h::t,l) = h::append(t,l)";
    parse @"length(nil) = 0";
    parse @"length(h::t) = SUC(length(t))";
    parse @"rev(nil) = nil";
    parse @"rev(h::t) = append(rev(t),h::nil)"; ];;
complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "length"; "append"; "rev"] eqs039;;

let iprove eqs' tm =
    complete_and_simplify
        ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
        (tm :: eqs' @ eqs039);;

iprove [] (parse @"x + 0 = x");;

iprove [] (parse @"x + SUC(y) = SUC(x + y)");;

iprove [] (parse @"(x + y) + z = x + y + z");;

iprove [] (parse @"length(append(x,y)) = length(x) + length(y)");;

iprove [] (parse @"append(append(x,y),z) = append(x,append(y,z))");;

iprove [] (parse @"append(x,nil) = x");;

iprove 
    [parse @"append(append(x,y),z) = append(x,append(y,z))";
     parse @"append(x,nil) = x";]
    (parse @"rev(append(x,y)) = append(rev(y),rev(x))");;

iprove 
    [parse @"rev(append(x,y)) = append(rev(y),rev(x))";
    parse @"append(x,nil) = x";
    parse @"append(append(x,y),z) = append(x,append(y,z))"; ]
    (parse @"rev(rev(x)) = x");;

// ------------------------------------------------------------------------- //
// Here it's not immediately so obvious since we get extra equs.             //
// ------------------------------------------------------------------------- //

iprove [] (parse @"rev(rev(x)) = x");;

// ------------------------------------------------------------------------- //
// With fewer lemmas, it may just need more time or may not terminate.       //
// ------------------------------------------------------------------------- //

// not enough lemmas...or maybe it just needs more runtime
// long running
//iprove 
//    [(parse @"rev(append(x,y)) = append(rev(y),rev(x))")]
//    (parse @"rev(rev(x)) = x");;

// ------------------------------------------------------------------------- //
// Now something actually false...                                           //
// ------------------------------------------------------------------------- //

iprove [] (parse @"length(append(x,y)) = length(x)");; // try something false
