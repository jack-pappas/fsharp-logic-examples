// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.cong
open FSharpx.Books.AutomatedReasoning.cooper
open FSharpx.Books.AutomatedReasoning.real
open FSharpx.Books.AutomatedReasoning.combining

fsi.AddPrinter sprint_fol_formula

// pg. 440
// ------------------------------------------------------------------------- //
// Running example if we magically knew the interpolant.                     //
// ------------------------------------------------------------------------- //
    
(integer_qelim << generalize) (parse
    "(u + 1 = v /\ v_1 + 1 = u - 1 /\ v_2 - 1 = v + 1 /\ v_3 = v - 1) ==> u = v_3 /\ ~(v_1 = v_2)");;

ccvalid (parse
    "(v_2 = f(v_3) /\ v_1 = f(u)) ==> ~(u = v_3 /\ ~(v_1 = v_2))");;
        
// pg. 444
// ------------------------------------------------------------------------- //
// Check that our example works.                                             //
// ------------------------------------------------------------------------- //

nelop001 (add_default [int_lang]) (parse
    "f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false");;
     
// pg. 444
// ------------------------------------------------------------------------- //
// Bell numbers show the size of our case analysis.                          //
// ------------------------------------------------------------------------- //

let bell n = List.length (allpartitions (1 -- n))
List.map bell (1 -- 10);;
            
// pg. 446
// ------------------------------------------------------------------------- //
// Some additional examples (from ICS paper and Shostak's "A practical..."   //
// ------------------------------------------------------------------------- //

nelop (add_default [int_lang]) (parse
    "y <= x /\ y >= x + z /\ z >= 0 ==> f(f(x) - f(y)) = f(z)");;

nelop (add_default [int_lang]) (parse
    "x = y /\ y >= z /\ z >= x ==> f(z) = f(x)");;

nelop (add_default [int_lang]) (parse
    "a <= b /\ b <= f(a) /\ f(a) <= 1 ==> a + b <= 1 \/ b + f(b) <= 1 \/ f(f(b)) <= f(a)");;

// pg. 447
// ------------------------------------------------------------------------- //
// Confirmation of non-convexity.                                            //
// ------------------------------------------------------------------------- //

List.map (real_qelim << generalize) [
    parse "x * y = 0 /\ z = 0 ==> x = z \/ y = z";
    parse "x * y = 0 /\ z = 0 ==> x = z";
    parse "x * y = 0 /\ z = 0 ==> y = z"; ];;

List.map (integer_qelim << generalize) [
    parse "0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y \/ x = z";
    parse "0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y";
    parse "0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = z"; ];;

// pg. 449
// ------------------------------------------------------------------------- //
// Failures of original Shostak procedure.                                   //
// ------------------------------------------------------------------------- //

nelop (add_default [int_lang]) (parse
    "f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false");;

// ** And this one is where the original procedure loops **//

nelop (add_default [int_lang]) (parse
    "f(v) = v /\ f(u) = u - 1 /\ u = v ==> false");;

// ------------------------------------------------------------------------- //
// Additional examples not in the text.                                      //
// ------------------------------------------------------------------------- //

//** This is on p. 8 of Shostak's "Deciding combinations" paper

time (nelop (add_default [int_lang])) (parse
    "z = f(x - y) /\ x = z + y /\ ~(-(y) = -(x - f(f(z)))) ==> false");;

//** This (ICS theories-1) fails without array operations

time (nelop (add_default [int_lang])) (parse
    "a + 2 = b ==> f(read(update(A,a,3),b-2)) = f(b - a + 1)");;

//** can-001 from ICS examples site, with if-then-elses expanded manually

time (nelop (add_default [int_lang])) (parse
    "(x = y /\ z = 1 ==> f(f((x+z))) = f(f((1+y))))");;

// ** RJB example; lists plus uninterpreted functions

time (nelop (add_default [int_lang])) (parse
    "hd(x) = hd(y) /\ tl(x) = tl(y) /\ ~(x = nil) /\ ~(y = nil) ==> f(x) = f(y)");;

// ** Another one from the ICS paper

time (nelop (add_default [int_lang])) (parse
    "~(f(f(x) - f(y)) = f(z)) /\ y <= x /\ y >= x + z /\ z >= 0 ==> false");;

// ** Shostak's "A Practical Decision Procedure..." paper
// *** No longer works since I didn't do predicates in congruence closure

time (nelop (add_default [int_lang])) (parse
    "x < f(y) + 1 /\ f(y) <= x ==> (P(x,y) <=> P(f(y),y))");;

//** Shostak's "Practical..." paper again, using extra clauses for MAX

time (nelop (add_default [int_lang])) (parse
    "(x >= y ==> MAX(x,y) = x) /\ (y >= x ==> MAX(x,y) = y) ==> x = y + 2 ==> MAX(x,y) = x");;

// ** Shostak's "Practical..." paper again

time (nelop (add_default [int_lang])) (parse
    "x <= g(x) /\ x >= g(x) ==> x = g(g(g(g(x))))");;

// ** Easy example I invented **//

time (nelop (add_default [real_lang])) (parse
    "x^2 =  1 ==> (f(x) = f(-(x)))  ==> (f(x) = f(1))");;

// ** Taken from Clark Barrett's CVC page

time (nelop (add_default [int_lang])) (parse
    "2 * f(x + y) = 3 * y /\ 2 * x = y ==> f(f(x + y)) = 3 * x");;

// ** My former running example in the text; seems too slow.
// *** Anyway this also needs extra predicates in CC
time (nelop (add_default [real_lang])) (parse
    "x^2 = y^2 /\ x < y /\ z^2 = z /\ x < x * z /\ P(f(1 + z)) ==> P(f(x + y) - f(0))");;

// ** An example where the "naive" procedure is slow but feasible

nelop (add_default [int_lang]) (parse
    "4 * x = 2 * x + 2 * y /\ x = f(2 * x - y) /\ f(2 * y - x) = 3 /\ f(x) = 4 ==> false");;