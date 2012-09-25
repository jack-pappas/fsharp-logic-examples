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
open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
open Reasoning.Automated.Harrison.Handbook.equal

//
// pg. 239
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// (parse "forall x1 x2 x3 y1 y2 y3. x1 =y1 /\ x2 =y2 /\ x3 =y3 ==> f(x1,x2,x3) =f(y1,y2,y3)")
// val it : unit = ()
print_fol_formula_list (function_congruence ("f", 3));;

// (parse "forall x1 x2 y1 y2. x1 =y1 /\ x2 =y2 ==> x1 +x2 =y1 +y2")
// val it : unit = ()
print_fol_formula_list (function_congruence ("+", 2));;

// pg. 241
// ------------------------------------------------------------------------- //
// A simple example (see EWD1266a and the application to Morley's theorem).  //
// ------------------------------------------------------------------------- //

// val ewd : fol Reasoning.Automated.Harrison.Handbook.formulas.formula =
//   Imp
//     (And
//        (Forall ("x",Atom (R ("=",[Var "x"; Var "x"]))),
//         And
//           (Forall
//              ("x",
//               Forall
//                 ("y",
//                  Forall
//                    ("z",
//                     Imp
//                       (And
//                          (Atom (R ("=",[Var "x"; Var "y"])),
//                           Atom (R ("=",[Var "x"; Var "z"]))),
//                        Atom (R ("=",[Var "y"; Var "z"])))))),
//            And
//              (Forall
//                 ("x1",
//                  Forall
//                    ("y1",
//                     Imp
//                       (Atom (R ("=",[Var "x1"; Var "y1"])),
//                        Imp
//                          (Atom (R ("f",[Var "x1"])),Atom (R ("f",[Var "y1"])))))),
//               Forall
//                 ("x1",
//                  Forall
//                    ("y1",
//                     Imp
//                       (Atom (R ("=",[Var "x1"; Var "y1"])),
//                        Imp
//                          (Atom (R ("g",[Var "x1"])),Atom (R ("g",[Var "y1"]))))))))),
//      Imp
//        (And
//           (Forall
//              ("x",Imp (Atom (R ("f",[Var "x"])),Atom (R ("g",[Var "x"])))),
//            And
//              (Exists ("x",Atom (R ("f",[Var "x"]))),
//               Forall
//                 ("x",
//                  Forall
//                    ("y",
//                     Imp
//                       (And (Atom (R ("g",[Var "x"])),Atom (R ("g",[Var "y"]))),
//                        Atom (R ("=",[Var "x"; Var "y"]))))))),
//         Forall ("y",Imp (Atom (R ("g",[Var "y"])),Atom (R ("f",[Var "y"]))))))
let ewd = equalitize (parse "(forall x. f(x) ==> g(x)) /\ (exists x. f(x)) /\ (forall x y. g(x) /\ g(y) ==> x = y) ==> forall y. g(y) ==> f(y)");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// val it : int list = [6]
meson002 ewd;;

// pg. 241
// ------------------------------------------------------------------------- //
// Wishnu Prasetya's example (even nicer with an "exists unique" primitive). //
// ------------------------------------------------------------------------- //

// val wishnu : fol Reasoning.Automated.Harrison.Handbook.formulas.formula =
//   Imp
//     (And
//        (Forall ("x",Atom (R ("=",[Var "x"; Var "x"]))),
//         And
//           (Forall
//              ("x",
//               Forall
//                 ("y",
//                  Forall
//                    ("z",
//                     Imp
//                       (And
//                          (Atom (R ("=",[Var "x"; Var "y"])),
//                           Atom (R ("=",[Var "x"; Var "z"]))),
//                        Atom (R ("=",[Var "y"; Var "z"])))))),
//            And
//              (Forall
//                 ("x1",
//                  Forall
//                    ("y1",
//                     Imp
//                       (Atom (R ("=",[Var "x1"; Var "y1"])),
//                        Atom
//                          (R ("=",[Fn ("f",[Var "x1"]); Fn ("f",[Var "y1"])]))))),
//               Forall
//                 ("x1",
//                  Forall
//                    ("y1",
//                     Imp
//                       (Atom (R ("=",[Var "x1"; Var "y1"])),
//                        Atom
//                          (R ("=",[Fn ("g",[Var "x1"]); Fn ("g",[Var "y1"])])))))))),
//      Iff
//        (Exists
//           ("x",
//            And
//              (Atom (R ("=",[Var "x"; Fn ("f",[Fn ("g",[Var "x"])])])),
//               Forall
//                 ("x'",
//                  Imp
//                    (Atom (R ("=",[Var "x'"; Fn ("f",[Fn ("g",[Var "x'"])])])),
//                     Atom (R ("=",[Var "x"; Var "x'"])))))),
//         Exists
//           ("y",
//            And
//              (Atom (R ("=",[Var "y"; Fn ("g",[Fn ("f",[Var "y"])])])),
//               Forall
//                 ("y'",
//                  Imp
//                    (Atom (R ("=",[Var "y'"; Fn ("g",[Fn ("f",[Var "y'"])])])),
//                     Atom (R ("=",[Var "y"; Var "y'"]))))))))
let wishnu =
    equalitize (parse
        "(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=> (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')");;

// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// Searching with depth limit 14
// Searching with depth limit 15
// Searching with depth limit 16
// Searching with depth limit 0
// Searching with depth limit 1
// Searching with depth limit 2
// Searching with depth limit 3
// Searching with depth limit 4
// Searching with depth limit 5
// Searching with depth limit 6
// Searching with depth limit 7
// Searching with depth limit 8
// Searching with depth limit 9
// Searching with depth limit 10
// Searching with depth limit 11
// Searching with depth limit 12
// Searching with depth limit 13
// Searching with depth limit 14
// Searching with depth limit 15
// Searching with depth limit 16
// CPU time (user): 18.406250
// val it : int list = [16; 16]
time meson002 wishnu;;

// pg. 248
// ------------------------------------------------------------------------- //
// More challenging equational problems. (Size 18, 61814 seconds.)           //
// ------------------------------------------------------------------------- //

//********

(meson002 >>|> equalitize) (parse
    "(forall x y z. x * (y * z) = (x * y) * z) /\ (forall x. 1 * x = x) /\ (forall x. i(x) * x = 1) ==> forall x. x * i(x) = 1");;

// *******//

// ------------------------------------------------------------------------- //
// Other variants not mentioned in book.                                     //
// ------------------------------------------------------------------------- //
//
//************
//
//(meson002 ** equalitize)
// (parse "(forall x y z. x * (y * z) = (x * y) * z) /\
//   (forall x. 1 * x = x) /\
//   (forall x. x * 1 = x) /\
//   (forall x. x * x = 1)
//   ==> forall x y. x * y  = y * x");;
//
// ------------------------------------------------------------------------- //
// With symmetry at leaves and one-sided congruences (Size = 16, 54659 s).   //
// ------------------------------------------------------------------------- //
//
//let fm =
// (parse "(forall x. x = x) /\
//   (forall x y z. x * (y * z) = (x * y) * z) /\
//   (forall x y z. =((x * y) * z,x * (y * z))) /\
//   (forall x. 1 * x = x) /\
//   (forall x. x = 1 * x) /\
//   (forall x. i(x) * x = 1) /\
//   (forall x. 1 = i(x) * x) /\
//   (forall x y. x = y ==> i(x) = i(y)) /\
//   (forall x y z. x = y ==> x * z = y * z) /\
//   (forall x y z. x = y ==> z * x = z * y) /\
//   (forall x y z. x = y /\ y = z ==> x = z)
//   ==> forall x. x * i(x) = 1");;
//
//time meson002 fm;;
//
// ------------------------------------------------------------------------- //
// Newer version of stratified equalities.                                   //
// ------------------------------------------------------------------------- //
//
//let fm =
// (parse "(forall x y z. axiom(x * (y * z),(x * y) * z)) /\
//   (forall x y z. axiom((x * y) * z,x * (y * z)) /\
//   (forall x. axiom(1 * x,x)) /\
//   (forall x. axiom(x,1 * x)) /\
//   (forall x. axiom(i(x) * x,1)) /\
//   (forall x. axiom(1,i(x) * x)) /\
//   (forall x x'. x = x' ==> cchain(i(x),i(x'))) /\
//   (forall x x' y y'. x = x' /\ y = y' ==> cchain(x * y,x' * y'))) /\
//   (forall s t. axiom(s,t) ==> achain(s,t)) /\
//   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
//   (forall x x' u. x = x' /\ achain(i(x'),u) ==> cchain(i(x),u)) /\
//   (forall x x' y y' u.
//        x = x' /\ y = y' /\ achain(x' * y',u) ==> cchain(x * y,u)) /\
//   (forall s t. cchain(s,t) ==> s = t) /\
//   (forall s t. achain(s,t) ==> s = t) /\
//   (forall t. t = t)
//   ==> forall x. x * i(x) = 1");;
//
//time meson002 fm;;
//
//let fm =
// (parse "(forall x y z. axiom(x * (y * z),(x * y) * z)) /\
//   (forall x y z. axiom((x * y) * z,x * (y * z)) /\
//   (forall x. axiom(1 * x,x)) /\
//   (forall x. axiom(x,1 * x)) /\
//   (forall x. axiom(i(x) * x,1)) /\
//   (forall x. axiom(1,i(x) * x)) /\
//   (forall x x'. x = x' ==> cong(i(x),i(x'))) /\
//   (forall x x' y y'. x = x' /\ y = y' ==> cong(x * y,x' * y'))) /\
//   (forall s t. axiom(s,t) ==> achain(s,t)) /\
//   (forall s t. cong(s,t) ==> cchain(s,t)) /\
//   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
//   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\
//   (forall s t. cchain(s,t) ==> s = t) /\
//   (forall s t. achain(s,t) ==> s = t) /\
//   (forall t. t = t)
//   ==> forall x. x * i(x) = 1");;
//
//time meson002 fm;;
//
// ------------------------------------------------------------------------- //
// Showing congruence closure.                                               //
// ------------------------------------------------------------------------- //
//
//let fm = equalitize
// (parse "forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c");;
//
//time meson002 fm;;
//
//let fm =
// (parse "axiom(f(f(f(f(f(c))))),c) /\
//   axiom(c,f(f(f(f(f(c)))))) /\
//   axiom(f(f(f(c))),c) /\
//   axiom(c,f(f(f(c)))) /\
//   (forall s t. axiom(s,t) ==> achain(s,t)) /\
//   (forall s t. cong(s,t) ==> cchain(s,t)) /\
//   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
//   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\
//   (forall s t. cchain(s,t) ==> s = t) /\
//   (forall s t. achain(s,t) ==> s = t) /\
//   (forall t. t = t) /\
//   (forall x y. x = y ==> cong(f(x),f(y)))
//   ==> f(c) = c");;
//
//time meson002 fm;;
//
// ------------------------------------------------------------------------- //
// With stratified equalities.                                               //
// ------------------------------------------------------------------------- //
//
//let fm =
// (parse "(forall x y z. eqA (x * (y * z),(x * y) * z)) /\
//   (forall x y z. eqA ((x * y) * z)) /\
//   (forall x. eqA (1 * x,x)) /\
//   (forall x. eqA (x,1 * x)) /\
//   (forall x. eqA (i(x) * x,1)) /\
//   (forall x. eqA (1,i(x) * x)) /\
//   (forall x. eqA (x,x)) /\
//   (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\
//   (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\
//   (forall x y. eqT (x,y) ==> eqC (i(x),i(y))) /\
//   (forall w x y z. eqA (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqA (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqA (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqC (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqC (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqC (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqT (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqT (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
//   (forall w x y z. eqT (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
//   (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z))
//   ==> forall x. eqT (x * i(x),1)");;
//
// ------------------------------------------------------------------------- //
// With transitivity chains...                                               //
// ------------------------------------------------------------------------- //
//
//let fm =
// (parse "(forall x y z. eqA (x * (y * z),(x * y) * z)) /\
//   (forall x y z. eqA ((x * y) * z)) /\
//   (forall x. eqA (1 * x,x)) /\
//   (forall x. eqA (x,1 * x)) /\
//   (forall x. eqA (i(x) * x,1)) /\
//   (forall x. eqA (1,i(x) * x)) /\
//   (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\
//   (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\
//   (forall w x y. eqA (w,x) ==> eqC (w * y,x * y)) /\
//   (forall w x y. eqC (w,x) ==> eqC (w * y,x * y)) /\
//   (forall x y z. eqA (y,z) ==> eqC (x * y,x * z)) /\
//   (forall x y z. eqC (y,z) ==> eqC (x * y,x * z)) /\
//   (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqC (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\
//   (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z))
//   ==> forall x. eqT (x * i(x),1) \/ eqC (x * i(x),1)");;
//
//time meson002 fm;;
//
// ------------------------------------------------------------------------- //
// Enforce canonicity (proof size = 20).                                     //
// ------------------------------------------------------------------------- //
//
//let fm =
// (parse "(forall x y z. eq1(x * (y * z),(x * y) * z)) /\
//   (forall x y z. eq1((x * y) * z,x * (y * z))) /\
//   (forall x. eq1(1 * x,x)) /\
//   (forall x. eq1(x,1 * x)) /\
//   (forall x. eq1(i(x) * x,1)) /\
//   (forall x. eq1(1,i(x) * x)) /\
//   (forall x y z. eq1(x,y) ==> eq1(x * z,y * z)) /\
//   (forall x y z. eq1(x,y) ==> eq1(z * x,z * y)) /\
//   (forall x y z. eq1(x,y) /\ eq2(y,z) ==> eq2(x,z)) /\
//   (forall x y. eq1(x,y) ==> eq2(x,y))
//   ==> forall x. eq2(x,i(x))");;
//
//time meson002 fm;;
//
//*****************//