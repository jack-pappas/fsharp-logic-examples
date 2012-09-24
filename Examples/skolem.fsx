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
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem

// pg. 140
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : fol formula =
//   Imp (Forall ("x",Atom (R ("P",[Var "x"]))),Atom (R ("Q",[])))
simplify004 (parse "(forall x y. P(x) \/ (P(y) /\ false)) ==> exists z. Q");;

// pg. 141
// ------------------------------------------------------------------------- //
// Example of NNF function in action.                                        //
// ------------------------------------------------------------------------- //

// val it : fol formula =
//   Or
//     (Exists ("x",Not (Atom (R ("P",[Var "x"])))),
//      Or
//        (And
//           (Exists ("y",Atom (R ("Q",[Var "y"]))),
//            Exists
//              ("z",And (Atom (R ("P",[Var "z"])),Atom (R ("Q",[Var "z"]))))),
//         And
//           (Forall ("y",Not (Atom (R ("Q",[Var "y"])))),
//            Forall
//              ("z",
//               Or
//                 (Not (Atom (R ("P",[Var "z"]))),Not (Atom (R ("Q",[Var "z"]))))))))
nnf (parse "(forall x. P(x)) ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))");;

// pg. 144
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : fol formula =
//   Exists
//     ("x",
//      Forall
//        ("z",
//         Or
//           (And (Not (Atom (R ("P",[Var "x"]))),Not (Atom (R ("R",[Var "y"])))),
//            Or
//              (Atom (R ("Q",[Var "x"])),
//               Or
//                 (Not (Atom (R ("P",[Var "z"]))),Not (Atom (R ("Q",[Var "z"]))))))))
pnf (parse "(forall x. P(x) \/ R(y)) ==> exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z))");;

// pg. 150
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : fol formula =
//   Or
//     (Not (Atom (R ("<",[Var "x"; Fn ("f_y",[Var "x"])]))),
//      Atom
//        (R ("<",
//            [Fn ("*",[Var "x"; Var "u"]);
//             Fn ("*",[Fn ("f_y",[Var "x"]); Fn ("f_v",[Var "u"; Var "x"])])])))
skolemize (parse "exists y. x < y ==> forall u. exists v. x * u < y * v");;

// val it : fol formula =
//   Or
//     (Not (Atom (R ("P",[Var "x"]))),
//      Or
//        (Atom (R ("Q",[Fn ("c_y",[])])),
//         Or (Not (Atom (R ("P",[Var "z"]))),Not (Atom (R ("Q",[Var "z"]))))))
skolemize
 (parse "forall x. P(x)
             ==> (exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z)))");;