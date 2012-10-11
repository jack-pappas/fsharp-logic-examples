// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.fol
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.folderived

fsi.AddPrinter sprint_thm

// pg. 490
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Atom (R ("=",[Var "s"; Var "t"])),
//      Atom
//        (R ("=",
//            [Fn
//               ("f",
//                [Var "s"; Fn ("g",[Var "s"; Var "t"; Var "s"]); Var "u";
//                 Fn ("h",[Fn ("h",[Var "s"])])]);
//             Fn
//               ("f",
//                [Var "s"; Fn ("g",[Var "t"; Var "t"; Var "s"]); Var "u";
//                 Fn ("h",[Fn ("h",[Var "t"])])])])))
icongruence (parset @"s") (parset @"t") (parset @"f(s,g(s,t,s),u,h(h(s)))")
                            (parset @"f(s,g(t,t,s),u,h(h(t)))");;
    
// pg. 494
// ------------------------------------------------------------------------- //
// An example.                                                               //
// ------------------------------------------------------------------------- //

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("y",
//            Forall
//              ("z",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
//                      Fn ("+",[Var "z"; Fn ("+",[Var "y"; Var "x"])])]))))),
//      Forall
//        ("y'",
//         Forall
//           ("z",
//            Atom
//              (R ("=",
//                  [Fn ("+",[Var "y"; Fn ("+",[Var "y'"; Var "z"])]);
//                   Fn ("+",[Var "z"; Fn ("+",[Var "y'"; Var "y"])])])))))
ispec (parset @"y") (parse @"forall x y z. x + y + z = z + y + x");;

// ------------------------------------------------------------------------- //
// Additional tests not in main text.                                        //
// ------------------------------------------------------------------------- //

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Atom
//        (R ("=",
//            [Fn ("+",[Var "x"; Var "x"]); Fn ("*",[Fn ("2",[]); Var "x"])])),
//      Imp
//        (Imp
//           (Atom (R ("=",[Fn ("+",[Var "x"; Var "x"]); Var "x"])),
//            Atom (R ("=",[Var "x"; Fn ("0",[])]))),
//         Imp
//           (Atom (R ("=",[Fn ("*",[Fn ("2",[]); Var "x"]); Var "x"])),
//            Atom (R ("=",[Var "x"; Fn ("0",[])])))))
isubst (parset @"x + x") (parset @"2 * x")
        (parse @"x + x = x ==> x = 0") (parse @"2 * x = x ==> x = 0");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Atom
//        (R ("=",
//            [Fn ("+",[Var "x"; Var "x"]); Fn ("*",[Fn ("2",[]); Var "x"])])),
//      Imp
//        (Imp
//           (Atom
//              (R ("=",
//                  [Fn ("+",[Var "x"; Var "x"]);
//                   Fn ("+",[Var "y"; Var "y"])])),
//            Atom
//              (R ("=",
//                  [Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])]);
//                   Fn ("+",[Var "x"; Fn ("+",[Var "x"; Var "x"])])]))),
//         Imp
//           (Atom
//              (R ("=",
//                  [Fn ("*",[Fn ("2",[]); Var "x"]);
//                   Fn ("+",[Var "y"; Var "y"])])),
//            Atom
//              (R ("=",
//                  [Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])]);
//                   Fn ("+",[Var "x"; Fn ("*",[Fn ("2",[]); Var "x"])])])))))
isubst (parset @"x + x")  (parset @"2 * x")
        (parse @"(x + x = y + y) ==> (y + y + y = x + x + x)")
        (parse @"2 * x = y + y ==> y + y + y = x + 2 * x");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("y",
//            Forall
//              ("z",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
//                      Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])]))))),
//      Forall
//        ("y",
//         Forall
//           ("z",
//            Atom
//              (R ("=",
//                  [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
//                   Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])])))))
ispec (parset @"x") (parse @"forall x y z. x + y + z = y + z + z") ;;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall ("x",Atom (R ("=",[Var "x"; Var "x"]))),
//      Atom (R ("=",[Var "x"; Var "x"])))
ispec (parset @"x") (parse @"forall x. x = x") ;;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("y",
//            Forall
//              ("z",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
//                      Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])]))))),
//      Forall
//        ("y'",
//         Forall
//           ("z'",
//            Atom
//              (R ("=",
//                  [Fn
//                     ("+",
//                      [Fn ("+",[Var "w"; Fn ("+",[Var "y"; Var "z"])]);
//                       Fn ("+",[Var "y'"; Var "z'"])]);
//                   Fn ("+",[Var "y'"; Fn ("+",[Var "z'"; Var "z'"])])])))))
ispec (parset @"w + y + z") (parse @"forall x y z. x + y + z = y + z + z") ;;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("y",
//            Forall
//              ("z",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
//                      Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])]))))),
//      Forall
//        ("y'",
//         Forall
//           ("z'",
//            Atom
//              (R ("=",
//                  [Fn
//                     ("+",
//                      [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
//                       Fn ("+",[Var "y'"; Var "z'"])]);
//                  Fn ("+",[Var "y'"; Fn ("+",[Var "z'"; Var "z'"])])])))))
ispec (parset @"x + y + z") (parse @"forall x y z. x + y + z = y + z + z") ;;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall ("x",Forall ("y",Forall ("z",Atom (R ("nothing_much",[]))))),
//      Forall ("y",Forall ("z",Atom (R ("nothing_much",[])))))
ispec (parset @"x + y + z") (parse @"forall x y z. nothing_much") ;;

// val it :
//   (Reasoning.Automated.Harrison.Handbook.formulas.formula<fol> ->
//      Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm) =
//   <fun:it@292>
isubst (parset @"x + x") (parset @"2 * x")
        (parse @"(x + x = y + y) <=> (something \/ y + y + y = x + x + x)");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Atom
//        (R ("=",
//            [Fn ("+",[Var "x"; Var "x"]); Fn ("*",[Fn ("2",[]); Var "x"])])),
//      Imp
//        (Iff
//           (Exists ("x",Atom (R ("=",[Var "x"; Fn ("2",[])]))),
//            Exists
//              ("y",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "y"; Fn ("+",[Var "x"; Var "x"])]);
//                      Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])])])))),
//         Iff
//           (Exists ("x",Atom (R ("=",[Var "x"; Fn ("2",[])]))),
//            Exists
//              ("y",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "y"; Fn ("*",[Fn ("2",[]); Var "x"])]);
//                      Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])])]))))))
isubst (parset @"x + x")  (parset @"2 * x")
        (parse @"(exists x. x = 2) <=> exists y. y + x + x = y + y + y")
        (parse @"(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Atom (R ("=",[Var "x"; Var "y"])),
//      Imp
//        (Iff
//           (Forall ("z",Atom (R ("=",[Var "x"; Var "z"]))),
//            And
//              (Exists ("x",Atom (R ("<",[Var "y"; Var "z"]))),
//               Forall ("y",Atom (R ("<",[Var "y"; Var "x"]))))),
//         Iff
//           (Forall ("z",Atom (R ("=",[Var "y"; Var "z"]))),
//            And
//              (Exists ("x",Atom (R ("<",[Var "y"; Var "z"]))),
//               Forall ("y'",Atom (R ("<",[Var "y'"; Var "y"])))))))
isubst (parset @"x")  (parset @"y")
        (parse @"(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)")
        (parse @"(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)");;

// ------------------------------------------------------------------------- //
// The bug is now fixed.                                                     //
// ------------------------------------------------------------------------- //

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("x'",
//            Forall
//              ("x''",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
//                      Fn ("0",[])]))))),
//      Forall
//        ("x''",
//         Forall
//           ("x'''",
//            Atom
//              (R ("=",
//                  [Fn ("+",[Var "x'"; Fn ("+",[Var "x''"; Var "x'''"])]);
//                   Fn ("0",[])])))))
ispec (parset @"x'") (parse @"forall x x' x''. x + x' + x'' = 0");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("x'",
//            Forall
//              ("x''",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
//                      Fn ("0",[])]))))),
//      Forall
//        ("x'",
//         Forall
//           ("x'''",
//            Atom
//              (R ("=",
//                  [Fn ("+",[Var "x''"; Fn ("+",[Var "x'"; Var "x'''"])]);
//                   Fn ("0",[])])))))
ispec (parset @"x''") (parse @"forall x x' x''. x + x' + x'' = 0");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("x'",
//            Forall
//              ("x''",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
//                      Fn ("0",[])]))))),
//      Forall
//        ("x'''",
//         Forall
//           ("x''''",
//            Atom
//              (R ("=",
//                  [Fn
//                     ("+",
//                      [Fn ("+",[Var "x'"; Var "x''"]);
//                       Fn ("+",[Var "x'''"; Var "x''''"])]); Fn ("0",[])])))))
ispec (parset @"x' + x''") (parse @"forall x x' x''. x + x' + x'' = 0");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("x'",
//            Forall
//              ("x''",
//               Atom
//                 (R ("=",
//                     [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
//                      Fn ("0",[])]))))),
//      Forall
//        ("x'''",
//         Forall
//           ("x''''",
//            Atom
//              (R ("=",
//                  [Fn
//                     ("+",
//                      [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
//                       Fn ("+",[Var "x'''"; Var "x''''"])]); Fn ("0",[])])))))
ispec (parset @"x + x' + x''") (parse @"forall x x' x''. x + x' + x'' = 0");;

// val it : Reasoning.Automated.Harrison.Handbook.lcf.ProverOperators.thm =
//   Imp
//     (Forall
//        ("x",
//         Forall
//           ("x'",
//            Atom
//              (R ("=",
//                  [Fn ("+",[Var "x"; Var "x'"]);
//                   Fn ("+",[Var "x'"; Var "x"])])))),
//      Forall
//        ("x'",
//         Atom
//           (R ("=",
//               [Fn ("+",[Fn ("*",[Fn ("2",[]); Var "x"]); Var "x'"]);
//                Fn ("+",[Var "x'"; Fn ("*",[Fn ("2",[]); Var "x"])])]))))
ispec (parset @"2 * x") (parse @"forall x x'. x + x' = x' + x");;