// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.interpolation

fsi.AddPrinter sprint_fol_formula

// pg. 429
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

//val p002 : formula<fol> =
//  Forall
//    ("x",
//     Forall
//       ("y",
//        And
//          (Atom (R ("R",[Var "x"; Fn ("f",[Var "x"])])),
//           Iff
//             (Atom (R ("S",[Var "x"; Var "y"])),
//              Or
//                (Atom (R ("R",[Var "x"; Var "y"])),
//                 Atom (R ("R",[Var "y"; Var "x"])))))))
let p002 = prenex (parse @"(forall x. R(x,f(x))) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))");;

//val q002 : formula<fol> =
//  Forall
//    ("x",
//     Forall
//       ("y",
//        Forall
//          ("z",
//           And
//             (Imp
//                (And
//                   (Atom (R ("S",[Var "x"; Var "y"])),
//                    Atom (R ("S",[Var "y"; Var "z"]))),
//                 Atom (R ("T",[Var "x"; Var "z"]))),
//              Not (Atom (R ("T",[Fn ("0",[]); Fn ("0",[])])))))))
let q002 = prenex (parse @"(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(0,0)");;

//0 ground instances tried; 0 items in list.
//0 ground instances tried; 0 items in list.
//1 ground instances tried; 5 items in list.
//1 ground instances tried; 5 items in list.
//2 ground instances tried; 6 items in list.
//3 ground instances tried; 10 items in list.
//
//val c002 : formula<fol> =
//  Or
//    (And
//       (Atom (R ("S",[Fn ("0",[]); Fn ("f",[Fn ("0",[])])])),
//        Atom (R ("S",[Fn ("f",[Fn ("0",[])]); Fn ("0",[])]))),
//     And
//       (Atom (R ("S",[Fn ("0",[]); Fn ("f",[Fn ("0",[])])])),
//        Atom (R ("S",[Fn ("f",[Fn ("0",[])]); Fn ("0",[])]))))
let c002 = urinterpolate p002 q002;;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(p002,c002));;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(q002,Not c002));;
        
// pg. 433
// ------------------------------------------------------------------------- //
// The same example now gives a true interpolant.                            //
// ------------------------------------------------------------------------- //

//0 ground instances tried; 0 items in list.
//0 ground instances tried; 0 items in list.
//1 ground instances tried; 5 items in list.
//1 ground instances tried; 5 items in list.
//2 ground instances tried; 6 items in list.
//3 ground instances tried; 10 items in list.
//
//val c003 : formula<fol> =
//  Forall
//    ("v_2",
//     Exists
//       ("v_1",
//        Or
//          (And
//             (Atom (R ("S",[Var "v_2"; Var "v_1"])),
//              Atom (R ("S",[Var "v_1"; Var "v_2"]))),
//           And
//             (Atom (R ("S",[Var "v_2"; Var "v_1"])),
//              Atom (R ("S",[Var "v_1"; Var "v_2"]))))))
let c003 = uinterpolate p002 q002;;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(p002,c003));;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(q002,Not c003));;
        
// pg. 434
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// val p004 : formula<fol> =
//   And
//     (Forall ("x",Exists ("y",Atom (R ("R",[Var "x"; Var "y"])))),
//      Forall
//        ("x",
//         Forall
//           ("y",
//            Iff
//              (Atom (R ("S",[Var "v"; Var "x"; Var "y"])),
//               Or
//                 (Atom (R ("R",[Var "x"; Var "y"])),
//                  Atom (R ("R",[Var "y"; Var "x"])))))))
let p004 = (parse @"(forall x. exists y. R(x,y)) /\ (forall x y. S(v,x,y) <=> R(x,y) \/ R(y,x))");;

// val q004 : formula<fol> =
//   And
//     (Forall
//        ("x",
//         Forall
//           ("y",
//            Forall
//              ("z",
//               Imp
//                 (And
//                    (Atom (R ("S",[Var "v"; Var "x"; Var "y"])),
//                     Atom (R ("S",[Var "v"; Var "y"; Var "z"]))),
//                  Atom (R ("T",[Var "x"; Var "z"])))))),
//      Exists ("u",Not (Atom (R ("T",[Var "u"; Var "u"])))))
let q004 = (parse @"(forall x y z. S(v,x,y) /\ S(v,y,z) ==> T(x,z)) /\ (exists u. ~T(u,u))");;

// 0 ground instances tried; 0 items in list.
// 0 ground instances tried; 0 items in list.
// 1 ground instances tried; 5 items in list.
// 2 ground instances tried; 6 items in list.
// 3 ground instances tried; 10 items in list.
// 4 ground instances tried; 11 items in list.
// 5 ground instances tried; 16 items in list.
// 6 ground instances tried; 17 items in list.
// 7 ground instances tried; 20 items in list.
// 8 ground instances tried; 21 items in list.
// 8 ground instances tried; 21 items in list.
// 9 ground instances tried; 22 items in list.
// 10 ground instances tried; 23 items in list.
// 11 ground instances tried; 24 items in list.
// 12 ground instances tried; 25 items in list.
// 13 ground instances tried; 29 items in list.
// 14 ground instances tried; 30 items in list.
// 15 ground instances tried; 34 items in list.
// 16 ground instances tried; 35 items in list.
// 17 ground instances tried; 36 items in list.
// 18 ground instances tried; 37 items in list.
// 19 ground instances tried; 38 items in list.
// 20 ground instances tried; 39 items in list.
// 21 ground instances tried; 43 items in list.
// 22 ground instances tried; 44 items in list.
// 23 ground instances tried; 48 items in list.
// 24 ground instances tried; 49 items in list.
// 25 ground instances tried; 54 items in list.
// 26 ground instances tried; 55 items in list.
// 27 ground instances tried; 59 items in list.
// 28 ground instances tried; 60 items in list.
// 29 ground instances tried; 65 items in list.
// 30 ground instances tried; 66 items in list.
// 
// val c004 : formula<fol> =
//   Forall
//     ("v_2",
//      Exists
//        ("v_1",
//         Or
//           (And
//              (Atom (R ("S",[Var "v"; Var "v_2"; Var "v_1"])),
//               Atom (R ("S",[Var "v"; Var "v_1"; Var "v_2"]))),
//            And
//              (Atom (R ("S",[Var "v"; Var "v_2"; Var "v_1"])),
//               Atom (R ("S",[Var "v"; Var "v_1"; Var "v_2"]))))))
let c004 = interpolate p004 q004;;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(p004,c004));;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(q004,Not c004));;

// ------------------------------------------------------------------------- //
// More examples, not in the text.                                           //
// ------------------------------------------------------------------------- //

// val p005 : formula<fol> =
//   Imp (Atom (R ("p",[])),And (Atom (R ("q",[])),Atom (R ("r",[]))))
let p005 = (parse @"(p ==> q /\ r)");;

// val q005 : formula<fol> =
//   Not
//     (Imp
//        (Imp (Atom (R ("q",[])),Atom (R ("p",[]))),
//         Imp
//           (Atom (R ("s",[])),Iff (Atom (R ("p",[])),Atom (R ("q",[]))))))
let q005 = (parse @"~((q ==> p) ==> s ==> (p <=> q))");;

// 0 ground instances tried; 0 items in list.
// 0 ground instances tried; 0 items in list.
//
// val c005 : formula<fol> =
//   Or
//     (Not (Atom (R ("p",[]))),
//      Or (Not (Atom (R ("p",[]))),Atom (R ("q",[]))))
let c005 = interpolate p005 q005;;

// val it : bool = true
tautology(Imp(And(p005,q005),False));;

// val it : bool = true
tautology(Imp(p005,c005));;

// val it : bool = true
tautology(Imp(q005,Not c005));;

// ------------------------------------------------------------------------- //
// A more interesting example.                                               //
// ------------------------------------------------------------------------- //

// val p006 : formula<fol> =
//   And
//     (Forall ("x",Exists ("y",Atom (R ("R",[Var "x"; Var "y"])))),
//      Forall
//        ("x",
//         Forall
//           ("y",
//            Iff
//              (Atom (R ("S",[Var "x"; Var "y"])),
//               Or
//                 (Atom (R ("R",[Var "x"; Var "y"])),
//                  Atom (R ("R",[Var "y"; Var "x"])))))))
let p006 = (parse @"(forall x. exists y. R(x,y)) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))");;

// val q006 : formula<fol> =
//   And
//     (Forall
//        ("x",
//         Forall
//           ("y",
//            Forall
//              ("z",
//               Imp
//                 (And
//                    (Atom (R ("S",[Var "x"; Var "y"])),
//                     Atom (R ("S",[Var "y"; Var "z"]))),
//                  Atom (R ("T",[Var "x"; Var "z"])))))),
//      Not (Atom (R ("T",[Var "u"; Var "u"]))))
let q006 = (parse @"(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)");;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(And(p006,q006),False));;

// 0 ground instances tried; 0 items in list.
// 0 ground instances tried; 0 items in list.
// 1 ground instances tried; 5 items in list.
// 1 ground instances tried; 5 items in list.
// 2 ground instances tried; 6 items in list.
// 3 ground instances tried; 10 items in list.
// 
// val c006 : formula<fol> =
//   Forall
//     ("v_2",
//      Exists
//        ("v_1",
//         Or
//           (And
//              (Atom (R ("S",[Var "v_2"; Var "v_1"])),
//               Atom (R ("S",[Var "v_1"; Var "v_2"]))),
//            And
//              (Atom (R ("S",[Var "v_2"; Var "v_1"])),
//               Atom (R ("S",[Var "v_1"; Var "v_2"]))))))
let c006 = interpolate p006 q006;;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(p006,c006));;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(q006,Not c006));;

// ------------------------------------------------------------------------- //
// A variant where u is free in both parts.                                  //
// ------------------------------------------------------------------------- //

// val p007 : formula<fol> =
//   And
//     (Forall ("x",Exists ("y",Atom (R ("R",[Var "x"; Var "y"])))),
//      And
//        (Forall
//           ("x",
//            Forall
//              ("y",
//               Iff
//                 (Atom (R ("S",[Var "x"; Var "y"])),
//                  Or
//                    (Atom (R ("R",[Var "x"; Var "y"])),
//                     Atom (R ("R",[Var "y"; Var "x"])))))),
//         Forall
//           ("v",
//            Imp
//              (Atom (R ("R",[Var "u"; Var "v"])),
//               Atom (R ("Q",[Var "v"; Var "u"]))))))
let p007 = (parse @"(forall x. exists y. R(x,y)) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x)) /\ (forall v. R(u,v) ==> Q(v,u))");;

// val q007 : formula<fol> =
//   And
//     (Forall
//        ("x",
//         Forall
//           ("y",
//            Forall
//              ("z",
//               Imp
//                 (And
//                    (Atom (R ("S",[Var "x"; Var "y"])),
//                     Atom (R ("S",[Var "y"; Var "z"]))),
//                  Atom (R ("T",[Var "x"; Var "z"])))))),
//      Not (Atom (R ("T",[Var "u"; Var "u"]))))
let q007 = (parse @"(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)");;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(And(p007,q007),False));;

// 0 ground instances tried; 0 items in list.
// 0 ground instances tried; 0 items in list.
// 1 ground instances tried; 6 items in list.
// 1 ground instances tried; 6 items in list.
// 2 ground instances tried; 7 items in list.
// 3 ground instances tried; 11 items in list.
//
// val c007 : formula<fol> =
//   Exists
//     ("v_1",
//      Or
//        (Or
//           (And
//              (Atom (R ("S",[Var "u"; Var "v_1"])),
//               Atom (R ("S",[Var "v_1"; Var "u"]))),
//            And
//              (Atom (R ("S",[Var "u"; Var "v_1"])),
//               Atom (R ("S",[Var "v_1"; Var "u"])))),
//         Or
//           (Or
//              (And
//                 (Atom (R ("S",[Var "u"; Var "v_1"])),
//                  Atom (R ("S",[Var "v_1"; Var "u"]))),
//               And
//                 (Atom (R ("S",[Var "u"; Var "v_1"])),
//                  Atom (R ("S",[Var "v_1"; Var "u"])))),
//            Or
//              (And
//                 (Atom (R ("S",[Var "u"; Var "v_1"])),
//                  Atom (R ("S",[Var "v_1"; Var "u"]))),
//               And
//                 (Atom (R ("S",[Var "u"; Var "v_1"])),
//                  Atom (R ("S",[Var "v_1"; Var "u"])))))))
let c007 = interpolate p007 q007;;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(p007,c007));;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(q007,Not c007));;

// ------------------------------------------------------------------------- //
// Way of generating examples quite easily (see K&K exercises).              //
// ------------------------------------------------------------------------- //

// val test_interp : formula<fol> -> formula<fol>
let test_interp fm =
    let rec p = generalize (skolemize fm)
    and q = generalize (skolemize (Not fm))
    let c = interpolate p q
    meson002(Imp(And(p,q),False)) |> ignore
    meson002(Imp(p,c)) |> ignore
    meson002(Imp(q,Not c)) |> ignore
    c;;
    
// Fixed this: Process is terminated due to StackOverflowException.
test_interp (parse @"forall x. P(x) ==> exists y. forall z. P(z) ==> Q(y)");;

// Fixed this: Process is terminated due to StackOverflowException.
test_interp (parse @"forall y. exists y. forall z. exists a. P(a,x,y,z) ==> P(x,y,z,a)");;

// ------------------------------------------------------------------------- //
// Hintikka's examples.                                                      //
// ------------------------------------------------------------------------- //

// val p009 : formula<fol> = Forall ("x",Atom (R ("L",[Var "x"; Var "b"])))
let p009 = (parse @"forall x. L(x,b)");;

// val q009 : formula<fol> =
//   And
//     (Forall
//        ("y",
//         Imp
//           (Atom (R ("L",[Var "b"; Var "y"])),
//            Atom (R ("=",[Var "m"; Var "y"])))),
//      Not (Atom (R ("=",[Var "m"; Var "b"]))))
let q009 = (parse @"(forall y. L(b,y) ==> m = y) /\ ~(m = b)");;

// 0 ground instances tried; 0 items in list.
// 0 ground instances tried; 0 items in list.
// 
// val c009 : formula<fol> = Atom (R ("L",[Var "b"; Var "b"]))
let c009 = einterpolate p009 q009;;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(p009,c009));;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(q009,Not c009));;

// val p010 : formula<fol> =
//   And
//     (Forall
//        ("x",
//         Imp
//           (And (Atom (R ("A",[Var "x"])),Atom (R ("C",[Var "x"]))),
//            Atom (R ("B",[Var "x"])))),
//      Forall
//        ("x",
//         Imp
//           (Or (Atom (R ("D",[Var "x"])),Not (Atom (R ("D",[Var "x"])))),
//            Atom (R ("C",[Var "x"])))))
let p010 = (parse @"(forall x. A(x) /\ C(x) ==> B(x)) /\ (forall x. D(x) \/ ~D(x) ==> C(x))");;

// val q010 : formula<fol> =
//   Not
//     (Forall
//        ("x",
//         Imp
//           (Atom (R ("E",[Var "x"])),
//            Imp (Atom (R ("A",[Var "x"])),Atom (R ("B",[Var "x"]))))))
let q010 = (parse @"~(forall x. E(x) ==> A(x) ==> B(x))");;

// 0 ground instances tried; 0 items in list.
// 0 ground instances tried; 0 items in list.
// 
// val c010 : formula<fol> =
//   Forall
//     ("v_1",
//      Or
//        (Or (Not (Atom (R ("A",[Var "v_1"]))),Atom (R ("B",[Var "v_1"]))),
//         Or (Not (Atom (R ("A",[Var "v_1"]))),Atom (R ("B",[Var "v_1"])))))
let c010 = interpolate p010 q010;;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(p010,c010));;

// Fixed this: Process is terminated due to StackOverflowException.
meson002(Imp(q010,Not c010));;
