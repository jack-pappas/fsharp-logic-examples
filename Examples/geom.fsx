// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.cooper
open FSharpx.Books.AutomatedReasoning.complex
open FSharpx.Books.AutomatedReasoning.real
open FSharpx.Books.AutomatedReasoning.grobner
open FSharpx.Books.AutomatedReasoning.geom

// pg. 415
//  ------------------------------------------------------------------------- // 
//  Trivial example.                                                          // 
//  ------------------------------------------------------------------------- // 

// val it : formula<fol> =
//   Imp
//     (Atom
//        (R ("=",
//            [Fn
//               ("*",
//                [Fn ("-",[Var "a_x"; Var "b_x"]);
//                 Fn ("-",[Var "b_y"; Var "c_y"])]);
//             Fn
//               ("*",
//                [Fn ("-",[Var "a_y"; Var "b_y"]);
//                 Fn ("-",[Var "b_x"; Var "c_x"])])])),
//      Atom
//        (R ("=",
//            [Fn
//               ("*",
//                [Fn ("-",[Var "b_x"; Var "a_x"]);
//                 Fn ("-",[Var "a_y"; Var "c_y"])]);
//             Fn
//               ("*",
//                [Fn ("-",[Var "b_y"; Var "a_y"]);
//                 Fn ("-",[Var "a_x"; Var "c_x"])])])))
coordinate (parse @"collinear(a,b,c) ==> collinear(b,a,c)");;
        
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// val it : bool = true
List.forall (grobner_decide << invariant_under_translation) coordinations;;

// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 5 basis elements and 5 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 5 basis elements and 5 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 5 basis elements and 5 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 5 basis elements and 5 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 5 basis elements and 9 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 9 basis elements and 29 pairs
// 9 basis elements and 28 pairs
// 9 basis elements and 27 pairs
// 4 basis elements and 6 pairs
// 5 basis elements and 9 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 9 basis elements and 29 pairs
// 9 basis elements and 28 pairs
// 10 basis elements and 36 pairs
// 10 basis elements and 35 pairs
// 10 basis elements and 34 pairs
// 10 basis elements and 33 pairs
// 10 basis elements and 32 pairs
// 10 basis elements and 31 pairs
// 10 basis elements and 30 pairs
// 10 basis elements and 29 pairs
// 10 basis elements and 28 pairs
// 10 basis elements and 27 pairs
// 10 basis elements and 26 pairs
// 11 basis elements and 35 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 7 basis elements and 16 pairs
// 7 basis elements and 15 pairs
// 7 basis elements and 14 pairs
// 7 basis elements and 13 pairs
// 7 basis elements and 12 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 8 basis elements and 22 pairs
// 8 basis elements and 21 pairs
// 8 basis elements and 20 pairs
// 8 basis elements and 19 pairs
// 8 basis elements and 18 pairs
// 8 basis elements and 17 pairs
// 8 basis elements and 16 pairs
// 8 basis elements and 15 pairs
// 8 basis elements and 14 pairs
// 9 basis elements and 21 pairs
// 9 basis elements and 20 pairs
// 10 basis elements and 28 pairs
// 10 basis elements and 27 pairs
// 10 basis elements and 26 pairs
// 10 basis elements and 25 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 9 basis elements and 29 pairs
// 9 basis elements and 28 pairs
// 9 basis elements and 27 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// val it : bool = true
List.forall (grobner_decide << invariant_under_rotation) coordinations;;
    
// pg. 416
//  ------------------------------------------------------------------------- // 
//  And show we can always invent such a transformation to zero a y:          // 
//  ------------------------------------------------------------------------- // 

Initialization.runWithEnlargedStack (fun () -> real_qelim (parse @"forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0"));;

// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 6 basis elements and 10 pairs
// 7 basis elements and 15 pairs
// 7 basis elements and 14 pairs
// 7 basis elements and 13 pairs
// 7 basis elements and 12 pairs
// 7 basis elements and 11 pairs
// 7 basis elements and 10 pairs
// 7 basis elements and 9 pairs
// 7 basis elements and 8 pairs
// 8 basis elements and 14 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 6 basis elements and 10 pairs
// 7 basis elements and 15 pairs
// 7 basis elements and 14 pairs
// 7 basis elements and 13 pairs
// 7 basis elements and 12 pairs
// 7 basis elements and 11 pairs
// 7 basis elements and 10 pairs
// 7 basis elements and 9 pairs
// 7 basis elements and 8 pairs
// 8 basis elements and 14 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 6 basis elements and 10 pairs
// 7 basis elements and 15 pairs
// 7 basis elements and 14 pairs
// 7 basis elements and 13 pairs
// 7 basis elements and 12 pairs
// 7 basis elements and 11 pairs
// 7 basis elements and 10 pairs
// 7 basis elements and 9 pairs
// 7 basis elements and 8 pairs
// 8 basis elements and 14 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 6 basis elements and 10 pairs
// 7 basis elements and 15 pairs
// 7 basis elements and 14 pairs
// 7 basis elements and 13 pairs
// 7 basis elements and 12 pairs
// 7 basis elements and 11 pairs
// 7 basis elements and 10 pairs
// 7 basis elements and 9 pairs
// 7 basis elements and 8 pairs
// 8 basis elements and 14 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 7 basis elements and 16 pairs
// 8 basis elements and 22 pairs
// 8 basis elements and 21 pairs
// 8 basis elements and 20 pairs
// 9 basis elements and 27 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 9 basis elements and 29 pairs
// 9 basis elements and 28 pairs
// 10 basis elements and 36 pairs
// 10 basis elements and 35 pairs
// 10 basis elements and 34 pairs
// 10 basis elements and 33 pairs
// 10 basis elements and 32 pairs
// 11 basis elements and 41 pairs
// 11 basis elements and 40 pairs
// 11 basis elements and 39 pairs
// 11 basis elements and 38 pairs
// 11 basis elements and 37 pairs
// 11 basis elements and 36 pairs
// 12 basis elements and 46 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 7 basis elements and 16 pairs
// 7 basis elements and 15 pairs
// 7 basis elements and 14 pairs
// 7 basis elements and 13 pairs
// 8 basis elements and 19 pairs
// 9 basis elements and 26 pairs
// 9 basis elements and 25 pairs
// 9 basis elements and 24 pairs
// 9 basis elements and 23 pairs
// 9 basis elements and 22 pairs
// 9 basis elements and 21 pairs
// 9 basis elements and 20 pairs
// 9 basis elements and 19 pairs
// 9 basis elements and 18 pairs
// 9 basis elements and 17 pairs
// 10 basis elements and 25 pairs
// 10 basis elements and 24 pairs
// 10 basis elements and 23 pairs
// 10 basis elements and 22 pairs
// 10 basis elements and 21 pairs
// 10 basis elements and 20 pairs
// 10 basis elements and 19 pairs
// 11 basis elements and 28 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 8 basis elements and 22 pairs
// 8 basis elements and 21 pairs
// 8 basis elements and 20 pairs
// 9 basis elements and 27 pairs
// 10 basis elements and 35 pairs
// 10 basis elements and 34 pairs
// 10 basis elements and 33 pairs
// 10 basis elements and 32 pairs
// 11 basis elements and 41 pairs
// 11 basis elements and 40 pairs
// 11 basis elements and 39 pairs
// 12 basis elements and 49 pairs
// 12 basis elements and 48 pairs
// 12 basis elements and 47 pairs
// 13 basis elements and 58 pairs
// 14 basis elements and 70 pairs
// 14 basis elements and 69 pairs
// 14 basis elements and 68 pairs
// 14 basis elements and 67 pairs
// 14 basis elements and 66 pairs
// 14 basis elements and 65 pairs
// 14 basis elements and 64 pairs
// 14 basis elements and 63 pairs
// 14 basis elements and 62 pairs
// 14 basis elements and 61 pairs
// 14 basis elements and 60 pairs
// 14 basis elements and 59 pairs
// 14 basis elements and 58 pairs
// 14 basis elements and 57 pairs
// 15 basis elements and 70 pairs
// 15 basis elements and 69 pairs
// 15 basis elements and 68 pairs
// 15 basis elements and 67 pairs
// 15 basis elements and 66 pairs
// 15 basis elements and 65 pairs
// 15 basis elements and 64 pairs
// 15 basis elements and 63 pairs
// 15 basis elements and 62 pairs
// 16 basis elements and 76 pairs
// 16 basis elements and 75 pairs
// 16 basis elements and 74 pairs
// 16 basis elements and 73 pairs
// 16 basis elements and 72 pairs
// 16 basis elements and 71 pairs
// 16 basis elements and 70 pairs
// 16 basis elements and 69 pairs
// 16 basis elements and 68 pairs
// 16 basis elements and 67 pairs
// 17 basis elements and 82 pairs
// 17 basis elements and 81 pairs
// 17 basis elements and 80 pairs
// 17 basis elements and 79 pairs
// 17 basis elements and 78 pairs
// 17 basis elements and 77 pairs
// 17 basis elements and 76 pairs
// 17 basis elements and 75 pairs
// 17 basis elements and 74 pairs
// 17 basis elements and 73 pairs
// 17 basis elements and 72 pairs
// 18 basis elements and 88 pairs
// 18 basis elements and 87 pairs
// 18 basis elements and 86 pairs
// 18 basis elements and 85 pairs
// 18 basis elements and 84 pairs
// 18 basis elements and 83 pairs
// 18 basis elements and 82 pairs
// 18 basis elements and 81 pairs
// 18 basis elements and 80 pairs
// 18 basis elements and 79 pairs
// 18 basis elements and 78 pairs
// 18 basis elements and 77 pairs
// 19 basis elements and 94 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 4 basis elements and 4 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 6 basis elements and 11 pairs
// 7 basis elements and 16 pairs
// 7 basis elements and 15 pairs
// 7 basis elements and 14 pairs
// 7 basis elements and 13 pairs
// 7 basis elements and 12 pairs
// 4 basis elements and 6 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 8 basis elements and 22 pairs
// 8 basis elements and 21 pairs
// 8 basis elements and 20 pairs
// 8 basis elements and 19 pairs
// 9 basis elements and 26 pairs
// 9 basis elements and 25 pairs
// 9 basis elements and 24 pairs
// 9 basis elements and 23 pairs
// 9 basis elements and 22 pairs
// 9 basis elements and 21 pairs
// 9 basis elements and 20 pairs
// 9 basis elements and 19 pairs
// 9 basis elements and 18 pairs
// 9 basis elements and 17 pairs
// 9 basis elements and 16 pairs
// val it : bool = true
List.forall (grobner_decide << invariant_under_scaling) coordinations;;

// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 2 basis elements and 1 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 1 pairs
// 3 basis elements and 0 pairs
// 2 basis elements and 1 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 1 pairs
// 3 basis elements and 0 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 5 basis elements and 5 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 3 basis elements and 3 pairs
// 4 basis elements and 5 pairs
// 5 basis elements and 8 pairs
// 5 basis elements and 7 pairs
// 5 basis elements and 6 pairs
// 5 basis elements and 5 pairs
// val it : (string * formula<fol>) list * (string * formula<fol>) list =
//   ([("collinear",
//      Atom
//        (R ("=",
//            [Fn
//               ("*",
//                [Fn ("-",[Var "1_x"; Var "2_x"]);
//                 Fn ("-",[Var "2_y"; Var "3_y"])]);
//             Fn
//               ("*",
//                [Fn ("-",[Var "1_y"; Var "2_y"]);
//                 Fn ("-",[Var "2_x"; Var "3_x"])])])));
//     ("parallel",
//      Atom
//        (R ("=",
//            [Fn
//               ("*",
//                [Fn ("-",[Var "1_x"; Var "2_x"]);
//                 Fn ("-",[Var "3_y"; Var "4_y"])]);
//             Fn
//               ("*",
//                [Fn ("-",[Var "1_y"; Var "2_y"]);
//                 Fn ("-",[Var "3_x"; Var "4_x"])])])));
//     ("is_midpoint",
//      And
//        (Atom
//           (R ("=",
//               [Fn ("*",[Fn ("2",[]); Var "1_x"]);
//                Fn ("+",[Var "2_x"; Var "3_x"])])),
//         Atom
//           (R ("=",
//               [Fn ("*",[Fn ("2",[]); Var "1_y"]);
//                Fn ("+",[Var "2_y"; Var "3_y"])]))));
//     ("is_intersection",
//      And
//        (Atom
//           (R ("=",
//               [Fn
//                  ("*",
//                   [Fn ("-",[Var "1_x"; Var "2_x"]);
//                    Fn ("-",[Var "2_y"; Var "3_y"])]);
//                Fn
//                  ("*",
//                   [Fn ("-",[Var "1_y"; Var "2_y"]);
//                    Fn ("-",[Var "2_x"; Var "3_x"])])])),
//         Atom
//           (R ("=",
//               [Fn
//                  ("*",
//                   [Fn ("-",[Var "1_x"; Var "4_x"]);
//                    Fn ("-",[Var "4_y"; Var "5_y"])]);
//                Fn
//                  ("*",
//                   [Fn ("-",[Var "1_y"; Var "4_y"]);
//                    Fn ("-",[Var "4_x"; Var "5_x"])])]))));
//     ("=",
//      And
//        (Atom (R ("=",[Var "1_x"; Var "2_x"])),
//         Atom (R ("=",[Var "1_y"; Var "2_y"]))))],
//    [("perpendicular",
//      Atom
//        (R ("=",
//            [Fn
//               ("+",
//                [Fn
//                   ("*",
//                    [Fn ("-",[Var "1_x"; Var "2_x"]);
//                     Fn ("-",[Var "3_x"; Var "4_x"])]);
//                 Fn
//                   ("*",
//                    [Fn ("-",[Var "1_y"; Var "2_y"]);
//                     Fn ("-",[Var "3_y"; Var "4_y"])])]); Fn ("0",[])])));
//     ("lengths_eq",
//      Atom
//        (R ("=",
//            [Fn
//               ("+",
//                [Fn ("^",[Fn ("-",[Var "1_x"; Var "2_x"]); Fn ("2",[])]);
//                 Fn ("^",[Fn ("-",[Var "1_y"; Var "2_y"]); Fn ("2",[])])]);
//             Fn
//               ("+",
//                [Fn ("^",[Fn ("-",[Var "3_x"; Var "4_x"]); Fn ("2",[])]);
//                 Fn ("^",[Fn ("-",[Var "3_y"; Var "4_y"]); Fn ("2",[])])])])))])
List.partition (grobner_decide << invariant_under_shearing) coordinations;;
    
// pg. 418
//  ------------------------------------------------------------------------- // 
//  One from "Algorithms for Computer Algebra"                                // 
//  ------------------------------------------------------------------------- // 

(grobner_decide << originate) (parse @"is_midpoint(m,a,c) /\ perpendicular(a,c,m,b) ==> lengths_eq(a,b,b,c)");;
       
// pg. 418
//  ------------------------------------------------------------------------- // 
//  Parallelogram theorem (Chou's expository example at the start).           // 
//  ------------------------------------------------------------------------- // 

(grobner_decide << originate) (parse @"parallel(a,b,d,c) /\ parallel(a,d,b,c) /\ is_intersection(e,a,c,b,d) ==> lengths_eq(a,e,e,c)");;

(grobner_decide << originate) (parse @"parallel(a,b,d,c) /\ parallel(a,d,b,c) /\ is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c) ==> lengths_eq(a,e,e,c)");;
        
// pg. 421
//  ------------------------------------------------------------------------- // 
//  Simson's theorem.                                                         // 
//  ------------------------------------------------------------------------- // 

// val simson : formula<fol> =
//   Imp
//     (And
//        (Atom (R ("lengths_eq",[Var "o"; Var "a"; Var "o"; Var "b"])),
//         And
//           (Atom (R ("lengths_eq",[Var "o"; Var "a"; Var "o"; Var "c"])),
//            And
//              (Atom
//                 (R ("lengths_eq",[Var "o"; Var "a"; Var "o"; Var "d"])),
//               And
//                 (Atom (R ("collinear",[Var "e"; Var "b"; Var "c"])),
//                  And
//                    (Atom (R ("collinear",[Var "f"; Var "a"; Var "c"])),
//                     And
//                       (Atom
//                          (R ("collinear",[Var "g"; Var "a"; Var "b"])),
//                        And
//                          (Atom
//                             (R ("perpendicular",
//                                 [Var "b"; Var "c"; Var "d"; Var "e"])),
//                           And
//                             (Atom
//                                (R ("perpendicular",
//                                    [Var "a"; Var "c"; Var "d"; Var "f"])),
//                              Atom
//                                (R ("perpendicular",
//                                    [Var "a"; Var "b"; Var "d"; Var "g"])))))))))),
//      Atom (R ("collinear",[Var "e"; Var "f"; Var "g"])))
let simson = (parse @"lengths_eq(o,a,o,b) /\ lengths_eq(o,a,o,c) /\ lengths_eq(o,a,o,d) /\ collinear(e,b,c) /\ collinear(f,a,c) /\ collinear(g,a,b) /\ perpendicular(b,c,d,e) /\ perpendicular(a,c,d,f) /\ perpendicular(a,b,d,g) ==> collinear(e,f,g)");;

// val vars001 : string list =
//   ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";
//    "b_y"; "b_x"; "o_x"]
let vars001 = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";  "b_y"; "b_x"; "o_x"];;

// val zeros001 : string list = ["a_x"; "a_y"; "o_y"]
let zeros001 = ["a_x"; "a_y"; "o_y"];;

// val it : formula<fol> list =
//   [Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn
//                                ("*",
//                                 [Var "b_x";
//                                  Fn
//                                    ("+",
//                                     [Fn ("0",[]);
//                                      Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
//                          Fn
//                            ("*",
//                             [Var "b_y";
//                              Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
//                      Fn
//                        ("*",
//                         [Var "c_x";
//                          Fn
//                            ("+",
//                             [Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "b_x"; Fn ("-2",[])])]);
//                              Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "c_y";
//                      Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "b_y"; Fn ("-2",[])])]);
//                          Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]);
//                      Fn
//                        ("*",
//                         [Var "b_x";
//                          Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "b_y";
//                      Fn
//                        ("+",
//                         [Fn ("0",[]); Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]); Fn ("*",[Var "b_x"; Fn ("-1",[])])]);
//                  Fn ("*",[Var "c_x"; Fn ("1",[])])]); Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]);
//                      Fn
//                        ("*",
//                         [Var "c_x";
//                          Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "c_y";
//                      Fn
//                        ("+",
//                         [Fn ("0",[]); Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "b_x"; Fn ("1",[])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "c_x"; Fn ("1",[])])]);
//              Fn ("0",[])])));
//    Not (Atom (R ("=",[Fn ("-1",[]); Fn ("0",[])])))]
wu simson vars001 zeros001;;
    
// pg. 423
//  ------------------------------------------------------------------------- // 
//  Try without special coordinates.                                          // 
//  ------------------------------------------------------------------------- // 

// val it : formula<fol> list =
//   [Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn
//                                ("*",
//                                 [Var "a_y";
//                                  Fn
//                                    ("+",
//                                     [Fn ("0",[]);
//                                      Fn ("*",[Var "a_y"; Fn ("1",[])])])])]);
//                          Fn
//                            ("*",
//                             [Var "a_x";
//                              Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "a_x"; Fn ("1",[])])])])]);
//                      Fn
//                        ("*",
//                         [Var "b_x";
//                          Fn
//                            ("+",
//                             [Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "a_x"; Fn ("-2",[])])]);
//                              Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "b_y";
//                      Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "a_y"; Fn ("-2",[])])]);
//                          Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn
//                                ("*",
//                                 [Var "a_y";
//                                  Fn
//                                    ("+",
//                                     [Fn ("0",[]);
//                                      Fn ("*",[Var "a_y"; Fn ("1",[])])])])]);
//                          Fn
//                            ("*",
//                             [Var "a_x";
//                              Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "a_x"; Fn ("1",[])])])])]);
//                      Fn
//                        ("*",
//                         [Var "c_x";
//                          Fn
//                            ("+",
//                             [Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "a_x"; Fn ("-2",[])])]);
//                              Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "c_y";
//                      Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "a_y"; Fn ("-2",[])])]);
//                          Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn
//                                ("*",
//                                 [Var "b_x";
//                                  Fn
//                                    ("+",
//                                     [Fn ("0",[]);
//                                      Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
//                          Fn
//                            ("*",
//                             [Var "b_y";
//                              Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
//                      Fn
//                        ("*",
//                         [Var "c_x";
//                          Fn
//                            ("+",
//                             [Fn
//                                ("+",
//                                 [Fn ("0",[]);
//                                  Fn ("*",[Var "b_x"; Fn ("-2",[])])]);
//                              Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "c_y";
//                      Fn
//                        ("+",
//                         [Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "b_y"; Fn ("-2",[])])]);
//                          Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]); Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
//                  Fn ("*",[Var "b_x"; Fn ("1",[])])]); Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]); Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
//                  Fn ("*",[Var "c_x"; Fn ("1",[])])]); Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]); Fn ("*",[Var "b_x"; Fn ("-1",[])])]);
//                  Fn ("*",[Var "c_x"; Fn ("1",[])])]); Fn ("0",[])])));
//    Not (Atom (R ("=",[Fn ("-1",[]); Fn ("0",[])])))]
wu simson (vars001 @ zeros001) [];;
    
// pg. 423
//  ------------------------------------------------------------------------- // 
//  Pappus (Chou's figure 6).                                                 // 
//  ------------------------------------------------------------------------- // 

// val pappus : formula<fol> =
//   Imp
//     (And
//        (Atom (R ("collinear",[Var "a1"; Var "b2"; Var "d"])),
//         And
//           (Atom (R ("collinear",[Var "a2"; Var "b1"; Var "d"])),
//            And
//              (Atom (R ("collinear",[Var "a2"; Var "b3"; Var "e"])),
//               And
//                 (Atom (R ("collinear",[Var "a3"; Var "b2"; Var "e"])),
//                  And
//                    (Atom (R ("collinear",[Var "a1"; Var "b3"; Var "f"])),
//                     Atom (R ("collinear",[Var "a3"; Var "b1"; Var "f"]))))))),
//      Atom (R ("collinear",[Var "d"; Var "e"; Var "f"])))
let pappus = (parse @"collinear(a1,b2,d) /\ collinear(a2,b1,d) /\ collinear(a2,b3,e) /\ collinear(a3,b2,e) /\ collinear(a1,b3,f) /\ collinear(a3,b1,f) ==> collinear(d,e,f)");;

// val vars002 : string list =
//   ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "b3_y"; "b2_y"; "b1_y";
//    "a3_x"; "a2_x"; "a1_x"]
let vars002 = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"];;

// val zeros002 : string list =
//   ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"]
let zeros002 = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"];;

// val it : formula<fol> list =
//   [Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]);
//                      Fn
//                        ("*",
//                         [Var "b1_y";
//                          Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "a1_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "b2_y";
//                      Fn
//                        ("+",
//                         [Fn ("0",[]);
//                          Fn ("*",[Var "a2_x"; Fn ("-1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]);
//                      Fn
//                        ("*",
//                         [Var "b1_y";
//                          Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "a1_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "b3_y";
//                      Fn
//                        ("+",
//                         [Fn ("0",[]);
//                          Fn ("*",[Var "a3_x"; Fn ("-1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn
//                ("+",
//                 [Fn
//                    ("+",
//                     [Fn ("0",[]);
//                      Fn
//                        ("*",
//                         [Var "b2_y";
//                          Fn
//                            ("+",
//                             [Fn ("0",[]);
//                              Fn ("*",[Var "a2_x"; Fn ("1",[])])])])]);
//                  Fn
//                    ("*",
//                     [Var "b3_y";
//                      Fn
//                        ("+",
//                         [Fn ("0",[]);
//                          Fn ("*",[Var "a3_x"; Fn ("-1",[])])])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "a1_x"; Fn ("-1",[])])]);
//              Fn ("0",[])])));
//    Not
//      (Atom
//         (R ("=",
//             [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "a2_x"; Fn ("-1",[])])]);
//              Fn ("0",[])])))]
wu pappus vars002 zeros002;;

//  ------------------------------------------------------------------------- // 
//  The Butterfly (figure 9).                                                 // 
//  ------------------------------------------------------------------------- // 

// val butterfly : formula<fol> =
//   Imp
//     (And
//        (Atom (R ("lengths_eq",[Var "b"; Var "o"; Var "a"; Var "o"])),
//         And
//           (Atom (R ("lengths_eq",[Var "c"; Var "o"; Var "a"; Var "o"])),
//            And
//              (Atom
//                 (R ("lengths_eq",[Var "d"; Var "o"; Var "a"; Var "o"])),
//               And
//                 (Atom (R ("collinear",[Var "a"; Var "e"; Var "c"])),
//                  And
//                    (Atom (R ("collinear",[Var "d"; Var "e"; Var "b"])),
//                     And
//                       (Atom
//                          (R ("perpendicular",
//                              [Var "e"; Var "f"; Var "o"; Var "e"])),
//                        And
//                          (Atom
//                             (R ("collinear",[Var "a"; Var "f"; Var "d"])),
//                           And
//                             (Atom
//                                (R ("collinear",
//                                    [Var "f"; Var "e"; Var "g"])),
//                              Atom
//                                (R ("collinear",
//                                    [Var "b"; Var "c"; Var "g"])))))))))),
//      Atom (R ("is_midpoint",[Var "e"; Var "f"; Var "g"])))
let butterfly = (parse @"lengths_eq(b,o,a,o) /\ lengths_eq(c,o,a,o) /\ lengths_eq(d,o,a,o) /\ collinear(a,e,c) /\ collinear(d,e,b) /\  perpendicular(e,f,o,e) /\ collinear(a,f,d) /\ collinear(f,e,g) /\ collinear(b,c,g) ==> is_midpoint(e,f,g)");;

// val vars003 : string list =
//   ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "c_y"; "b_y"; "d_x";
//    "c_x"; "b_x"; "a_x"]
let vars003 = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "c_y"; "b_y"; "d_x"; "c_x"; "b_x"; "a_x"]

// val zeros003 : string list = ["a_y"; "o_x"; "o_y"]
let zeros003 = ["a_y"; "o_x"; "o_y"];;

// This one is costly (too big for laptop, but doable in about 300M)
// However, it gives exactly the same degenerate conditions as Chou

//val it : formula<fol> list =
//  [Not
//     (Atom
//        (R ("=",
//            [Fn
//               ("+",
//                [Fn
//                   ("+",
//                    [Fn
//                       ("+",
//                        [Fn
//                           ("+",
//                            [Fn ("0",[]);
//                             Fn
//                               ("*",
//                                [Var "e_x";
//                                 Fn
//                                   ("+",
//                                    [Fn
//                                       ("+",
//                                        [Fn ("0",[]);
//                                         Fn
//                                           ("*",[Var "b_y"; Fn ("1",[])])]);
//                                     Fn ("*",[Var "c_y"; Fn ("-1",[])])])])]);
//                         Fn
//                           ("*",
//                            [Var "e_y";
//                             Fn
//                               ("+",
//                                [Fn
//                                   ("+",
//                                    [Fn ("0",[]);
//                                     Fn ("*",[Var "b_x"; Fn ("-1",[])])]);
//                                 Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
//                     Fn
//                       ("*",
//                        [Var "f_x";
//                         Fn
//                           ("+",
//                            [Fn
//                               ("+",
//                                [Fn ("0",[]);
//                                 Fn ("*",[Var "b_y"; Fn ("-1",[])])]);
//                             Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
//                 Fn
//                   ("*",
//                    [Var "f_y";
//                     Fn
//                       ("+",
//                        [Fn
//                           ("+",
//                            [Fn ("0",[]);
//                             Fn ("*",[Var "b_x"; Fn ("1",[])])]);
//                         Fn ("*",[Var "c_x"; Fn ("-1",[])])])])]);
//             Fn ("0",[])])));
//   Not
//     (Atom
//        (R ("=",
//            [Fn
//               ("+",
//                [Fn
//                   ("+",
//                    [Fn
//                       ("+",
//                        [Fn ("0",[]);
//                         Fn
//                           ("*",
//                            [Var "b_y";
//                             Fn
//                               ("+",
//                                [Fn
//                                   ("+",
//                                    [Fn ("0",[]);
//                                     Fn ("*",[Var "a_x"; Fn ("1",[])])]);
//                                 Fn ("*",[Var "c_x"; Fn ("-1",[])])])])]);
//                     Fn
//                       ("*",
//                        [Var "c_y";
//                         Fn
//                           ("+",
//                            [Fn
//                               ("+",
//                                [Fn ("0",[]);
//                                 Fn ("*",[Var "b_x"; Fn ("1",[])])]);
//                             Fn ("*",[Var "d_x"; Fn ("-1",[])])])])]);
//                 Fn
//                   ("*",
//                    [Var "d_y";
//                     Fn
//                       ("+",
//                        [Fn
//                           ("+",
//                            [Fn ("0",[]);
//                             Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
//                         Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
//             Fn ("0",[])])));
//   Not
//     (Atom
//        (R ("=",
//            [Fn
//               ("+",
//                [Fn
//                   ("+",[Fn ("0",[]); Fn ("*",[Var "a_x"; Fn ("1",[])])]);
//                 Fn ("*",[Var "c_x"; Fn ("-1",[])])]); Fn ("0",[])])));
//   Not
//     (Atom
//        (R ("=",
//            [Fn
//               ("+",
//                [Fn
//                   ("+",
//                    [Fn ("0",[]);
//                     Fn
//                       ("*",
//                        [Var "e_x";
//                         Fn
//                           ("+",
//                            [Fn
//                               ("+",
//                                [Fn ("0",[]);
//                                 Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
//                             Fn ("*",[Var "d_x"; Fn ("1",[])])])])]);
//                 Fn
//                   ("*",
//                    [Var "e_y";
//                     Fn
//                       ("+",
//                        [Fn ("0",[]); Fn ("*",[Var "d_y"; Fn ("1",[])])])])]);
//             Fn ("0",[])])));
//   Not
//     (Atom
//        (R ("=",
//            [Fn
//               ("+",
//                [Fn
//                   ("+",[Fn ("0",[]); Fn ("*",[Var "e_x"; Fn ("1",[])])]);
//                 Fn ("*",[Var "f_x"; Fn ("-1",[])])]); Fn ("0",[])])));
//   Not
//     (Atom
//        (R ("=",
//            [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "e_y"; Fn ("1",[])])]);
//             Fn ("0",[])])));
//   Not (Atom (R ("=",[Fn ("1",[]); Fn ("0",[])])))]
wu butterfly vars003 zeros003;;


// ** Other examples removed from text

//  ------------------------------------------------------------------------- // 
//  Centroid (Chou, example 142).                                             // 
//  ------------------------------------------------------------------------- // 

(grobner_decide << originate) (parse @"is_midpoint(d,b,c) /\ is_midpoint(e,a,c) /\ is_midpoint(f,a,b) /\ is_intersection(m,b,e,a,d) ==> collinear(c,f,m)");;
