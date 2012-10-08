// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.geom

open NUnit.Framework
open FsUnit
open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.cooper
open Reasoning.Automated.Harrison.Handbook.complex
open Reasoning.Automated.Harrison.Handbook.real
open Reasoning.Automated.Harrison.Handbook.grobner
open Reasoning.Automated.Harrison.Handbook.geom


(* ------------------------------------------------------------------------- *)
(* Trivial example.                                                          *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 1``() =
    @"collinear(a,b,c) ==> collinear(b,a,c)"
    |> parse
    |> coordinate
    |> should equal
    <| Imp
         (Atom
           (R ("=",
             [Fn ("*",
               [Fn ("-", [Var "a_x"; Var "b_x"]);
                Fn ("-", [Var "b_y"; Var "c_y"])]);
              Fn ("*",
               [Fn ("-", [Var "a_y"; Var "b_y"]);
                Fn ("-", [Var "b_x"; Var "c_x"])])])),
         Atom
          (R ("=",
            [Fn ("*",
              [Fn ("-", [Var "b_x"; Var "a_x"]);
               Fn ("-", [Var "a_y"; Var "c_y"])]);
             Fn ("*",
              [Fn ("-", [Var "b_y"; Var "a_y"]);
               Fn ("-", [Var "a_x"; Var "c_x"])])])))

(* ------------------------------------------------------------------------- *)
(* Verify equivalence under rotation.                                        *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 2``() =
    coordinations
    |> List.forall (grobner_decide << invariant_under_translation)
    |> should equal true

[<Test>]
let ``examples 3``() =
    coordinations
    |> List.forall (grobner_decide << invariant_under_rotation)
    |> should equal true


(* ------------------------------------------------------------------------- *)
(* And show we can always invent such a transformation to zero a y:          *)
(* ------------------------------------------------------------------------- *)

[<Test; Category("LongRunning")>]
let ``examples 4``() =
    @"forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0"
    |> parse
    |> real_qelim
    |> should equal True


(* ------------------------------------------------------------------------- *)
(* Other interesting invariances.                                            *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 5``() =
    coordinations
    |> List.forall (grobner_decide << invariant_under_scaling)
    |> should equal true

// TODO : Determine the expected result of this test; it's output is truncated
// by ocamltop so we can't tell what it should be.
//[<Test>]
//let ``examples 6``() =
//    coordinations
//    |> List.partition (grobner_decide << invariant_under_shearing)
//    |> should equal (* ??? *)


(* ------------------------------------------------------------------------- *)
(* One from "Algorithms for Computer Algebra"                                *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 7``() =
    @"is_midpoint(m,a,c) /\ perpendicular(a,c,m,b)
        ==> lengths_eq(a,b,b,c)"
    |> parse
    |> (grobner_decide << originate)
    |> should equal true


(* ------------------------------------------------------------------------- *)
(* Parallelogram theorem (Chou's expository example at the start).           *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 8``() =
    @"parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
       is_intersection(e,a,c,b,d)
       ==> lengths_eq(a,e,e,c)"
    |> parse
    |> (grobner_decide << originate)
    |> should equal false

[<Test>]
let ``examples 9``() =
    @"parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
       is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
       ==> lengths_eq(a,e,e,c)"
    |> parse
    |> (grobner_decide << originate)
    |> should equal true


(* ------------------------------------------------------------------------- *)
(* Simson's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let private simson =
    @"lengths_eq(o,a,o,b) /\
    lengths_eq(o,a,o,c) /\
    lengths_eq(o,a,o,d) /\
    collinear(e,b,c) /\
    collinear(f,a,c) /\
    collinear(g,a,b) /\
    perpendicular(b,c,d,e) /\
    perpendicular(a,c,d,f) /\
    perpendicular(a,b,d,g)
    ==> collinear(e,f,g)"
    |> parse

let rec private simson_vars =
    ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y";
     "d_x"; "c_y"; "c_x"; "b_y"; "b_x"; "o_x"]

and private simson_zeros =
    ["a_x"; "a_y"; "o_y"]

[<Test>]
let ``examples 10``() =
    wu simson simson_vars simson_zeros
    |> should equal
    <| [Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn
                                    ("*",
                                     [Var "b_x";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
                              Fn
                                ("*",
                                 [Var "b_y";
                                  Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
                          Fn
                            ("*",
                             [Var "c_x";
                              Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "b_x"; Fn ("-2",[])])]);
                                  Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
                      Fn
                        ("*",
                         [Var "c_y";
                          Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn ("*",[Var "b_y"; Fn ("-2",[])])]);
                              Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
                  Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn ("0",[]);
                          Fn
                            ("*",
                             [Var "b_x";
                              Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
                      Fn
                        ("*",
                         [Var "b_y";
                          Fn
                            ("+",
                             [Fn ("0",[]); Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
                  Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn ("0",[]); Fn ("*",[Var "b_x"; Fn ("-1",[])])]);
                      Fn ("*",[Var "c_x"; Fn ("1",[])])]); Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn ("0",[]);
                          Fn
                            ("*",
                             [Var "c_x";
                              Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
                      Fn
                        ("*",
                         [Var "c_y";
                          Fn
                            ("+",
                             [Fn ("0",[]); Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
                  Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "b_x"; Fn ("1",[])])]);
                  Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "c_x"; Fn ("1",[])])]);
                  Fn ("0",[])])));
        Not (Atom (R ("=",[Fn ("-1",[]); Fn ("0",[])])))]


(* ------------------------------------------------------------------------- *)
(* Try without special coordinates.                                          *)
(* ------------------------------------------------------------------------- *)

[<Test>]
let ``examples 11``() =
    wu simson (simson_vars @ simson_zeros) []
    |> should equal
    <| [Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn
                                    ("*",
                                     [Var "a_y";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "a_y"; Fn ("1",[])])])])]);
                              Fn
                                ("*",
                                 [Var "a_x";
                                  Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "a_x"; Fn ("1",[])])])])]);
                          Fn
                            ("*",
                             [Var "b_x";
                              Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "a_x"; Fn ("-2",[])])]);
                                  Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
                      Fn
                        ("*",
                         [Var "b_y";
                          Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn ("*",[Var "a_y"; Fn ("-2",[])])]);
                              Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
                  Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn
                                    ("*",
                                     [Var "a_y";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "a_y"; Fn ("1",[])])])])]);
                              Fn
                                ("*",
                                 [Var "a_x";
                                  Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "a_x"; Fn ("1",[])])])])]);
                          Fn
                            ("*",
                             [Var "c_x";
                              Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "a_x"; Fn ("-2",[])])]);
                                  Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
                      Fn
                        ("*",
                         [Var "c_y";
                          Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn ("*",[Var "a_y"; Fn ("-2",[])])]);
                              Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
                  Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn
                                    ("*",
                                     [Var "b_x";
                                      Fn
                                        ("+",
                                         [Fn ("0",[]);
                                          Fn ("*",[Var "b_x"; Fn ("1",[])])])])]);
                              Fn
                                ("*",
                                 [Var "b_y";
                                  Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "b_y"; Fn ("1",[])])])])]);
                          Fn
                            ("*",
                             [Var "c_x";
                              Fn
                                ("+",
                                 [Fn
                                    ("+",
                                     [Fn ("0",[]);
                                      Fn ("*",[Var "b_x"; Fn ("-2",[])])]);
                                  Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
                      Fn
                        ("*",
                         [Var "c_y";
                          Fn
                            ("+",
                             [Fn
                                ("+",
                                 [Fn ("0",[]);
                                  Fn ("*",[Var "b_y"; Fn ("-2",[])])]);
                              Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
                  Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn ("0",[]); Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
                      Fn ("*",[Var "b_x"; Fn ("1",[])])]); Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn ("0",[]); Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
                      Fn ("*",[Var "c_x"; Fn ("1",[])])]); Fn ("0",[])])));
        Not
          (Atom
             (R ("=",
                 [Fn
                    ("+",
                     [Fn
                        ("+",
                         [Fn ("0",[]); Fn ("*",[Var "b_x"; Fn ("-1",[])])]);
                      Fn ("*",[Var "c_x"; Fn ("1",[])])]); Fn ("0",[])])));
        Not (Atom (R ("=",[Fn ("-1",[]); Fn ("0",[])])))]


(* ------------------------------------------------------------------------- *)
(* Pappus (Chou's figure 6).                                                 *)
(* ------------------------------------------------------------------------- *)

let private pappus =
    @"collinear(a1,b2,d) /\
    collinear(a2,b1,d) /\
    collinear(a2,b3,e) /\
    collinear(a3,b2,e) /\
    collinear(a1,b3,f) /\
    collinear(a3,b1,f)
    ==> collinear(d,e,f)"
    |> parse

let rec private pappus_vars =
    ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "b3_y";
     "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"]

and private pappus_zeros =
    ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"]

[<Test>]
let ``examples 12``() =
    wu pappus pappus_vars pappus_zeros
    |> should equal
    <| [Not
          (Atom
            (R ("=",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "b1_y";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "a1_x"; Fn ("1", [])])])])]);
                 Fn ("*",
                  [Var "b2_y";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "a2_x"; Fn ("-1", [])])])])]);
               Fn ("0", [])])));
         Not
          (Atom
            (R ("=",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "b1_y";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "a1_x"; Fn ("1", [])])])])]);
                 Fn ("*",
                  [Var "b3_y";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "a3_x"; Fn ("-1", [])])])])]);
               Fn ("0", [])])));
         Not
          (Atom
            (R ("=",
              [Fn ("+",
                [Fn ("+",
                  [Fn ("0", []);
                   Fn ("*",
                    [Var "b2_y";
                     Fn ("+",
                      [Fn ("0", []); Fn ("*", [Var "a2_x"; Fn ("1", [])])])])]);
                 Fn ("*",
                  [Var "b3_y";
                   Fn ("+",
                    [Fn ("0", []); Fn ("*", [Var "a3_x"; Fn ("-1", [])])])])]);
               Fn ("0", [])])));
         Not
          (Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "a1_x"; Fn ("-1", [])])]);
               Fn ("0", [])])));
         Not
          (Atom
            (R ("=",
              [Fn ("+", [Fn ("0", []); Fn ("*", [Var "a2_x"; Fn ("-1", [])])]);
               Fn ("0", [])])))]


(* ------------------------------------------------------------------------- *)
(* The Butterfly (figure 9).                                                 *)
(* ------------------------------------------------------------------------- *)

let private butterfly =
    @"lengths_eq(b,o,a,o) /\ lengths_eq(c,o,a,o) /\ lengths_eq(d,o,a,o) /\
    collinear(a,e,c) /\ collinear(d,e,b) /\
    perpendicular(e,f,o,e) /\
    collinear(a,f,d) /\ collinear(f,e,g) /\ collinear(b,c,g)
    ==> is_midpoint(e,f,g)"
    |> parse

let rec private butterfly_vars =
    ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y";
     "c_y"; "b_y"; "d_x"; "c_x"; "b_x"; "a_x"]

and private butterfly_zeros =
    ["a_y"; "o_x"; "o_y"]

 // This one is costly (too big for laptop, but doable in about 300M)
 // However, it gives exactly the same degenerate conditions as Chou

[<Test; Category("LongRunning")>]
let ``examples 13``() =
    wu butterfly butterfly_vars butterfly_zeros
    |> should equal
    <| [Not
         (Atom
            (R ("=",
                [Fn
                   ("+",
                    [Fn
                       ("+",
                        [Fn
                           ("+",
                            [Fn
                               ("+",
                                [Fn ("0",[]);
                                 Fn
                                   ("*",
                                    [Var "e_x";
                                     Fn
                                       ("+",
                                        [Fn
                                           ("+",
                                            [Fn ("0",[]);
                                             Fn
                                               ("*",[Var "b_y"; Fn ("1",[])])]);
                                         Fn ("*",[Var "c_y"; Fn ("-1",[])])])])]);
                             Fn
                               ("*",
                                [Var "e_y";
                                 Fn
                                   ("+",
                                    [Fn
                                       ("+",
                                        [Fn ("0",[]);
                                         Fn ("*",[Var "b_x"; Fn ("-1",[])])]);
                                     Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
                         Fn
                           ("*",
                            [Var "f_x";
                             Fn
                               ("+",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "b_y"; Fn ("-1",[])])]);
                                 Fn ("*",[Var "c_y"; Fn ("1",[])])])])]);
                     Fn
                       ("*",
                        [Var "f_y";
                         Fn
                           ("+",
                            [Fn
                               ("+",
                                [Fn ("0",[]);
                                 Fn ("*",[Var "b_x"; Fn ("1",[])])]);
                             Fn ("*",[Var "c_x"; Fn ("-1",[])])])])]);
                 Fn ("0",[])])));
       Not
         (Atom
            (R ("=",
                [Fn
                   ("+",
                    [Fn
                       ("+",
                        [Fn
                           ("+",
                            [Fn ("0",[]);
                             Fn
                               ("*",
                                [Var "b_y";
                                 Fn
                                   ("+",
                                    [Fn
                                       ("+",
                                        [Fn ("0",[]);
                                         Fn ("*",[Var "a_x"; Fn ("1",[])])]);
                                     Fn ("*",[Var "c_x"; Fn ("-1",[])])])])]);
                         Fn
                           ("*",
                            [Var "c_y";
                             Fn
                               ("+",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "b_x"; Fn ("1",[])])]);
                                 Fn ("*",[Var "d_x"; Fn ("-1",[])])])])]);
                     Fn
                       ("*",
                        [Var "d_y";
                         Fn
                           ("+",
                            [Fn
                               ("+",
                                [Fn ("0",[]);
                                 Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
                             Fn ("*",[Var "c_x"; Fn ("1",[])])])])]);
                 Fn ("0",[])])));
       Not
         (Atom
            (R ("=",
                [Fn
                   ("+",
                    [Fn
                       ("+",[Fn ("0",[]); Fn ("*",[Var "a_x"; Fn ("1",[])])]);
                     Fn ("*",[Var "c_x"; Fn ("-1",[])])]); Fn ("0",[])])));
       Not
         (Atom
            (R ("=",
                [Fn
                   ("+",
                    [Fn
                       ("+",
                        [Fn ("0",[]);
                         Fn
                           ("*",
                            [Var "e_x";
                             Fn
                               ("+",
                                [Fn
                                   ("+",
                                    [Fn ("0",[]);
                                     Fn ("*",[Var "a_x"; Fn ("-1",[])])]);
                                 Fn ("*",[Var "d_x"; Fn ("1",[])])])])]);
                     Fn
                       ("*",
                        [Var "e_y";
                         Fn
                           ("+",
                            [Fn ("0",[]); Fn ("*",[Var "d_y"; Fn ("1",[])])])])]);
                 Fn ("0",[])])));
       Not
         (Atom
            (R ("=",
                [Fn
                   ("+",
                    [Fn
                       ("+",[Fn ("0",[]); Fn ("*",[Var "e_x"; Fn ("1",[])])]);
                     Fn ("*",[Var "f_x"; Fn ("-1",[])])]); Fn ("0",[])])));
       Not
         (Atom
            (R ("=",
                [Fn ("+",[Fn ("0",[]); Fn ("*",[Var "e_y"; Fn ("1",[])])]);
                 Fn ("0",[])])));
       Not (Atom (R ("=",[Fn ("1",[]); Fn ("0",[])])))]

