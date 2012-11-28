// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.equal

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal

open NUnit.Framework
open FsUnit

// pg. 239
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// equal.p001
[<Test>]
let ``congruence 1``() =
    function_congruence ("f", 3)
    |> should equal [Forall
     ("x1",
      Forall
        ("x2",
         Forall
           ("x3",
            Forall
              ("y1",
               Forall
                 ("y2",
                  Forall
                    ("y3",
                     Imp
                       (And
                          (Atom (R ("=",[Var "x1"; Var "y1"])),
                           And
                             (Atom (R ("=",[Var "x2"; Var "y2"])),
                              Atom (R ("=",[Var "x3"; Var "y3"])))),
                        Atom
                          (R ("=",
                              [Fn ("f",[Var "x1"; Var "x2"; Var "x3"]);
                               Fn ("f",[Var "y1"; Var "y2"; Var "y3"])])))))))))]

// equal.p002
[<Test>]
let ``congruence 2``() =
    function_congruence ("+", 2)
    |> should equal [Forall
     ("x1",
      Forall
        ("x2",
         Forall
           ("y1",
            Forall
              ("y2",
               Imp
                 (And
                    (Atom (R ("=",[Var "x1"; Var "y1"])),
                     Atom (R ("=",[Var "x2"; Var "y2"]))),
                  Atom
                    (R ("=",
                        [Fn ("+",[Var "x1"; Var "x2"]);
                         Fn ("+",[Var "y1"; Var "y2"])])))))))]

// pg. 241
// ------------------------------------------------------------------------- //
// A simple example (see EWD1266a and the application to Morley's theorem).  //
// ------------------------------------------------------------------------- //

// equal.p003
// Dijkstra 1266a 
[<Test>]
let ``meson002 1``() =
    equalitize (parse @"
        (forall x. f(x) ==> g(x)) /\ 
        (exists x. f(x)) /\ 
        (forall x y. g(x) /\ g(y) ==> x = y) 
        ==> forall y. g(y) ==> f(y)")
    |> meson002
    |> should equal [6]

// Dijkstra 1266a
// equal.p003
[<Test>]
let ``Dijkstra 1266a``() =
    let ewd = 
        equalitize (parse @"
        (forall x. f(x) ==> g(x)) /\ 
        (exists x. f(x)) /\ 
        (forall x y. g(x) /\ g(y) ==> x = y) 
        ==> forall y. g(y) ==> f(y)")
    meson002 ewd
    |> should equal [6]

// equal.p004
// Wishnu #1
[<Test>]
let ``Wishnu #1``() =
    let wishnu =
        equalitize (parse @"
            (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
            (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')")
    meson002 wishnu
    |> should equal [16; 16]

// equal.p010
[<Test>]
let ``meson002 2``() =
    equalitize (parse @"forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c")
    |> meson002
    |> should equal [8]

// equal.p011
[<Test>]
let ``meson002 3``() =
    (parse @"
    axiom(f(f(f(f(f(c))))),c) /\ 
    axiom(c,f(f(f(f(f(c)))))) /\ 
    axiom(f(f(f(c))),c) /\ 
    axiom(c,f(f(f(c)))) /\ 
    (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
    (forall s t. cong(s,t) ==> cchain(s,t)) /\ 
    (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
    (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\ 
    (forall s t. cchain(s,t) ==> s = t) /\ 
    (forall s t. achain(s,t) ==> s = t) /\ 
    (forall t. t = t) /\ 
    (forall x y. x = y ==> cong(f(x),f(y))) 
    ==> f(c) = c")
    |> meson002
    |> should equal [17]
