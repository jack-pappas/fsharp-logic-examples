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

let private function_congruenceValues : ((string * int) * formula<fol> list)[] = [| 
    (
        // idx 0
        // equal.p001
        ("f", 3),
        [Forall
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
    );
    (
        // idx 1
        // equal.p002
        ("+", 2),
        [Forall
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
    );
    |]

[<TestCase(0, TestName = "equal.p001")>]
[<TestCase(1, TestName = "equal.p002")>]

[<Test>]
let ``function_congruence tests`` idx = 
    let (formula, _) = function_congruenceValues.[idx]
    let (_, result) = function_congruenceValues.[idx]
    function_congruence formula
    |> should equal result

let private equalitizeValues : (string * formula<fol> * string)[] = [| 
    (
        // idx 0
        // Dijkstra 1266a 
        @"(forall x. f(x) ==> g(x)) /\ 
        (exists x. f(x)) /\ 
        (forall x y. g(x) /\ g(y) ==> x = y) 
        ==> forall y. g(y) ==> f(y)",
        Imp
          (And
             (Forall ("x",Atom (R ("=",[Var "x"; Var "x"]))),
              And
                (Forall
                   ("x",
                    Forall
                      ("y",
                       Forall
                         ("z",
                          Imp
                            (And
                               (Atom (R ("=",[Var "x"; Var "y"])),
                                Atom (R ("=",[Var "x"; Var "z"]))),
                             Atom (R ("=",[Var "y"; Var "z"])))))),
                 And
                   (Forall
                      ("x1",
                       Forall
                         ("y1",
                          Imp
                            (Atom (R ("=",[Var "x1"; Var "y1"])),
                             Imp
                               (Atom (R ("f",[Var "x1"])),
                                Atom (R ("f",[Var "y1"])))))),
                    Forall
                      ("x1",
                       Forall
                         ("y1",
                          Imp
                            (Atom (R ("=",[Var "x1"; Var "y1"])),
                             Imp
                               (Atom (R ("g",[Var "x1"])),
                                Atom (R ("g",[Var "y1"]))))))))),
           Imp
             (And
                (Forall
                   ("x",
                    Imp (Atom (R ("f",[Var "x"])),Atom (R ("g",[Var "x"])))),
                 And
                   (Exists ("x",Atom (R ("f",[Var "x"]))),
                    Forall
                      ("x",
                       Forall
                         ("y",
                          Imp
                            (And
                               (Atom (R ("g",[Var "x"])),
                                Atom (R ("g",[Var "y"]))),
                             Atom (R ("=",[Var "x"; Var "y"]))))))),
              Forall
                ("y",Imp (Atom (R ("g",[Var "y"])),Atom (R ("f",[Var "y"])))))),
        @"<<(forall x. x =x) /\ (forall x y z. x =y /\ x =z ==> y =z) /\ " + 
           "(forall x1 y1. x1 =y1 ==> f(x1) ==> f(y1)) /\ " + 
           "(forall x1 y1. x1 =y1 ==> g(x1) ==> g(y1)) " + 
           "==> (forall x. f(x) ==> g(x)) /\ " + 
              "(exists x. f(x)) /\ (forall x y. g(x) /\ g(y) ==> x =y) " + 
              "==> (forall y. g(y) ==> f(y))>>"
    );
    (
        // idx 1
        // Wishnu #1
        @"(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
        (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')",
        Imp
          (And
             (Forall ("x",Atom (R ("=",[Var "x"; Var "x"]))),
              And
                (Forall
                   ("x",
                    Forall
                      ("y",
                       Forall
                         ("z",
                          Imp
                            (And
                               (Atom (R ("=",[Var "x"; Var "y"])),
                                Atom (R ("=",[Var "x"; Var "z"]))),
                             Atom (R ("=",[Var "y"; Var "z"])))))),
                 And
                   (Forall
                      ("x1",
                       Forall
                         ("y1",
                          Imp
                            (Atom (R ("=",[Var "x1"; Var "y1"])),
                             Atom
                               (R ("=",
                                   [Fn ("f",[Var "x1"]); Fn ("f",[Var "y1"])]))))),
                    Forall
                      ("x1",
                       Forall
                         ("y1",
                          Imp
                            (Atom (R ("=",[Var "x1"; Var "y1"])),
                             Atom
                               (R ("=",
                                   [Fn ("g",[Var "x1"]); Fn ("g",[Var "y1"])])))))))),
           Iff
             (Exists
                ("x",
                 And
                   (Atom (R ("=",[Var "x"; Fn ("f",[Fn ("g",[Var "x"])])])),
                    Forall
                      ("x'",
                       Imp
                         (Atom
                            (R ("=",[Var "x'"; Fn ("f",[Fn ("g",[Var "x'"])])])),
                          Atom (R ("=",[Var "x"; Var "x'"])))))),
              Exists
                ("y",
                 And
                   (Atom (R ("=",[Var "y"; Fn ("g",[Fn ("f",[Var "y"])])])),
                    Forall
                      ("y'",
                       Imp
                         (Atom
                            (R ("=",[Var "y'"; Fn ("g",[Fn ("f",[Var "y'"])])])),
                          Atom (R ("=",[Var "y"; Var "y'"])))))))),
        @"<<(forall x. x =x) /\ (forall x y z. x =y /\ x =z ==> y =z) /\ " + 
        "(forall x1 y1. x1 =y1 ==> f(x1) =f(y1)) /\ (forall x1 y1. x1 =y1 ==> g(x1) =g(y1)) " + 
        "==> ((exists x. x =f(g(x)) /\ (forall x'. x' =f(g(x')) ==> x =x')) " + 
        "<=> (exists y. y =g(f(y)) /\ (forall y'. y' =g(f(y')) ==> y =y')))>>"
    );
    |]

[<TestCase(0, TestName = "Dijkstra 1266a")>]
[<TestCase(1, TestName = "Wishnu #1")>]

[<Test>]
let ``equalitize tests`` idx = 
    let (formula, _, _) = equalitizeValues.[idx]
    let (_, astResult, _) = equalitizeValues.[idx]
    let (_, _, stringResult) = equalitizeValues.[idx]
    let result = equalitize (parse formula)
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult

// -----------------------------------------------------------------------------

let private meson002Values : (formula<fol> * int list)[] = [| 
    (
        // idx 0
        // equal.p003
        equalitize (parse @"
            (forall x. f(x) ==> g(x)) /\ 
            (exists x. f(x)) /\ 
            (forall x y. g(x) /\ g(y) ==> x = y) 
            ==> forall y. g(y) ==> f(y)"),
        [6]
    );
    (
        // idx 1
        // equal.p004
        equalitize (parse @"
            (exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
            (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')"),
        [16; 16]
    );
    (
        // idx 2
        // equal.p005
        equalitize (parse @"
            (forall x y z. x * (y * z) = (x * y) * z) /\ 
            (forall x. 1 * x = x) /\ 
            (forall x. i(x) * x = 1) 
            ==> forall x. x * i(x) = 1"),
        [] // Dummy value used as place holder
    );
    (
        // idx 3
        // equal.p006
        equalitize (parse @"
            (forall x y z. x * (y * z) = (x * y) * z) /\ 
            (forall x. 1 * x = x) /\ 
            (forall x. x * 1 = x) /\ 
            (forall x. x * x = 1) 
            ==> forall x y. x * y  = y * x"),
        [] // Dummy value used as place holder
    );
    (
        // idx 4
        // equal.p007
        parse @"
            (forall x. x = x) /\ 
            (forall x y z. x * (y * z) = (x * y) * z) /\ 
            (forall x y z. =((x * y) * z,x * (y * z))) /\ 
            (forall x. 1 * x = x) /\ 
            (forall x. x = 1 * x) /\ 
            (forall x. i(x) * x = 1) /\ 
            (forall x. 1 = i(x) * x) /\ 
            (forall x y. x = y ==> i(x) = i(y)) /\ 
            (forall x y z. x = y ==> x * z = y * z) /\ 
            (forall x y z. x = y ==> z * x = z * y) /\ 
            (forall x y z. x = y /\ y = z ==> x = z) 
            ==> forall x. x * i(x) = 1",
        [] // Dummy value used as place holder
    );
    (
        // idx 5
        // equal.p008
        parse @"
            (forall x y z. axiom(x * (y * z),(x * y) * z)) /\ 
            (forall x y z. axiom((x * y) * z,x * (y * z)) /\ 
            (forall x. axiom(1 * x,x)) /\ 
            (forall x. axiom(x,1 * x)) /\ 
            (forall x. axiom(i(x) * x,1)) /\ 
            (forall x. axiom(1,i(x) * x)) /\ 
            (forall x x'. x = x' ==> cchain(i(x),i(x'))) /\ 
            (forall x x' y y'. x = x' /\ y = y' ==> cchain(x * y,x' * y'))) /\ 
            (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
            (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
            (forall x x' u. x = x' /\ achain(i(x'),u) ==> cchain(i(x),u)) /\ 
            (forall x x' y y' u. 
                x = x' /\ y = y' /\ achain(x' * y',u) ==> cchain(x * y,u)) /\ 
            (forall s t. cchain(s,t) ==> s = t) /\ 
            (forall s t. achain(s,t) ==> s = t) /\ 
            (forall t. t = t) 
            ==> forall x. x * i(x) = 1",
        [] // Dummy value used as place holder
    );
    (
        // idx 6
        // equal.p009
        parse @"
            (forall x y z. axiom(x * (y * z),(x * y) * z)) /\ 
            (forall x y z. axiom((x * y) * z,x * (y * z)) /\ 
            (forall x. axiom(1 * x,x)) /\ 
            (forall x. axiom(x,1 * x)) /\ 
            (forall x. axiom(i(x) * x,1)) /\ 
            (forall x. axiom(1,i(x) * x)) /\ 
            (forall x x'. x = x' ==> cong(i(x),i(x'))) /\ 
            (forall x x' y y'. x = x' /\ y = y' ==> cong(x * y,x' * y'))) /\ 
            (forall s t. axiom(s,t) ==> achain(s,t)) /\ 
            (forall s t. cong(s,t) ==> cchain(s,t)) /\ 
            (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\ 
            (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\ 
            (forall s t. cchain(s,t) ==> s = t) /\ 
            (forall s t. achain(s,t) ==> s = t) /\ 
            (forall t. t = t) 
            ==> forall x. x * i(x) = 1",
        [] // Dummy value used as place holder
    );
    (
        // idx 7
        // equal.p010
        equalitize (parse @"
            forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c"),
        [8]
    );
    (
        // idx 8
        // equal.p011
        parse  @"
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
            ==> f(c) = c",
        [17]
    );
    |]

[<TestCase(0, TestName = "equal.p003")>]
[<TestCase(1, TestName = "equal.p004", Category = "LongRunning")>]
[<TestCase(2, TestName = "equal.p005", Category = "LongRunning")>]
[<TestCase(3, TestName = "equal.p006", Category = "LongRunning")>]
[<TestCase(4, TestName = "equal.p007", Category = "LongRunning")>]
[<TestCase(5, TestName = "equal.p008", Category = "LongRunning")>]
[<TestCase(6, TestName = "equal.p009", Category = "LongRunning")>]
[<TestCase(7, TestName = "equal.p010")>]
[<TestCase(8, TestName = "equal.p011")>]

[<Test>]
let ``meson002 tests`` idx = 
    let (formula, _) = meson002Values.[idx]
    let (_, result) = meson002Values.[idx]
    meson002 formula
    |> should equal result
