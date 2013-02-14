// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.decidable

open FSharpx.Books.AutomatedReasoning.initialization
open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.herbrand
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.resolution
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.decidable

open NUnit.Framework
open FsUnit

let private meson002Values : (string * int list)[] = [| 
    (
        // idx 0
        // decidable.p001
        @"forall x. p(x)",
        [] // Dummy value used as place holder
        // Note: Causes StackOverflowException which NUnit can't handle correctly.
        // Tried using try with around prolog, but NUnit still captures exceptions and aborts.
    );
    (
        // idx 1
        // decidable.p029
        @"(exists x y z. forall u.
            R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=>
        ~((forall x. ~R(x,x)) /\
            (forall x. exists z. R(x,z)) /\
            (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))",
        [1; 3; 9; 1]
    );
    (
        // idx 2
        // decidable.p030
        @"(exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=>
        ~((forall x. ~R(x,x)) /\
            (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))",
        [1; 6; 4]
    );
    (
        // idx 3
        // decidable.p031
        @"~((forall x. ~R(x,x)) /\
            (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))
        ==> ~((forall x. ~R(x,x)) /\
            (forall x. exists z. R(x,z)) /\
            (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))",
        [1; 5]
    );
    |]

[<Test>]
[<TestCase(1, TestName = "decidable.p029")>]
[<TestCase(2, TestName = "decidable.p030")>]
[<TestCase(3, TestName = "decidable.p031")>]
let ``meson002 tests`` idx = 
    let (formula, _) = meson002Values.[idx]
    let (_, result) = meson002Values.[idx]
    meson002 (parse formula)
    |> should equal result

let private aedecideValues : (StackSize * string * bool)[] = [| 
    (
        // idx 0
        // decidable.p006
        // Los #1
        Standard,
        @"(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ 
        (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\ 
        (forall x y. P(x,y) ==> P(y,x)) /\ 
        (forall x y. P(x,y) \/ Q(x,y)) 
        ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
        true
    );
    (
        // idx 1
        // decidable.p008
        Large,
        @"(forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\
        (forall u v w x y z.
            P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
        ==> forall a b c. P(a,b,c) ==> P(b,a,c)",
        true
    );
    (
        // idx 2
        // decidable.p009
        Large,
        @"(forall x. P(x,x,1)) /\
        (forall u v w x y z.
            P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
        ==> forall a b c. P(a,b,c) ==> P(b,a,c)",
        true
    );
    (
        // idx 3
        // decidable.p010
        Large,
        @"(exists x. P(x)) /\ (exists x. G(x))
        ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
            (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
        true
    );
    (
        // idx 4
        // decidable.p011
        // Pelletier #18
        Standard,
        @"exists y. forall x. P(y) ==> P(x)",
        false
    );
    |]

[<Test>]
[<TestCase(0, TestName = "decidable.p006")>]
[<TestCase(1, TestName = "decidable.p008", Category = "LongRunning")>]
[<TestCase(2, TestName = "decidable.p009", Category = "LongRunning")>]
[<TestCase(3, TestName = "decidable.p010")>]
[<TestCase(4, TestName = "decidable.p011",
    ExpectedException = typeof<System.Exception>,
    ExpectedMessage = "Not decidable")>]
let ``aedecide tests`` idx = 
    let (stackSize, _,  _) = aedecideValues.[idx]
    let (_, formula, _) = aedecideValues.[idx]
    let (_, _, result) = aedecideValues.[idx]
    match stackSize with
    | Standard -> 
        aedecide (parse formula)
    | Large ->
        runWithEnlargedStack (fun () -> aedecide (parse formula))
    |> should equal result

let private resolution001Values : (string * bool list)[] = [| 
    (
        // idx 0
        // decidable.p003
        @"forall x. p(x)",
        [] // Dummy value used as place holder
    );
    |]

[<Test>]
[<TestCase(0, TestName = "decidable.p003",
    ExpectedException = typeof<System.Exception>,
    ExpectedMessage = "No proof found")>]
let ``resolution001 tests`` idx = 
    let (formula, _) = resolution001Values.[idx]
    let (_, result) = resolution001Values.[idx]
    resolution001 (parse formula)
    |> should equal result

let private skolemizeValues : (formula<fol> * formula<fol> * string)[] = [| 
    (
        // idx 0
        // decidable.p004
        Not (parse @"
        (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ 
        (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\ 
        (forall x y. P(x,y) ==> P(y,x)) /\ 
        (forall x y. P(x,y) \/ Q(x,y)) 
        ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))"),
        And
          (And
             (Or
                (Or
                   (Not (Atom (R ("P",[Var "x"; Var "y"]))),
                    Not (Atom (R ("P",[Var "y"; Var "z"])))),
                 Atom (R ("P",[Var "x"; Var "z"]))),
              And
                (Or
                   (Or
                      (Not (Atom (R ("Q",[Var "x"; Var "y"]))),
                       Not (Atom (R ("Q",[Var "y"; Var "z"])))),
                    Atom (R ("Q",[Var "x"; Var "z"]))),
                 And
                   (Or
                      (Not (Atom (R ("P",[Var "x"; Var "y"]))),
                       Atom (R ("P",[Var "y"; Var "x"]))),
                    Or
                      (Atom (R ("P",[Var "x"; Var "y"])),
                       Atom (R ("Q",[Var "x"; Var "y"])))))),
           And
             (Not (Atom (R ("P",[Fn ("c_x",[]); Fn ("c_y",[])]))),
              Not (Atom (R ("Q",[Fn ("c_x'",[]); Fn ("c_y'",[])]))))),
        @"<<(((~P(x,y) \/ ~P(y,z)) \/ P(x,z)) /\ ((~Q(x,y) \/ ~Q(y,z)) \/ Q(x,z)) /\ " + 
        "(~P(x,y) \/ P(y,x)) /\ (P(x,y) \/ Q(x,y))) /\ ~P(c_x,c_y) /\ ~Q(c_x',c_y')>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "decidable.p004")>]
let ``skolemize tests`` idx = 
    let (formula, _, _) = skolemizeValues.[idx]
    let (_, astResult, _) = skolemizeValues.[idx]
    let (_, _, stringResult) = skolemizeValues.[idx]
    let result = skolemize formula
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult

let private davisputnamValues : (string * int)[] = [| 
    (
        // idx 0
        // decidable.p005
        @"(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\ 
        (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\ 
        (forall x y. P(x,y) ==> P(y,x)) /\ 
        (forall x y. P(x,y) \/ Q(x,y)) 
        ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))",
        45
    );
    (
        // idx 1
        // decidable.p012
        // Pelletier #18
        @"exists y. forall x. P(y) ==> P(x)",
        2
    );
    |]

[<Test>]
[<TestCase(0, TestName = "decidable.p005")>]
[<TestCase(1, TestName = "decidable.p012")>]
let ``davisputnam tests`` idx = 
    let (formula, _) = davisputnamValues.[idx]
    let (_, result) = davisputnamValues.[idx]
    davisputnam (parse formula)
    |> should equal result

let private pnfValues : (formula<fol> * formula<fol> * string)[] = [| 
    (
        // idx 0
        // decidable.p007
        parse (@"(forall x. p(x)) \/ (exists y. p(y))"),
        Forall
          ("x",
           Exists ("y",Or (Atom (R ("p",[Var "x"])),Atom (R ("p",[Var "y"]))))),
        @"<<forall x. exists y. p(x) \/ p(y)>>"
    );
    (
        // idx 1
        // decidable.p015
        nnf (miniscope(nnf (parse @"(
            forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
            ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"))),
        Forall
          ("z",
           Forall
             ("z'",
              Forall
                ("x",
                 Forall
                   ("y",
                    Exists
                      ("x'",
                       Exists
                         ("w",
                          Exists
                            ("y'",
                             Or
                               (Or
                                  (And
                                     (Atom (R ("P",[Var "x'"])),
                                      And
                                        (Not (Atom (R ("R",[Var "z"]))),
                                         And
                                           (Not (Atom (R ("U",[Var "w"]))),
                                            Atom (R ("Q",[Var "y'"]))))),
                                   Or
                                     (And
                                        (Atom (R ("P",[Var "x'"])),
                                         And
                                           (Not (Atom (R ("R",[Var "z'"]))),
                                            Atom (R ("Q",[Var "w"])))),
                                      And
                                        (Atom (R ("P",[Var "x'"])),
                                         And
                                           (Not (Atom (R ("U",[Var "w"]))),
                                            Atom (R ("Q",[Var "y'"])))))),
                                Or
                                  (Or
                                     (Not (Atom (R ("P",[Var "x"]))),
                                      Not (Atom (R ("Q",[Var "y"])))),
                                   Atom (R ("R",[Var "x'"]))))))))))),
        @"<<forall z z' x y. exists x' w y'. (P(x') /\ ~R(z) /\ ~U(w) /\ Q(y') \/ P(x') /\ " + 
        "~R(z') /\ Q(w) \/ P(x') /\ ~U(w) /\ Q(y')) \/ (~P(x) \/ ~Q(y)) \/ R(x')>>"
    );
    (
        // idx 2
        // decidable.p017
        // Pelletier #34
        nnf(miniscope(nnf (parse @"
        ((exists x. forall y. P(x) <=> P(y)) <=>
            ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
            ((exists x. P(x)) <=> (forall y. P(y))))"))),
        formula<fol>.False,
        @"<<forall y y' y'' y''' y'''' y''''' y'''''' x y''''''' y'''''''' y''''''''' y'''''''''' y''''''''''' y'''''''''''' y''''''''''''' x' x''. exists x''' x'''' y'''''''''''''' x''''' y''''''''''''''' x'''''' x''''''' y'''''''''''''''' x'''''''' y'''''''''''''''''. (((P(x''') /\ ~P(x''')) /\ P(y) /\ (~P(y) \/ P(y)) \/ (P(x''') /\ ~P(x''')) /\ ~P(y') /\ (~P(y') \/ P(y')) \/ (P(x''') /\ ~P(x''')) /\ (~P(y'') \/ P(y'')) \/ P(x''') /\ P(y''') /\ ~P(y''') /\ (~P(y''') \/ P(y''')) \/ P(x''') /\ P(y'''') /\ (~P(y'''') \/ P(y'''')) \/ ~P(x''') /\ P(y''''') /\ ~P(y''''') /\ (~P(y''''') \/ P(y''''')) \/ ~P(x''') /\ ~P(y'''''') /\ (~P(y'''''') \/ P(y''''''))) /\ (Q(x'''') /\ Q(y) \/ ~Q(y') /\ ~Q(x'''')) \/ ((~P(x) \/ P(x)) /\ (~P(x) \/ ~P(x''')) /\ (P(x) \/ P(x'''')) /\ (~P(y'''''''''''''') \/ P(y''''''''''''''))) /\ (Q(x''''') /\ ~Q(y''''''''''''''') \/ ~Q(x) /\ Q(x))) /\ (((Q(x'''''') /\ ~Q(x'''''')) /\ Q(y) /\ (~Q(y) \/ Q(y)) \/ (Q(x'''''') /\ ~Q(x'''''')) /\ ~Q(y') /\ (~Q(y') \/ Q(y')) \/ (Q(x'''''') /\ ~Q(x'''''')) /\ (~Q(y'') \/ Q(y'')) \/ Q(x'''''') /\ Q(y''') /\ ~Q(y''') /\ (~Q(y''') \/ Q(y''')) \/ Q(x'''''') /\ Q(y'''') /\ (~Q(y'''') \/ Q(y'''')) \/ ~Q(x'''''') /\ Q(y''''') /\ ~Q(y''''') /\ (~Q(y''''') \/ Q(y''''')) \/ ~Q(x'''''') /\ ~Q(y'''''') /\ (~Q(y'''''') \/ Q(y''''''))) /\ (P(x''''''') /\ P(y) \/ ~P(y') /\ ~P(x''''''')) \/ ((~Q(x) \/ Q(x)) /\ (~Q(x) \/ ~Q(x'''''')) /\ (Q(x) \/ Q(x''''''')) /\ (~Q(y'''''''''''''''') \/ Q(y''''''''''''''''))) /\ (P(x'''''''') /\ ~P(y''''''''''''''''') \/ ~P(x) /\ P(x))) \/ (((P(x''') /\ ~P(x''')) /\ P(y''''''') /\ (~P(y''''''') \/ P(y''''''')) \/ (P(x''') /\ ~P(x''')) /\ ~P(y'''''''') /\ (~P(y'''''''') \/ P(y'''''''')) \/ (P(x''') /\ ~P(x''')) /\ (~P(y''''''''') \/ P(y''''''''')) \/ P(x''') /\ P(y'''''''''') /\ ~P(y'''''''''') /\ (~P(y'''''''''') \/ P(y'''''''''')) \/ P(x''') /\ P(y''''''''''') /\ (~P(y''''''''''') \/ P(y''''''''''')) \/ ~P(x''') /\ P(y'''''''''''') /\ ~P(y'''''''''''') /\ (~P(y'''''''''''') \/ P(y'''''''''''')) \/ ~P(x''') /\ ~P(y''''''''''''') /\ (~P(y''''''''''''') \/ P(y'''''''''''''))) /\ (Q(x'''') /\ ~Q(y'''''''''''''') \/ ~Q(y''''''') /\ Q(y''''''')) \/ ((~P(x') \/ P(x')) /\ (~P(x') \/ ~P(x''')) /\ (P(x') \/ P(x'''')) /\ (~P(y'''''''''''''') \/ P(y''''''''''''''))) /\ (Q(x''''') /\ Q(x') \/ ~Q(x'') /\ ~Q(x'''''))) /\ (((Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\ Q(y''''''') /\ (~Q(y''''''') \/ Q(y''''''')) \/ (Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\ ~Q(y'''''''') /\ (~Q(y'''''''') \/ Q(y'''''''')) \/ (Q(y''''''''''''''') /\ ~Q(y''''''''''''''')) /\ (~Q(y''''''''') \/ Q(y''''''''')) \/ Q(y''''''''''''''') /\ Q(y'''''''''') /\ ~Q(y'''''''''') /\ (~Q(y'''''''''') \/ Q(y'''''''''')) \/ Q(y''''''''''''''') /\ Q(y''''''''''') /\ (~Q(y''''''''''') \/ Q(y''''''''''')) \/ ~Q(y''''''''''''''') /\ Q(y'''''''''''') /\ ~Q(y'''''''''''') /\ (~Q(y'''''''''''') \/ Q(y'''''''''''')) \/ ~Q(y''''''''''''''') /\ ~Q(y''''''''''''') /\ (~Q(y''''''''''''') \/ Q(y'''''''''''''))) /\ (P(x'''''') /\ ~P(x''''''') \/ ~P(y''''''') /\ P(y''''''')) \/ ((~Q(x') \/ Q(x')) /\ (~Q(x') \/ ~Q(y''''''''''''''')) /\ (Q(x') \/ Q(x'''''')) /\ (~Q(x''''''') \/ Q(x'''''''))) /\ (P(y'''''''''''''''') /\ P(x') \/ ~P(x'') /\ ~P(y'''''''''''''''')))>>"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "decidable.p007")>]
[<TestCase(1, TestName = "decidable.p015")>]
let ``pnf 1 tests`` idx = 
    let (formula, _, _) = pnfValues.[idx]
    let (_, astResult, _) = pnfValues.[idx]
    let (_, _, stringResult) = pnfValues.[idx]
    let result = pnf formula
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult

[<Test>]
[<TestCase(2, TestName = "decidable.p017")>]
let ``pnf 2 tests`` idx = 
    let (formula, _, _) = pnfValues.[idx]
    let (_, astResult, _) = pnfValues.[idx]
    let (_, _, stringResult) = pnfValues.[idx]
    let result = pnf formula
    sprint_fol_formula result
    |> should equal stringResult

let private wangValues : (string * bool)[] = [| 
    (
        // idx 0
        // decidable.p016
        // Pelletier #20
        @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
        true
    );
    |]

[<Test>]
[<TestCase(0, TestName = "Pelletier #20")>]
let ``wang tests`` idx = 
    let (formula, _) = wangValues.[idx]
    let (_, result) = wangValues.[idx]
    wang (parse formula)
    |> should equal result

let private decide_fmpValues : (string * bool)[] = [| 
    (
        // idx 0
        // decidable.p024
        @"(forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)",
        true
    );
    (
        // idx 1
        // decidable.p025
        @"(forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)",
        false
    );
    (
        // idx 2
        // decidable.p026
        @"~((forall x. ~R(x,x)) /\ 
        (forall x. exists z. R(x,z)) /\ 
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))",
        false // Dummy value used as place holder
        // Note: Causes StackOverflowException which NUnit can't handle correctly.
    );
    |]

[<Test>]
[<TestCase(0, TestName = "decidable.p024")>]
[<TestCase(1, TestName = "decidable.p025")>]
let ``decide_fmp tests`` idx = 
    let (formula, _) = decide_fmpValues.[idx]
    let (_, result) = decide_fmpValues.[idx]
    decide_fmp (parse formula)
    |> should equal result

// ----------------------------------------------------------------------


let private decide_monadicValues : (string * bool)[] = [| 
    (
        // idx 0
        // decidable.p027
        // Pelletier #34
        @"((exists x. forall y. P(x) <=> P(y)) <=>
            ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
            ((exists x. forall y. Q(x) <=> Q(y)) <=>
        ((exists x. P(x)) <=> (forall y. P(y))))",
        true
    );
    (
        // idx 1
        // decidable.p028
        // Pelletier #20
        @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
        false // Dummy value used as place holder
        // Note: Causes StackOverflowException which NUnit can't handle correctly.
    );
    |]

[<Test>]
[<TestCase(0, TestName = "Pelletier #34")>]
let ``decide_monadic tests`` idx = 
    let (formula, _) = decide_monadicValues.[idx]
    let (_, result) = decide_monadicValues.[idx]
    decide_monadic (parse formula)
    |> should equal result

// =======================================================================

