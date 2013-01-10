// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.lcffol

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop
open FSharpx.Books.AutomatedReasoning.lcffol

open NUnit.Framework
open FsUnit

let private lcfrefuteValues : (string * thm * string)[] = [| 
    (
        // idx 0
        // lcffol.p001  
        @"p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))",
        Imp
            (And
                (Atom (R ("p",[Fn ("1",[])])),
                And
                    (Not (Atom (R ("q",[Fn ("1",[])]))),
                    Forall
                        ("x",
                        Imp (Atom (R ("p",[Var "x"])),Atom (R ("q",[Var "x"])))))),
                formula<fol>.False),
        @"|- p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x)) ==> false"
    );
    (
         // idx 1
        // lcffol.p002 
        @"(exists x. ~p(x)) /\ (forall x. p(x))",
        Imp
            (And
                (Exists ("x",Not (Atom (R ("p",[Var "x"])))),
                Forall ("x",Atom (R ("p",[Var "x"])))),
                Imp
                    (Imp
                        (Not (Not (Atom (R ("p",[Fn ("f_1",[])])))),
                        Forall ("x",Not (Not (Atom (R ("p",[Var "x"])))))),formula<fol>.False)),
        @"|- (exists x. ~p(x)) /\ (forall x. p(x)) ==> (~(~p(f_1)) ==> (forall x. ~(~p(x)))) ==> false"
    );
    |]

// lcffol.p001
[<TestCase(0, TestName = "lcffol.p001")>]

// lcffol.p002
[<TestCase(1, TestName = "lcffol.p002")>]

[<Test>]
let ``lcfrefute ast tests`` idx = 
    let (formula, _, _) = lcfrefuteValues.[idx]
    let (_, ast_result, _) = lcfrefuteValues.[idx]
    lcfrefute (parse formula) 1 simpcont
    |> should equal ast_result

// lcffol.p001
[<TestCase(0, TestName = "lcffol.p001")>]

// lcffol.p002
[<TestCase(1, TestName = "lcffol.p002")>]

[<Test>]
let ``lcfrefute pp tests`` idx = 
    let (formula, _, _) = lcfrefuteValues.[idx]
    let (_, _, pretty_printer_result) = lcfrefuteValues.[idx]
    lcfrefute (parse formula) 1 simpcont
    |> sprint_thm
    |> should equal pretty_printer_result

let private lcfValues : (string * thm * string )[] = [| 
    (
        // idx 0
        // Pelletier #01
        // lcffol.p005  
        // lcffol.p022
        @"p ==> q <=> ~q ==> ~p",
        Iff
            (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),
             Imp (Not (Atom (R ("q",[]))),Not (Atom (R ("p",[]))))),
        @"|- p ==> q <=> ~q ==> ~p"
    );
    (
        // idx 1
        // Pelletier #02
        // lcffol.p006  
        // lcffol.p023
        @"~ ~p <=> p",
        Iff (Not (Not (Atom (R ("p",[])))),Atom (R ("p",[]))),
        @"|- ~(~p) <=> p"
    );
    (
        // idx 2
        // Pelletier #03
        // lcffol.p007  
        // lcffol.p024
        @"~(p ==> q) ==> q ==> p",
        Imp
            (Not (Imp (Atom (R ("p",[])),Atom (R ("q",[])))),
            Imp (Atom (R ("q",[])),Atom (R ("p",[])))),
        @"|- ~(p ==> q) ==> q ==> p"
    );
    (
        // idx 3
        // Pelletier #04
        // lcffol.p008  
        // lcffol.p025
        @"~p ==> q <=> ~q ==> p",
        Iff
            (Imp (Not (Atom (R ("p",[]))),Atom (R ("q",[]))),
            Imp (Not (Atom (R ("q",[]))),Atom (R ("p",[])))),
        @"|- ~p ==> q <=> ~q ==> p"
    );
    (
        // idx 4
        // Pelletier #05
        // lcffol.p009 
        // lcffol.p026
        @"(p \/ q ==> p \/ r) ==> p \/ (q ==> r)",
        Imp
            (Imp
                (Or (Atom (R ("p",[])),Atom (R ("q",[]))),
                Or (Atom (R ("p",[])),Atom (R ("r",[])))),
            Or (Atom (R ("p",[])),Imp (Atom (R ("q",[])),Atom (R ("r",[]))))),
        @"|- (p \/ q ==> p \/ r) ==> p \/ (q ==> r)"
    );
    (
        // idx 5
        // Pelletier #06
        // lcffol.p010  
        // lcffol.p027
        @"p \/ ~p",
        Or (Atom (R ("p",[])),Not (Atom (R ("p",[])))),
        @"|- p \/ ~p"
    );
    (
        // idx 6
        // Pelletier #07
        // lcffol.p011  
        // lcffol.p028
        @"p \/ ~ ~ ~p",
        Or (Atom (R ("p",[])),Not (Not (Not (Atom (R ("p",[])))))),
        @"|- p \/ ~(~(~p))"
    );
    (
        // idx 7
        // Pelletier #08
        // lcffol.p012  
        // lcffol.p029
        @"((p ==> q) ==> p) ==> p",
        Imp
            (Imp (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),Atom (R ("p",[]))),
            Atom (R ("p",[]))),
        @"|- ((p ==> q) ==> p) ==> p"
    );
    (
        // idx 8
        // Pelletier #09
        // lcffol.p013  
        // lcffol.p030
        @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)",
        Imp
            (And
                (Or (Atom (R ("p",[])),Atom (R ("q",[]))),
                And
                    (Or (Not (Atom (R ("p",[]))),Atom (R ("q",[]))),
                    Or (Atom (R ("p",[])),Not (Atom (R ("q",[])))))),
            Not (Or (Not (Atom (R ("q",[]))),Not (Atom (R ("q",[])))))),
        @"|- (p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)"
    );
    (
        // idx 9
        // Pelletier #10
        // lcffol.p014  
        // lcffol.p031
        @"(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)",
        Imp
            (And
                (Imp (Atom (R ("q",[])),Atom (R ("r",[]))),
                And
                    (Imp
                        (Atom (R ("r",[])),
                        And (Atom (R ("p",[])),Atom (R ("q",[])))),
                    Imp
                        (Atom (R ("p",[])),
                        And (Atom (R ("q",[])),Atom (R ("r",[])))))),
            Iff (Atom (R ("p",[])),Atom (R ("q",[])))),
        @"|- (q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)"
    );
    (
        // idx 10
        // Pelletier #11
        // lcffol.p015  
        // lcffol.p032
        @"p <=> p",
        Iff (Atom (R ("p",[])),Atom (R ("p",[]))),
        @"|- p <=> p"
    );
    (
        // idx 11
        // Pelletier #12
        // lcffol.p016  
        // lcffol.p033
        @"((p <=> q) <=> r) <=> (p <=> (q <=> r))",
        Iff
            (Iff (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),Atom (R ("r",[]))),
            Iff (Atom (R ("p",[])),Iff (Atom (R ("q",[])),Atom (R ("r",[]))))),
        @"|- ((p <=> q) <=> r) <=> p <=> q <=> r"
    );
    (
        // idx 12
        // Pelletier #13
        // lcffol.p017  
        // lcffol.p034
        @"p \/ q /\ r <=> (p \/ q) /\ (p \/ r)",
        Iff
            (Or (Atom (R ("p",[])),And (Atom (R ("q",[])),Atom (R ("r",[])))),
            And
                (Or (Atom (R ("p",[])),Atom (R ("q",[]))),
                Or (Atom (R ("p",[])),Atom (R ("r",[]))))),
        @"|- p \/ q /\ r <=> (p \/ q) /\ (p \/ r)"
    );
    (
        // idx 13
        // Pelletier #14
        // lcffol.p018  
        // lcffol.p035
        @"(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)",
        Iff
            (Iff (Atom (R ("p",[])),Atom (R ("q",[]))),
            And
                (Or (Atom (R ("q",[])),Not (Atom (R ("p",[])))),
                Or (Not (Atom (R ("q",[]))),Atom (R ("p",[]))))),
        @"|- (p <=> q) <=> (q \/ ~p) /\ (~q \/ p)"
    );
    (
        // idx 14
        // Pelletier #15
        // lcffol.p019  
        // lcffol.p036
        @"p ==> q <=> ~p \/ q",
        Iff
            (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),
            Or (Not (Atom (R ("p",[]))),Atom (R ("q",[])))),
        @"|- p ==> q <=> ~p \/ q"
    );
    (
        // idx 15
        // Pelletier #16
        // lcffol.p020  
        // lcffol.p037
        @"(p ==> q) \/ (q ==> p)",
        Or
            (Imp (Atom (R ("p",[])),Atom (R ("q",[]))),
            Imp (Atom (R ("q",[])),Atom (R ("p",[])))),
        @"|- (p ==> q) \/ (q ==> p)"
    );
    (
        // idx 16
        // Pelletier #17
        // lcffol.p038
        @"p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)",
        Iff
            (Imp
                (And
                    (Atom (R ("p",[])),Imp (Atom (R ("q",[])),Atom (R ("r",[])))),
                Atom (R ("s",[]))),
            And
                (Or
                    (Not (Atom (R ("p",[]))),
                    Or (Atom (R ("q",[])),Atom (R ("s",[])))),
                Or
                    (Not (Atom (R ("p",[]))),
                    Or (Not (Atom (R ("r",[]))),Atom (R ("s",[])))))),
        @"|- p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)"
    );
    (
        // idx 17
        // Pelletier #18
        // lcffol.p039
        @"exists y. forall x. P(y) ==> P(x)",
        Exists
            ("y",
            Forall
                ("x",Imp (Atom (R ("P",[Var "y"])),Atom (R ("P",[Var "x"]))))),
        @"|- exists y. forall x. P(y) ==> P(x)"
    );
    (
        // idx 18
        // Pelletier #19
        // lcffol.p040
        @"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)",
        Exists
            ("x",
            Forall
                ("y",
                Forall
                    ("z",
                    Imp
                        (Imp (Atom (R ("P",[Var "y"])),Atom (R ("Q",[Var "z"]))),
                        Imp (Atom (R ("P",[Var "x"])),Atom (R ("Q",[Var "x"]))))))),
        @"|- exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)"
    );
    (
        // idx 19
        // Pelletier #20
        // lcffol.p041
        @"(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
        ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))",
        Imp
            (Forall
                ("x",
                Forall
                    ("y",
                    Exists
                        ("z",
                        Forall
                            ("w",
                            Imp
                                (And
                                    (Atom (R ("P",[Var "x"])),Atom (R ("Q",[Var "y"]))),
                                And
                                    (Atom (R ("R",[Var "z"])),Atom (R ("U",[Var "w"])))))))),
            Imp
                (Exists
                    ("x",
                    Exists
                        ("y",
                        And (Atom (R ("P",[Var "x"])),Atom (R ("Q",[Var "y"]))))),
                Exists ("z",Atom (R ("R",[Var "z"]))))),
        @"|- (forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))"
    );
    (
        // idx 20
        // Pelletier #21
        // lcffol.p042
        @"(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
        ==> (exists x. P <=> Q(x))",
        Imp
            (And
                (Exists ("x",Imp (Atom (R ("P",[])),Atom (R ("Q",[Var "x"])))),
                Exists ("x",Imp (Atom (R ("Q",[Var "x"])),Atom (R ("P",[]))))),
            Exists ("x",Iff (Atom (R ("P",[])),Atom (R ("Q",[Var "x"]))))),
        @"|- (exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))"
    );
    (
        // idx 21
        // Pelletier #22
        // lcffol.p043
        @"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))",
        Imp
            (Forall ("x",Iff (Atom (R ("P",[])),Atom (R ("Q",[Var "x"])))),
            Iff (Atom (R ("P",[])),Forall ("x",Atom (R ("Q",[Var "x"]))))),
        @"|- (forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))"
    );
    (
        // idx 22
        // Pelletier #23
        // lcffol.p044
        @"(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))",
        Iff
            (Forall ("x",Or (Atom (R ("P",[])),Atom (R ("Q",[Var "x"])))),
            Or (Atom (R ("P",[])),Forall ("x",Atom (R ("Q",[Var "x"]))))),
        @"|- (forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))"
    );
    (
        // idx 23
        // Pelletier #24
        // lcffol.p045
        @"~(exists x. U(x) /\ Q(x)) /\
        (forall x. P(x) ==> Q(x) \/ R(x)) /\
        ~(exists x. P(x) ==> (exists x. Q(x))) /\
        (forall x. Q(x) /\ R(x) ==> U(x)) ==>
        (exists x. P(x) /\ R(x))",
        Imp
            (And
                (Not
                    (Exists
                    ("x",
                        And (Atom (R ("U",[Var "x"])),Atom (R ("Q",[Var "x"]))))),
                And
                    (Forall
                    ("x",
                        Imp
                            (Atom (R ("P",[Var "x"])),
                                Or (Atom (R ("Q",[Var "x"])),Atom (R ("R",[Var "x"]))))),
                    And
                        (Not
                            (Exists
                                ("x",
                                Imp
                                    (Atom (R ("P",[Var "x"])),
                                    Exists ("x",Atom (R ("Q",[Var "x"])))))),
                            Forall
                                ("x",
                                Imp
                                    (And
                                        (Atom (R ("Q",[Var "x"])),Atom (R ("R",[Var "x"]))),
                                    Atom (R ("U",[Var "x"]))))))),
            Exists
                ("x",And (Atom (R ("P",[Var "x"])),Atom (R ("R",[Var "x"]))))),
        @"|- ~(exists x. U(x) /\ Q(x)) /\ (forall x. P(x) ==> Q(x) \/ R(x)) /\ ~(exists x. P(x) ==> (exists x. Q(x))) /\ (forall x. Q(x) /\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))"
    );
    (
        // idx 24
        // Pelletier #25
        // lcffol.p046
        @"(exists x. P(x)) /\
        (forall x. U(x) ==> ~G(x) /\ R(x)) /\
        (forall x. P(x) ==> G(x) /\ U(x)) /\
        ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
        ==> (exists x. Q(x) /\ P(x))",
        Imp
            (And
               (Exists ("x",Atom (R ("P",[Var "x"]))),
                And
                    (Forall
                        ("x",
                        Imp
                            (Atom (R ("U",[Var "x"])),
                            And
                                (Not (Atom (R ("G",[Var "x"]))),
                                Atom (R ("R",[Var "x"]))))),
                    And
                        (Forall
                            ("x",
                            Imp
                                (Atom (R ("P",[Var "x"])),
                                And
                                    (Atom (R ("G",[Var "x"])),Atom (R ("U",[Var "x"]))))),
                        Or
                            (Forall
                                ("x",
                                Imp
                                    (Atom (R ("P",[Var "x"])),Atom (R ("Q",[Var "x"])))),
                                Exists
                                    ("x",
                                    And
                                        (Atom (R ("Q",[Var "x"])),Atom (R ("P",[Var "x"])))))))),
            Exists
                ("x",And (Atom (R ("Q",[Var "x"])),Atom (R ("P",[Var "x"]))))),
        @"|- (exists x. P(x)) /\ (forall x. U(x) ==> ~G(x) /\ R(x)) /\ (forall x. P(x) ==> G(x) /\ U(x)) /\ ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==> (exists x. Q(x) /\ P(x))"
    );
    (
        // idx 25
        // Pelletier #26
        // lcffol.p047
        @"((exists x. P(x)) <=> (exists x. Q(x))) /\
        (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x))
        <=> (forall x. Q(x) ==> U(x)))",
        Imp
            (And
                (Iff
                    (Exists ("x",Atom (R ("P",[Var "x"]))),
                    Exists ("x",Atom (R ("Q",[Var "x"])))),
                Forall
                        ("x",
                        Forall
                                ("y",
                                Imp
                                    (And (Atom (R ("P",[Var "x"])),Atom (R ("Q",[Var "y"]))),
                                        Iff (Atom (R ("R",[Var "x"])),Atom (R ("U",[Var "y"]))))))),
            Iff
                (Forall
                    ("x",Imp (Atom (R ("P",[Var "x"])),Atom (R ("R",[Var "x"])))),
                Forall
                    ("x",Imp (Atom (R ("Q",[Var "x"])),Atom (R ("U",[Var "x"])))))),
        @"|- ((exists x. P(x)) <=> (exists x. Q(x))) /\ (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))"
    );
    (
        // idx 26
        // Pelletier #27
        // lcffol.p048
        @"(exists x. P(x) /\ ~Q(x)) /\
        (forall x. P(x) ==> R(x)) /\
        (forall x. U(x) /\ V(x) ==> P(x)) /\
        (exists x. R(x) /\ ~Q(x))
        ==> (forall x. V(x) ==> ~R(x))
            ==> (forall x. U(x) ==> ~V(x))",
        Imp
          (And
             (Exists
                ("x",
                 And (Atom (R ("P",[Var "x"])),Not (Atom (R ("Q",[Var "x"]))))),
              And
                (Forall
                   ("x",
                    Imp (Atom (R ("P",[Var "x"])),Atom (R ("R",[Var "x"])))),
                 And
                   (Forall
                      ("x",
                       Imp
                         (And
                            (Atom (R ("U",[Var "x"])),Atom (R ("V",[Var "x"]))),
                          Atom (R ("P",[Var "x"])))),
                    Exists
                      ("x",
                       And
                         (Atom (R ("R",[Var "x"])),
                          Not (Atom (R ("Q",[Var "x"])))))))),
           Imp
             (Forall
                ("x",
                 Imp (Atom (R ("V",[Var "x"])),Not (Atom (R ("R",[Var "x"]))))),
              Forall
                ("x",
                 Imp (Atom (R ("U",[Var "x"])),Not (Atom (R ("V",[Var "x"]))))))),
        @"|- (exists x. P(x) /\ ~Q(x)) /\ (forall x. P(x) ==> R(x)) /\ (forall x. U(x) /\ V(x) ==> P(x)) /\ (exists x. R(x) /\ ~Q(x)) ==> (forall x. V(x) ==> ~R(x)) ==> (forall x. U(x) ==> ~V(x))"
    );
    (
        // idx 27
        // Pelletier #28
        // lcffol.p049
        @"(forall x. P(x) ==> (forall x. Q(x))) /\
        ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
        ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
        (forall x. P(x) /\ L(x) ==> M(x))",
        Imp
            (And
                (Forall
                    ("x",
                    Imp
                         (Atom (R ("P",[Var "x"])),
                          Forall ("x",Atom (R ("Q",[Var "x"]))))),
                And
                    (Imp
                        (Forall
                        ("x",
                            Or (Atom (R ("Q",[Var "x"])),Atom (R ("R",[Var "x"])))),
                        Exists
                            ("x",
                            And (Atom (R ("Q",[Var "x"])),Atom (R ("R",[Var "x"]))))),
                    Imp
                        (Exists ("x",Atom (R ("R",[Var "x"]))),
                        Forall
                            ("x",
                            Imp (Atom (R ("L",[Var "x"])),Atom (R ("M",[Var "x"]))))))),
            Forall
                ("x",
                Imp
                    (And (Atom (R ("P",[Var "x"])),Atom (R ("L",[Var "x"]))),
                    Atom (R ("M",[Var "x"]))))),
        @"|- (forall x. P(x) ==> (forall x. Q(x))) /\ ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\ ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> (forall x. P(x) /\ L(x) ==> M(x))"
    );
    (
        // idx 28
        // Pelletier #29
        // lcffol.p050
        @"(exists x. P(x)) /\ (exists x. G(x)) ==>
        ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))",
        Imp
            (And
                (Exists ("x",Atom (R ("P",[Var "x"]))),
                Exists ("x",Atom (R ("G",[Var "x"])))),
            Iff
               (And
                    (Forall
                        ("x",
                        Imp (Atom (R ("P",[Var "x"])),Atom (R ("H",[Var "x"])))),
                    Forall
                        ("x",
                        Imp (Atom (R ("G",[Var "x"])),Atom (R ("J",[Var "x"]))))),
                Forall
                    ("x",
                    Forall
                        ("y",
                        Imp
                            (And (Atom (R ("P",[Var "x"])),Atom (R ("G",[Var "y"]))),
                            And (Atom (R ("H",[Var "x"])),Atom (R ("J",[Var "y"])))))))),
        @"|- (exists x. P(x)) /\ (exists x. G(x)) ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=> (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))"
    );
    (
        // idx 29
        // Pelletier #30
        // lcffol.p051
        @"(forall x. P(x) \/ G(x) ==> ~H(x)) /\
        (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
        ==> (forall x. U(x))",
        Imp
            (And
               (Forall
                    ("x",
                    Imp
                        (Or (Atom (R ("P",[Var "x"])),Atom (R ("G",[Var "x"]))),
                        Not (Atom (R ("H",[Var "x"]))))),
                Forall
                    ("x",
                    Imp
                        (Imp
                            (Atom (R ("G",[Var "x"])),Not (Atom (R ("U",[Var "x"])))),
                            And (Atom (R ("P",[Var "x"])),Atom (R ("H",[Var "x"])))))),
            Forall ("x",Atom (R ("U",[Var "x"])))),
        @"|- (forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==> (forall x. U(x))"
    );
    (
        // idx 30
        // Pelletier #31
        // lcffol.p052
        @"~(exists x. P(x) /\ (G(x) \/ H(x))) /\
        (exists x. Q(x) /\ P(x)) /\
        (forall x. ~H(x) ==> J(x))
        ==> (exists x. Q(x) /\ J(x))",
        Imp
            (And
               (Not
                  (Exists
                        ("x",
                        And
                            (Atom (R ("P",[Var "x"])),
                            Or (Atom (R ("G",[Var "x"])),Atom (R ("H",[Var "x"])))))),
                And
                    (Exists
                        ("x",
                        And (Atom (R ("Q",[Var "x"])),Atom (R ("P",[Var "x"])))),
                    Forall
                        ("x",
                        Imp
                            (Not (Atom (R ("H",[Var "x"]))),Atom (R ("J",[Var "x"])))))),
            Exists
                ("x",And (Atom (R ("Q",[Var "x"])),Atom (R ("J",[Var "x"]))))),
        @"|- ~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\ (forall x. ~H(x) ==> J(x)) ==> (exists x. Q(x) /\ J(x))"
    );
    (
        // idx 31
        // Pelletier #32
        // lcffol.p053
        @"(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
        (forall x. Q(x) /\ H(x) ==> J(x)) /\
        (forall x. R(x) ==> H(x))
        ==> (forall x. P(x) /\ R(x) ==> J(x))",
        Imp
            (And
               (Forall
                    ("x",
                    Imp
                        (And
                            (Atom (R ("P",[Var "x"])),
                                Or (Atom (R ("G",[Var "x"])),Atom (R ("H",[Var "x"])))),
                            Atom (R ("Q",[Var "x"])))),
                And
                    (Forall
                        ("x",
                        Imp
                            (And (Atom (R ("Q",[Var "x"])),Atom (R ("H",[Var "x"]))),
                                Atom (R ("J",[Var "x"])))),
                    Forall
                        ("x",
                        Imp (Atom (R ("R",[Var "x"])),Atom (R ("H",[Var "x"])))))),
            Forall
                ("x",
                Imp
                  (And (Atom (R ("P",[Var "x"])),Atom (R ("R",[Var "x"]))),
                   Atom (R ("J",[Var "x"]))))),
        @"|- (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ (forall x. Q(x) /\ H(x) ==> J(x)) /\ (forall x. R(x) ==> H(x)) ==> (forall x. P(x) /\ R(x) ==> J(x))"
    );
    (
        // idx 32
        // Pelletier #33
        // lcffol.p054
        @"(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
        (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))",
        Iff
            (Forall
                ("x",
                Imp
                    (And
                        (Atom (R ("P",[Var "a"])),
                        Imp (Atom (R ("P",[Var "x"])),Atom (R ("P",[Var "b"])))),
                    Atom (R ("P",[Var "c"])))),
            And
                (Forall
                    ("x",
                    Imp
                        (Atom (R ("P",[Var "a"])),
                        Or (Atom (R ("P",[Var "x"])),Atom (R ("P",[Var "c"]))))),
                Imp
                    (Atom (R ("P",[Var "a"])),
                    Imp (Atom (R ("P",[Var "b"])),Atom (R ("P",[Var "c"])))))),
        @"|- (forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=> (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))"
    );
    (
        // idx 33
        // Pelletier #34
        // Ran for 9.5 hours with out completion.
        // lcffol.p055
        @"((exists x. forall y. P(x) <=> P(y)) <=>
            ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
        ((exists x. forall y. Q(x) <=> Q(y)) <=>
            ((exists x. P(x)) <=> (forall y. P(y))))",
        formula<fol>.False,       // The result was unknown when test created. False used as place holder.
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 34
        // Pelletier #35
        // lcffol.p056
        @"exists x y. P(x,y) ==> (forall x y. P(x,y))",
        Exists
            ("x",
            Exists
                ("y",
                Imp
                    (Atom (R ("P",[Var "x"; Var "y"])),
                    Forall ("x",Forall ("y",Atom (R ("P",[Var "x"; Var "y"]))))))),
        @"|- exists x y. P(x,y) ==> (forall x y. P(x,y))"
    );
    (
        // idx 35
        // Pelletier #36
        // lcffol.p057
        @"(forall x. exists y. P(x,y)) /\
        (forall x. exists y. G(x,y)) /\
        (forall x y. P(x,y) \/ G(x,y)
        ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
            ==> (forall x. exists y. H(x,y))",
        Imp
            (And
                (Forall ("x",Exists ("y",Atom (R ("P",[Var "x"; Var "y"])))),
                And
                    (Forall ("x",Exists ("y",Atom (R ("G",[Var "x"; Var "y"])))),
                    Forall
                        ("x",
                        Forall
                            ("y",
                            Imp
                                (Or
                                    (Atom (R ("P",[Var "x"; Var "y"])),
                                    Atom (R ("G",[Var "x"; Var "y"]))),
                                Forall
                                    ("z",
                                    Imp
                                        (Or
                                        (Atom (R ("P",[Var "y"; Var "z"])),
                                            Atom (R ("G",[Var "y"; Var "z"]))),
                                        Atom (R ("H",[Var "x"; Var "z"]))))))))),
            Forall ("x",Exists ("y",Atom (R ("H",[Var "x"; Var "y"]))))),
        @"|- (forall x. exists y. P(x,y)) /\ (forall x. exists y. G(x,y)) /\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z))) ==> (forall x. exists y. H(x,y))"
    );
    (
        // idx 36
        // Pelletier #37
        // lcffol.p058
        @"(forall z.
            exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
            (P(y,w) ==> (exists u. Q(u,w)))) /\
        (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
        ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
        (forall x. exists y. R(x,y))",
        Imp
            (And
                (Forall
                    ("z",
                    Exists
                        ("w",
                        Forall
                            ("x",
                            Exists
                                ("y",
                                And
                                    (Imp
                                        (Atom (R ("P",[Var "x"; Var "z"])),
                                        Atom (R ("P",[Var "y"; Var "w"]))),
                                    And
                                        (Atom (R ("P",[Var "y"; Var "z"])),
                                        Imp
                                            (Atom (R ("P",[Var "y"; Var "w"])),
                                            Exists
                                                ("u",Atom (R ("Q",[Var "u"; Var "w"])))))))))),
                And
                    (Forall
                            ("x",
                            Forall
                                ("z",
                                Imp
                                    (Not (Atom (R ("P",[Var "x"; Var "z"]))),
                                    Exists ("y",Atom (R ("Q",[Var "y"; Var "z"])))))),
                    Imp
                        (Exists
                            ("x",Exists ("y",Atom (R ("Q",[Var "x"; Var "y"])))),
                        Forall ("x",Atom (R ("R",[Var "x"; Var "x"])))))),
            Forall ("x",Exists ("y",Atom (R ("R",[Var "x"; Var "y"]))))),
        @"|- (forall z. exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\ (P(y,w) ==> (exists u. Q(u,w)))) /\ (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\ ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> (forall x. exists y. R(x,y))"
    );
    (
        // idx 37
        // Pelletier #38
        // lcffol.p059
        @"(forall x.
            P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
        (forall x.
            (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
            (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
            (exists z w. P(z) /\ R(x,w) /\ R(w,z))))",
        Iff
            (Forall
                ("x",
                Imp
                    (And
                        (Atom (R ("P",[Var "a"])),
                        Imp
                            (Atom (R ("P",[Var "x"])),
                            Exists
                                ("y",
                                And
                                    (Atom (R ("P",[Var "y"])),
                                    Atom (R ("R",[Var "x"; Var "y"])))))),
                    Exists
                        ("z",
                        Exists
                            ("w",
                            And
                                (Atom (R ("P",[Var "z"])),
                                And
                                    (Atom (R ("R",[Var "x"; Var "w"])),
                                    Atom (R ("R",[Var "w"; Var "z"])))))))),
                Forall
                    ("x",
                    And
                        (Or
                            (Not (Atom (R ("P",[Var "a"]))),
                            Or
                                (Atom (R ("P",[Var "x"])),
                                Exists
                                    ("z",
                                    Exists
                                        ("w",
                                        And
                                            (Atom (R ("P",[Var "z"])),
                                            And
                                                (Atom (R ("R",[Var "x"; Var "w"])),
                                                    Atom (R ("R",[Var "w"; Var "z"])))))))),
                        Or
                            (Not (Atom (R ("P",[Var "a"]))),
                            Or
                                (Not
                                    (Exists
                                        ("y",
                                        And
                                            (Atom (R ("P",[Var "y"])),
                                            Atom (R ("R",[Var "x"; Var "y"]))))),
                                    Exists
                                        ("z",
                                        Exists
                                            ("w",
                                            And
                                                (Atom (R ("P",[Var "z"])),
                                                And
                                                    (Atom (R ("R",[Var "x"; Var "w"])),
                                                    Atom (R ("R",[Var "w"; Var "z"]))))))))))),
        @"|- (forall x. P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==> (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=> (forall x. (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\ (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))))"
    );
    (
        // idx 38
        // Pelletier #39
        // lcffol.p060
        @"~(exists x. forall y. P(y,x) <=> ~P(y,y))",
        Not
            (Exists
                ("x",
                Forall
                    ("y",
                    Iff
                        (Atom (R ("P",[Var "y"; Var "x"])),
                        Not (Atom (R ("P",[Var "y"; Var "y"]))))))),
        @"|- ~(exists x. forall y. P(y,x) <=> ~P(y,y))"
    );
    (
        // idx 39
        // Pelletier #40
        // lcffol.p061
        @"(exists y. forall x. P(x,y) <=> P(x,x))
        ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))",
        Imp
            (Exists
                ("y",
                Forall
                    ("x",
                    Iff
                        (Atom (R ("P",[Var "x"; Var "y"])),
                        Atom (R ("P",[Var "x"; Var "x"]))))),
            Not
                (Forall
                    ("x",
                    Exists
                        ("y",
                        Forall
                            ("z",
                            Iff
                                (Atom (R ("P",[Var "z"; Var "y"])),
                                Not (Atom (R ("P",[Var "z"; Var "x"]))))))))),
        @"|- (exists y. forall x. P(x,y) <=> P(x,x)) ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))"
    );
    (
        // idx 40
        // Pelletier #41
        // lcffol.p062
        @"(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) 
        ==> ~(exists z. forall x. P(x,z))",
        Imp
            (Forall
                ("z",
                Exists
                    ("y",
                    Forall
                        ("x",
                        Iff
                            (Atom (R ("P",[Var "x"; Var "y"])),
                            And
                                (Atom (R ("P",[Var "x"; Var "z"])),
                                Not (Atom (R ("P",[Var "x"; Var "x"])))))))),
            Not (Exists ("z",Forall ("x",Atom (R ("P",[Var "x"; Var "z"])))))),
        @"|- (forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x)) ==> ~(exists z. forall x. P(x,z))"
    );
    (
        // idx 41
        // Pelletier #42
        // lcffol.p063
        @"~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))",
        Not
            (Exists
               ("y",
                Forall
                    ("x",
                    Iff
                        (Atom (R ("P",[Var "x"; Var "y"])),
                        Not
                            (Exists
                                ("z",
                                And
                                    (Atom (R ("P",[Var "x"; Var "z"])),
                                    Atom (R ("P",[Var "z"; Var "x"]))))))))),
        @"|- ~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))"
    );
    (
        // idx 42
        // Pelletier #43
        // lcffol.p064
        @"(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)",
        formula<fol>.False,       // The result was unknown when test created. False used as place holder.
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 43
        // Pelletier #44
        // lcffol.p065
        @"(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
        (exists y. G(y) /\ ~H(x,y))) /\
        (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
        (exists x. J(x) /\ ~P(x))",
        Imp
            (And
                (Forall
                    ("x",
                    Imp
                        (Atom (R ("P",[Var "x"])),
                        And
                            (Exists
                                ("y",
                                And
                                    (Atom (R ("G",[Var "y"])),
                                    Atom (R ("H",[Var "x"; Var "y"])))),
                                Exists
                                    ("y",
                                    And
                                        (Atom (R ("G",[Var "y"])),
                                        Not (Atom (R ("H",[Var "x"; Var "y"])))))))),
                Exists
                    ("x",
                    And
                        (Atom (R ("J",[Var "x"])),
                        Forall
                            ("y",
                            Imp
                                (Atom (R ("G",[Var "y"])),
                                Atom (R ("H",[Var "x"; Var "y"]))))))),
            Exists
                ("x",
                And (Atom (R ("J",[Var "x"])),Not (Atom (R ("P",[Var "x"])))))),
        @"|- (forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\ (exists y. G(y) /\ ~H(x,y))) /\ (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==> (exists x. J(x) /\ ~P(x))"
    );
    (
        // idx 44
        // Pelletier #45
        // lcffol.p066
        @"(forall x.
            P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
                (forall y. G(y) /\ H(x,y) ==> R(y))) /\
        ~(exists y. L(y) /\ R(y)) /\
        (exists x. P(x) /\ (forall y. H(x,y) ==>
            L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
        (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))",
        Imp
            (And
               (Forall
                    ("x",
                    Imp
                        (And
                            (Atom (R ("P",[Var "x"])),
                            Forall
                                ("y",
                                Imp
                                    (And
                                        (Atom (R ("G",[Var "y"])),
                                        Atom (R ("H",[Var "x"; Var "y"]))),
                                    Atom (R ("J",[Var "x"; Var "y"]))))),
                        Forall
                            ("y",
                            Imp
                                (And
                                    (Atom (R ("G",[Var "y"])),
                                    Atom (R ("H",[Var "x"; Var "y"]))),
                                Atom (R ("R",[Var "y"])))))),
                And
                    (Not
                        (Exists
                        ("y",
                            And (Atom (R ("L",[Var "y"])),Atom (R ("R",[Var "y"]))))),
                    Exists
                        ("x",
                        And
                            (Atom (R ("P",[Var "x"])),
                            And
                                (Forall
                                    ("y",
                                    Imp
                                        (Atom (R ("H",[Var "x"; Var "y"])),
                                        Atom (R ("L",[Var "y"])))),
                                Forall
                                    ("y",
                                    Imp
                                        (And
                                        (Atom (R ("G",[Var "y"])),
                                            Atom (R ("H",[Var "x"; Var "y"]))),
                                        Atom (R ("J",[Var "x"; Var "y"]))))))))),
            Exists
                ("x",
                And
                    (Atom (R ("P",[Var "x"])),
                    Not
                        (Exists
                            ("y",
                            And
                                (Atom (R ("G",[Var "y"])),
                                Atom (R ("H",[Var "x"; Var "y"])))))))),
        @"|- (forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\ ~(exists y. L(y) /\ R(y)) /\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))"
    );
    (
        // idx 45
        // Pelletier #46
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 46
        // Pelletier #47
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 47
        // Pelletier #48
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 48
        // Pelletier #49
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 49
        // Pelletier #50
        // lcffol.p0  
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 50
        // Pelletier #51
        // lcffol.p0  
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 51
        // Pelletier #52
        // lcffol.p0  
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 52
        // Pelletier #53
        // lcffol.p0  
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 53
        // Pelletier #54
        // lcffol.p0  
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 54
        // Pelletier #55
        // lcffol.p067
        @"lives(agatha) /\ lives(butler) /\ lives(charles) /\
        (killed(agatha,agatha) \/ killed(butler,agatha) \/
            killed(charles,agatha)) /\
        (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
        (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
        (hates(agatha,agatha) /\ hates(agatha,charles)) /\
        (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
        (forall x. hates(agatha,x) ==> hates(butler,x)) /\
        (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
        ==> killed(agatha,agatha) /\
            ~killed(butler,agatha) /\
            ~killed(charles,agatha)",
        Imp
            (And
                (Atom (R ("lives",[Var "agatha"])),
                And
                    (Atom (R ("lives",[Var "butler"])),
                    And
                        (Atom (R ("lives",[Var "charles"])),
                        And
                            (Or
                                (Atom (R ("killed",[Var "agatha"; Var "agatha"])),
                                Or
                                    (Atom (R ("killed",[Var "butler"; Var "agatha"])),
                                    Atom (R ("killed",[Var "charles"; Var "agatha"])))),
                                And
                                    (Forall
                                        ("x",
                                        Forall
                                            ("y",
                                            Imp
                                                (Atom (R ("killed",[Var "x"; Var "y"])),
                                                And
                                                    (Atom (R ("hates",[Var "x"; Var "y"])),
                                                    Not
                                                        (Atom
                                                            (R ("richer",[Var "x"; Var "y"]))))))),
                                    And
                                        (Forall
                                            ("x",
                                            Imp
                                                (Atom (R ("hates",[Var "agatha"; Var "x"])),
                                                Not
                                                    (Atom
                                                        (R ("hates",[Var "charles"; Var "x"]))))),
                                        And
                                            (And
                                            (Atom
                                                (R ("hates",[Var "agatha"; Var "agatha"])),
                                                Atom
                                                    (R ("hates",[Var "agatha"; Var "charles"]))),
                                            And
                                                (Forall
                                                    ("x",
                                                    Imp
                                                        (And
                                                            (Atom (R ("lives",[Var "x"])),
                                                            Not
                                                                (Atom
                                                                    (R ("richer",
                                                                        [Var "x"; Var "agatha"])))),
                                                        Atom
                                                            (R ("hates",[Var "butler"; Var "x"])))),
                                                    And
                                                        (Forall
                                                            ("x",
                                                            Imp
                                                                (Atom
                                                                (R ("hates",
                                                                    [Var "agatha"; Var "x"])),
                                                                Atom
                                                                    (R ("hates",
                                                                        [Var "butler"; Var "x"])))),
                                                            Forall
                                                                ("x",
                                                                Or
                                                                    (Not
                                                                        (Atom
                                                                            (R ("hates",
                                                                                [Var "x"; Var "agatha"]))),
                                                                        Or
                                                                            (Not
                                                                                (Atom
                                                                                    (R ("hates",
                                                                                        [Var "x"; Var "butler"]))),
                                                                                Not
                                                                                    (Atom
                                                                                        (R ("hates",
                                                                                            [Var "x";
                                                                                            Var "charles"]))))))))))))))),
            And
                (Atom (R ("killed",[Var "agatha"; Var "agatha"])),
                And
                    (Not (Atom (R ("killed",[Var "butler"; Var "agatha"]))),
                    Not (Atom (R ("killed",[Var "charles"; Var "agatha"])))))),
        @"|- lives(agatha) /\ lives(butler) /\ lives(charles) /\ (killed(agatha,agatha) \/ killed(butler,agatha) \/ killed(charles,agatha)) /\ (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\ (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\ (hates(agatha,agatha) /\ hates(agatha,charles)) /\ (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\ (forall x. hates(agatha,x) ==> hates(butler,x)) /\ (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) ==> killed(agatha,agatha) /\ ~killed(butler,agatha) /\ ~killed(charles,agatha)"
    );
    (
        // idx 55
        // Pelletier #56
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 56
        // Pelletier #57
        // lcffol.p068
        @"P(f(a,b),f(b,c)) /\
        P(f(b,c),f(a,c)) /\
        (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z))
        ==> P(f(a,b),f(a,c))",
        Imp
            (And
                (Atom
                    (R ("P",
                        [Fn ("f",[Var "a"; Var "b"]); Fn ("f",[Var "b"; Var "c"])])),
                And
                    (Atom
                        (R ("P",
                            [Fn ("f",[Var "b"; Var "c"]);
                            Fn ("f",[Var "a"; Var "c"])])),
                    Forall
                        ("x",
                        Forall
                            ("y",
                            Forall
                                ("z",
                                Imp
                                    (And
                                        (Atom (R ("P",[Var "x"; Var "y"])),
                                        Atom (R ("P",[Var "y"; Var "z"]))),
                                    Atom (R ("P",[Var "x"; Var "z"])))))))),
            Atom
                (R ("P",
                    [Fn ("f",[Var "a"; Var "b"]); Fn ("f",[Var "a"; Var "c"])]))),
        @"|- P(f(a,b),f(b,c)) /\ P(f(b,c),f(a,c)) /\ (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) ==> P(f(a,b),f(a,c))"
    );
    (
        // idx 57
        // Pelletier #58
        // TODO: Is this a conrrect translation from Pelletier #58? No
        // lcffol.p069
        @"forall P Q R. forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
        Forall
            ("P",
            Forall
                ("Q",
                Forall
                    ("R",
                    Forall
                        ("x",
                        Exists
                            ("v",
                            Exists
                                ("w",
                                Forall
                                    ("y",
                                    Forall
                                        ("z",
                                         Imp
                                            (And
                                                (Atom (R ("P",[Var "x"])),
                                                Atom (R ("Q",[Var "y"]))),
                                            And
                                                (Or
                                                    (Atom (R ("P",[Var "v"])),
                                                    Atom (R ("R",[Var "w"]))),
                                                Imp
                                                    (Atom (R ("R",[Var "z"])),
                                                    Atom (R ("Q",[Var "v"]))))))))))))),
        @"|- forall P Q R x. exists v w. forall y z. P(x) /\ Q(y) ==> (P(v) \/ R(w)) /\ (R(z) ==> Q(v))"
    );
    (
        // idx 58
        // Pelletier #59
        // lcffol.p070
        @"(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))",
        Imp
            (Forall
                ("x",
                Iff
                    (Atom (R ("P",[Var "x"])),
                    Not (Atom (R ("P",[Fn ("f",[Var "x"])]))))),
            Exists
                ("x",
                And
                    (Atom (R ("P",[Var "x"])),
                    Not (Atom (R ("P",[Fn ("f",[Var "x"])])))))),
        @"|- (forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))"
    );
    (
        // idx 59
        // Pelletier #60
        // lcffol.p071
        @"forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)",
        Forall
            ("x",
            Iff
                (Atom (R ("P",[Var "x"; Fn ("f",[Var "x"])])),
                Exists
                    ("y",
                    And
                        (Forall
                            ("z",
                            Imp
                                (Atom (R ("P",[Var "z"; Var "y"])),
                                Atom (R ("P",[Var "z"; Fn ("f",[Var "x"])])))),
                         Atom (R ("P",[Var "x"; Var "y"])))))),
        @"|- forall x. P(x,f(x)) <=> (exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y))"
    );
    (
        // idx 60
        // Pelletier #61
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 61
        // Pelletier #62
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 62
        // Pelletier #63
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 63
        // Pelletier #64
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 64
        // Pelletier #65
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 65
        // Pelletier #66
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 66
        // Pelletier #67
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 67
        // Pelletier #68
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 68
        // Pelletier #69
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 69
        // Pelletier #70
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 70
        // Pelletier #71
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 71
        // Pelletier #72
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 72
        // Pelletier #73
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 73
        // Pelletier #74
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 74
        // Pelletier #75
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 75
        // Gilmore #1
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 76
        // Gilmore #2
        @"formula_place_holder_for_future_use",
        formula<fol>.False,
        @"pretty_printer_result_place_holder"
    );
    (
        // idx 77
        // Gilmore #3
        // lcffol.p072
        @"exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> H(z)) /\
            F(x,y)
            ==> F(z,z)",
        Exists
            ("x",
            Forall
                ("y",
                Forall
                    ("z",
                    Imp
                        (And
                            (Imp
                                (Imp
                                    (Atom (R ("F",[Var "y"; Var "z"])),
                                    Imp
                                        (Atom (R ("G",[Var "y"])),
                                        Atom (R ("H",[Var "x"])))),
                                Atom (R ("F",[Var "x"; Var "x"]))),
                            And
                                (Imp
                                    (Imp
                                        (Atom (R ("F",[Var "z"; Var "x"])),
                                        Atom (R ("G",[Var "x"]))),
                                    Atom (R ("H",[Var "z"]))),
                                Atom (R ("F",[Var "x"; Var "y"])))),
                        Atom (R ("F",[Var "z"; Var "z"])))))),
        @"|- exists x. forall y z. ((F(y,z) ==> G(y) ==> H(x)) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> H(z)) /\ F(x,y) ==> F(z,z)"
    );
    (
        // idx 78
        // Gilmore #4
        // lcffol.p073
        @"exists x y. forall z.
            (F(x,y) ==> F(y,z) /\ F(z,z)) /\
            (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))",
        Exists
            ("x",
            Exists
                ("y",
                Forall
                    ("z",
                    And
                        (Imp
                            (Atom (R ("F",[Var "x"; Var "y"])),
                            And
                                (Atom (R ("F",[Var "y"; Var "z"])),
                                Atom (R ("F",[Var "z"; Var "z"])))),
                        Imp
                            (And
                                (Atom (R ("F",[Var "x"; Var "y"])),
                                Atom (R ("G",[Var "x"; Var "y"]))),
                            And
                                (Atom (R ("G",[Var "x"; Var "z"])),
                                Atom (R ("G",[Var "z"; Var "z"])))))))),
        @"|- exists x y. forall z. (F(x,y) ==> F(y,z) /\ F(z,z)) /\ (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))"
    );
    (
        // idx 79
        // Gilmore #5
        // lcffol.p074
        @"(forall x. exists y. F(x,y) \/ F(y,x)) /\
        (forall x y. F(y,x) ==> F(y,y))
        ==> exists z. F(z,z)",
        Imp
            (And
                (Forall
                    ("x",
                    Exists
                        ("y",
                        Or
                            (Atom (R ("F",[Var "x"; Var "y"])),
                            Atom (R ("F",[Var "y"; Var "x"]))))),
                Forall
                    ("x",
                    Forall
                        ("y",
                        Imp
                            (Atom (R ("F",[Var "y"; Var "x"])),
                            Atom (R ("F",[Var "y"; Var "y"])))))),
            Exists ("z",Atom (R ("F",[Var "z"; Var "z"])))),
        @"|- (forall x. exists y. F(x,y) \/ F(y,x)) /\ (forall x y. F(y,x) ==> F(y,y)) ==> (exists z. F(z,z))"
    );
    (
        // idx 80
        // Gilmore #6
        // lcffol.p075
        @"forall x. exists y.
            (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
            ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
                (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))",
        Forall
            ("x",
            Exists
                ("y",
                Imp
                    (Exists
                        ("u",
                        Forall
                            ("v",
                            Imp
                               (Atom (R ("F",[Var "u"; Var "x"])),
                                And
                                    (Atom (R ("G",[Var "v"; Var "u"])),
                                    Atom (R ("G",[Var "u"; Var "x"])))))),
                    Or
                        (Exists
                            ("u",
                            Forall
                                ("v",
                                Imp
                                    (Atom (R ("F",[Var "u"; Var "y"])),
                                    And
                                        (Atom (R ("G",[Var "v"; Var "u"])),
                                        Atom (R ("G",[Var "u"; Var "y"])))))),
                        Forall
                            ("u",
                            Forall
                                ("v",
                                Exists
                                    ("w",
                                    Imp
                                        (Or
                                            (Atom (R ("G",[Var "v"; Var "u"])),
                                            Atom (R ("H",[Var "w"; Var "y"; Var "u"]))),
                                        Atom (R ("G",[Var "u"; Var "w"])))))))))),
        @"|- forall x. exists y. (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x)) ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/ (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))"
    );
    (
        // idx 81
        // Gilmore #7
        // lcffol.p076
        @"(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
        (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
        ==> exists v w. K(v) /\ L(w) /\ G(v,w)",
        Imp
            (And
                (Forall
                    ("x",
                    Imp
                        (Atom (R ("K",[Var "x"])),
                        Exists
                            ("y",
                            And
                                (Atom (R ("L",[Var "y"])),
                                Imp
                                    (Atom (R ("F",[Var "x"; Var "y"])),
                                    Atom (R ("G",[Var "x"; Var "y"]))))))),
                Exists
                    ("z",
                    And
                        (Atom (R ("K",[Var "z"])),
                        Forall
                            ("u",
                            Imp
                                (Atom (R ("L",[Var "u"])),
                                Atom (R ("F",[Var "z"; Var "u"]))))))),
            Exists
                ("v",
                Exists
                    ("w",
                    And
                        (Atom (R ("K",[Var "v"])),
                        And
                            (Atom (R ("L",[Var "w"])),
                            Atom (R ("G",[Var "v"; Var "w"]))))))),
        @"|- (forall x. K(x) ==> (exists y. L(y) /\ (F(x,y) ==> G(x,y)))) /\ (exists z. K(z) /\ (forall u. L(u) ==> F(z,u))) ==> (exists v w. K(v) /\ L(w) /\ G(v,w))"
    );
    (
        // idx 82
        // Gilmore #8
        // lcffol.p077
        @"exists x. forall y z.
            ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
            ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
            F(x,y)
            ==> F(z,z)",
        Exists
            ("x",
            Forall
                ("y",
                Forall
                    ("z",
                    Imp
                        (And
                            (Imp
                               (Imp
                                    (Atom (R ("F",[Var "y"; Var "z"])),
                                    Imp
                                        (Atom (R ("G",[Var "y"])),
                                        Forall
                                            ("u",
                                            Exists
                                                ("v",
                                                Atom
                                                    (R ("H",[Var "u"; Var "v"; Var "x"])))))),
                                Atom (R ("F",[Var "x"; Var "x"]))),
                            And
                                (Imp
                                    (Imp
                                        (Atom (R ("F",[Var "z"; Var "x"])),
                                        Atom (R ("G",[Var "x"]))),
                                    Forall
                                        ("u",
                                        Exists
                                            ("v",
                                            Atom (R ("H",[Var "u"; Var "v"; Var "z"]))))),
                                Atom (R ("F",[Var "x"; Var "y"])))),
                        Atom (R ("F",[Var "z"; Var "z"])))))),
        @"|- exists x. forall y z. ((F(y,z) ==> G(y) ==> (forall u. exists v. H(u,v,x))) ==> F(x,x)) /\ ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\ F(x,y) ==> F(z,z)"
    );
    (
        // idx 83
        // Gilmore #9
        // lcffol.p078
        @"forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
            ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
            ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
        ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
        ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
            (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))",
        Forall
            ("x",
            Exists
                ("y",
                Forall
                    ("z",
                    And
                        (Imp
                            (Forall
                                ("u",
                                Exists
                                    ("v",
                                    And
                                        (Atom (R ("F",[Var "y"; Var "u"; Var "v"])),
                                        And
                                            (Atom (R ("G",[Var "y"; Var "u"])),
                                            Not (Atom (R ("H",[Var "y"; Var "x"]))))))),
                            Imp
                                (Forall
                                    ("u",
                                    Exists
                                        ("v",
                                        And
                                            (Atom (R ("F",[Var "x"; Var "u"; Var "v"])),
                                            And
                                               (Atom (R ("G",[Var "z"; Var "u"])),
                                                Not (Atom (R ("H",[Var "x"; Var "z"]))))))),
                                Forall
                                    ("u",
                                    Exists
                                        ("v",
                                        And
                                            (Atom (R ("F",[Var "x"; Var "u"; Var "v"])),
                                            And
                                               (Atom (R ("G",[Var "y"; Var "u"])),
                                                Not (Atom (R ("H",[Var "x"; Var "y"]))))))))),
                        Imp
                            (Forall
                                ("u",
                                Exists
                                    ("v",
                                    And
                                        (Atom (R ("F",[Var "x"; Var "u"; Var "v"])),
                                        And
                                            (Atom (R ("G",[Var "y"; Var "u"])),
                                            Not (Atom (R ("H",[Var "x"; Var "y"]))))))),
                            Imp
                                (Not
                                    (Forall
                                        ("u",
                                        Exists
                                            ("v",
                                            And
                                                (Atom
                                                    (R ("F",[Var "x"; Var "u"; Var "v"])),
                                                And
                                                    (Atom (R ("G",[Var "z"; Var "u"])),
                                                    Not
                                                        (Atom (R ("H",[Var "x"; Var "z"])))))))),
                                And
                                    (Forall
                                        ("u",
                                        Exists
                                            ("v",
                                            And
                                                (Atom
                                                    (R ("F",[Var "y"; Var "u"; Var "v"])),
                                                And
                                                    (Atom (R ("G",[Var "y"; Var "u"])),
                                                    Not
                                                        (Atom (R ("H",[Var "y"; Var "x"]))))))),
                                    Forall
                                        ("u",
                                        Exists
                                            ("v",
                                            And
                                                (Atom
                                                    (R ("F",[Var "z"; Var "u"; Var "v"])),
                                                    And
                                                        (Atom (R ("G",[Var "y"; Var "u"])),
                                                        Not
                                                            (Atom (R ("H",[Var "z"; Var "y"])))))))))))))),
        @"|- forall x. exists y. forall z. ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\ ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y)) ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z)) ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\ (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))"
    );
    (
        // idx 84
        // Davis Putnam #1
        // lcffol.p079
        @"exists x. exists y. forall z.
            (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
            ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))",
        Exists
            ("x",
            Exists
                ("y",
                Forall
                    ("z",
                    And
                        (Imp
                            (Atom (R ("F",[Var "x"; Var "y"])),
                            And
                                (Atom (R ("F",[Var "y"; Var "z"])),
                                Atom (R ("F",[Var "z"; Var "z"])))),
                         Imp
                            (And
                                (Atom (R ("F",[Var "x"; Var "y"])),
                                Atom (R ("G",[Var "x"; Var "y"]))),
                            And
                                (Atom (R ("G",[Var "x"; Var "z"])),
                                Atom (R ("G",[Var "z"; Var "z"])))))))),
        @"|- exists x y. forall z. (F(x,y) ==> F(y,z) /\ F(z,z)) /\ (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))"
    );
    (
        // idx 85
        // Dijkstra #1
        // lcffol.p004
        // lcffol.p080
        @"(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y))",
        Imp
            (And
                (Forall ("x",Atom (R ("<=",[Var "x"; Var "x"]))),
                And
                    (Forall
                        ("x",
                        Forall
                            ("y",
                            Forall
                                ("z",
                                Imp
                                    (And
                                        (Atom (R ("<=",[Var "x"; Var "y"])),
                                        Atom (R ("<=",[Var "y"; Var "z"]))),
                                    Atom (R ("<=",[Var "x"; Var "z"])))))),
                    Forall
                        ("x",
                        Forall
                            ("y",
                            Iff
                                (Atom (R ("<=",[Fn ("f",[Var "x"]); Var "y"])),
                                Atom (R ("<=",[Var "x"; Fn ("g",[Var "y"])]))))))),
            Forall
                ("x",
                Forall
                    ("y",
                    Imp
                        (Atom (R ("<=",[Var "x"; Var "y"])),
                        Atom (R ("<=",[Fn ("f",[Var "x"]); Fn ("f",[Var "y"])])))))),
        @"|- (forall x. x <=x) /\ (forall x y z. x <=y /\ y <=z ==> x <=z) /\ (forall x y. f(x) <=y <=> x <=g(y)) ==> (forall x y. x <=y ==> f(x) <=f(y))"
    );
    (
        // idx 86
        // Dijkstra #2
        // lcffol.p081
        @"(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> g(x) <= g(y))",
        Imp
            (And
                (Forall ("x",Atom (R ("<=",[Var "x"; Var "x"]))),
                And
                    (Forall
                        ("x",
                        Forall
                            ("y",
                            Forall
                                ("z",
                                Imp
                                    (And
                                        (Atom (R ("<=",[Var "x"; Var "y"])),
                                        Atom (R ("<=",[Var "y"; Var "z"]))),
                                    Atom (R ("<=",[Var "x"; Var "z"])))))),
                    Forall
                        ("x",
                        Forall
                            ("y",
                            Iff
                                (Atom (R ("<=",[Fn ("f",[Var "x"]); Var "y"])),
                                Atom (R ("<=",[Var "x"; Fn ("g",[Var "y"])]))))))),
            Forall
                ("x",
                Forall
                    ("y",
                    Imp
                        (Atom (R ("<=",[Var "x"; Var "y"])),
                        Atom (R ("<=",[Fn ("g",[Var "x"]); Fn ("g",[Var "y"])])))))),
        @"|- (forall x. x <=x) /\ (forall x y z. x <=y /\ y <=z ==> x <=z) /\ (forall x y. f(x) <=y <=> x <=g(y)) ==> (forall x y. x <=y ==> g(x) <=g(y))"
    );
    (
        // idx 87
        // lcffol.p003
        // Pelletier #58
        // TODO: Is this a conrrect translation from Pelletier #58? No
        @"forall x. exists v. exists w. forall y. forall z.
        ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))",
        Forall
            ("x",
            Exists
                ("v",
                Exists
                    ("w",
                    Forall
                        ("y",
                        Forall
                            ("z",
                            Imp
                                (And
                                    (Atom (R ("P",[Var "x"])),Atom (R ("Q",[Var "y"]))),
                                And
                                    (Or
                                        (Atom (R ("P",[Var "v"])),
                                        Atom (R ("R",[Var "w"]))),
                                    Imp
                                        (Atom (R ("R",[Var "z"])),
                                        Atom (R ("Q",[Var "v"])))))))))),
        @"|- forall x. exists v w. forall y z. P(x) /\ Q(y) ==> (P(v) \/ R(w)) /\ (R(z) ==> Q(v))"
    );
    |]

[<TestCase(0, TestName = "Pelletier #01")>]
[<TestCase(1, TestName = "Pelletier #02")>]
[<TestCase(2, TestName = "Pelletier #03")>]
[<TestCase(3, TestName = "Pelletier #04")>]
[<TestCase(4, TestName = "Pelletier #05")>]
[<TestCase(5, TestName = "Pelletier #06")>]
[<TestCase(6, TestName = "Pelletier #07")>]
[<TestCase(7, TestName = "Pelletier #08")>]
[<TestCase(8, TestName = "Pelletier #09")>]
[<TestCase(9, TestName = "Pelletier #10")>]
[<TestCase(10, TestName = "Pelletier #11")>]
[<TestCase(11, TestName = "Pelletier #12")>]
[<TestCase(12, TestName = "Pelletier #13")>]
[<TestCase(13, TestName = "Pelletier #14")>]
[<TestCase(14, TestName = "Pelletier #15")>]
[<TestCase(15, TestName = "Pelletier #16")>]
[<TestCase(16, TestName = "Pelletier #17")>]

[<Test>]
let ``lcftaut ast tests`` idx = 
    let (formula, _, _) = lcfValues.[idx]
    let (_, ast_result, _) = lcfValues.[idx]
    lcftaut (parse formula)
    |> should equal ast_result

[<TestCase(0, TestName = "Pelletier #01")>]
[<TestCase(1, TestName = "Pelletier #02")>]
[<TestCase(2, TestName = "Pelletier #03")>]
[<TestCase(3, TestName = "Pelletier #04")>]
[<TestCase(4, TestName = "Pelletier #05")>]
[<TestCase(5, TestName = "Pelletier #06")>]
[<TestCase(6, TestName = "Pelletier #07")>]
[<TestCase(7, TestName = "Pelletier #08")>]
[<TestCase(8, TestName = "Pelletier #09")>]
[<TestCase(9, TestName = "Pelletier #10")>]
[<TestCase(10, TestName = "Pelletier #11")>]
[<TestCase(11, TestName = "Pelletier #12")>]
[<TestCase(12, TestName = "Pelletier #13")>]
[<TestCase(13, TestName = "Pelletier #14")>]
[<TestCase(14, TestName = "Pelletier #15")>]
[<TestCase(15, TestName = "Pelletier #16")>]
[<TestCase(16, TestName = "Pelletier #17")>]

[<Test>]
let ``lcftaut pp tests`` idx = 
    let (formula, _, _) = lcfValues.[idx]
    let (_, _, pretty_printer_result) = lcfValues.[idx]
    lcftaut (parse formula)
    |> sprint_thm
    |> should equal pretty_printer_result
   
[<TestCase(0, TestName = "Pelletier #01")>]
[<TestCase(1, TestName = "Pelletier #02")>]
[<TestCase(2, TestName = "Pelletier #03")>]
[<TestCase(3, TestName = "Pelletier #04")>]
[<TestCase(4, TestName = "Pelletier #05")>]
[<TestCase(5, TestName = "Pelletier #06")>]
[<TestCase(6, TestName = "Pelletier #07")>]
[<TestCase(7, TestName = "Pelletier #08")>]
[<TestCase(8, TestName = "Pelletier #09")>]
[<TestCase(9, TestName = "Pelletier #10")>]
[<TestCase(10, TestName = "Pelletier #11")>]
[<TestCase(11, TestName = "Pelletier #12")>]
[<TestCase(12, TestName = "Pelletier #13")>]
[<TestCase(13, TestName = "Pelletier #14")>]
[<TestCase(14, TestName = "Pelletier #15")>]
[<TestCase(15, TestName = "Pelletier #16")>]
[<TestCase(16, TestName = "Pelletier #17")>]
[<TestCase(17, TestName = "Pelletier #18")>]
[<TestCase(18, TestName = "Pelletier #19")>]
[<TestCase(19, TestName = "Pelletier #20")>]
[<TestCase(20, TestName = "Pelletier #21")>]
[<TestCase(21, TestName = "Pelletier #22")>]
[<TestCase(22, TestName = "Pelletier #23")>]
[<TestCase(23, TestName = "Pelletier #24")>]
[<TestCase(24, TestName = "Pelletier #25")>]
[<TestCase(25, TestName = "Pelletier #26")>]
[<TestCase(26, TestName = "Pelletier #27")>]
[<TestCase(27, TestName = "Pelletier #28")>]
[<TestCase(28, TestName = "Pelletier #29")>]
[<TestCase(29, TestName = "Pelletier #30")>]
[<TestCase(30, TestName = "Pelletier #31")>]
[<TestCase(31, TestName = "Pelletier #32")>]
[<TestCase(32, TestName = "Pelletier #33")>]
[<TestCase(33, Category = "LongRunning", TestName = "Pelletier #34")>]
[<TestCase(34, TestName = "Pelletier #35")>]
[<TestCase(35, TestName = "Pelletier #36")>]
[<TestCase(36, TestName = "Pelletier #37")>]
[<TestCase(37, TestName = "Pelletier #38")>]
[<TestCase(38, TestName = "Pelletier #39")>]
[<TestCase(39, TestName = "Pelletier #40")>]
[<TestCase(40, TestName = "Pelletier #41")>]
[<TestCase(41, TestName = "Pelletier #42")>]
[<TestCase(42, Category = "LongRunning", TestName = "Pelletier #43")>]
[<TestCase(43, TestName = "Pelletier #44")>]
[<TestCase(44, TestName = "Pelletier #45")>]
[<TestCase(54, TestName = "Pelletier #55")>]
[<TestCase(56, TestName = "Pelletier #57")>]
[<TestCase(57, TestName = "Pelletier #58 1")>]
[<TestCase(87, TestName = "Pelletier #58 2")>]
[<TestCase(58, TestName = "Pelletier #59")>]
[<TestCase(59, TestName = "Pelletier #60")>]
[<TestCase(77, TestName = "Gilmore #3")>]
[<TestCase(78, TestName = "Gilmore #4")>]
[<TestCase(79, TestName = "Gilmore #5")>]
[<TestCase(80, TestName = "Gilmore #6")>]
[<TestCase(81, TestName = "Gilmore #7")>]
[<TestCase(82, TestName = "Gilmore #8")>]
[<TestCase(83, TestName = "Gilmore #9")>]
[<TestCase(84, TestName = "Davis Putnam #1")>]
[<TestCase(85, TestName = "Dijkstra #1")>]
[<TestCase(86, TestName = "Dijkstra #2")>]

[<Test>]
let ``lcffol ast tests`` idx = 
    let (formula, _, _) = lcfValues.[idx]
    let (_, ast_result, _) = lcfValues.[idx]
    lcffol (parse formula)
    |> should equal ast_result

[<TestCase(0, TestName = "Pelletier #01")>]
[<TestCase(1, TestName = "Pelletier #02")>]
[<TestCase(2, TestName = "Pelletier #03")>]
[<TestCase(3, TestName = "Pelletier #04")>]
[<TestCase(4, TestName = "Pelletier #05")>]
[<TestCase(5, TestName = "Pelletier #06")>]
[<TestCase(6, TestName = "Pelletier #07")>]
[<TestCase(7, TestName = "Pelletier #08")>]
[<TestCase(8, TestName = "Pelletier #09")>]
[<TestCase(9, TestName = "Pelletier #10")>]
[<TestCase(10, TestName = "Pelletier #11")>]
[<TestCase(11, TestName = "Pelletier #12")>]
[<TestCase(12, TestName = "Pelletier #13")>]
[<TestCase(13, TestName = "Pelletier #14")>]
[<TestCase(14, TestName = "Pelletier #15")>]
[<TestCase(15, TestName = "Pelletier #16")>]
[<TestCase(16, TestName = "Pelletier #17")>]
[<TestCase(17, TestName = "Pelletier #18")>]
[<TestCase(18, TestName = "Pelletier #19")>]
[<TestCase(19, TestName = "Pelletier #20")>]
[<TestCase(20, TestName = "Pelletier #21")>]
[<TestCase(21, TestName = "Pelletier #22")>]
[<TestCase(22, TestName = "Pelletier #23")>]
[<TestCase(23, TestName = "Pelletier #24")>]
[<TestCase(24, TestName = "Pelletier #25")>]
[<TestCase(25, TestName = "Pelletier #26")>]
[<TestCase(26, TestName = "Pelletier #27")>]
[<TestCase(27, TestName = "Pelletier #28")>]
[<TestCase(28, TestName = "Pelletier #29")>]
[<TestCase(29, TestName = "Pelletier #30")>]
[<TestCase(30, TestName = "Pelletier #31")>]
[<TestCase(31, TestName = "Pelletier #32")>]
[<TestCase(32, TestName = "Pelletier #33")>]
[<TestCase(33, Category = "LongRunning", TestName = "Pelletier #34")>]
[<TestCase(34, TestName = "Pelletier #35")>]
[<TestCase(35, TestName = "Pelletier #36")>]
[<TestCase(36, TestName = "Pelletier #37")>]
[<TestCase(37, TestName = "Pelletier #38")>]
[<TestCase(38, TestName = "Pelletier #39")>]
[<TestCase(39, TestName = "Pelletier #40")>]
[<TestCase(40, TestName = "Pelletier #41")>]
[<TestCase(41, TestName = "Pelletier #42")>]
[<TestCase(42, Category = "LongRunning", TestName = "Pelletier #43")>]
[<TestCase(43, TestName = "Pelletier #44")>]
[<TestCase(44, TestName = "Pelletier #45")>]
[<TestCase(54, TestName = "Pelletier #55")>]
[<TestCase(56, TestName = "Pelletier #57")>]
[<TestCase(57, TestName = "Pelletier #58 1")>]
[<TestCase(87, TestName = "Pelletier #58 2")>]
[<TestCase(58, TestName = "Pelletier #59")>]
[<TestCase(59, TestName = "Pelletier #60")>]
[<TestCase(77, TestName = "Gilmore #3")>]
[<TestCase(78, TestName = "Gilmore #4")>]
[<TestCase(79, TestName = "Gilmore #5")>]
[<TestCase(80, TestName = "Gilmore #6")>]
[<TestCase(81, TestName = "Gilmore #7")>]
[<TestCase(82, TestName = "Gilmore #8")>]
[<TestCase(83, TestName = "Gilmore #9")>]
[<TestCase(84, TestName = "Davis Putnam #1")>]
[<TestCase(85, TestName = "Dijkstra #1")>]
[<TestCase(86, TestName = "Dijkstra #2")>]

[<Test>]
let ``lcffol pp tests`` idx = 
    let (formula, _, _) = lcfValues.[idx]
    let (_, _, pretty_printer_result) = lcfValues.[idx]
    lcffol (parse formula)
    |> sprint_thm
    |> should equal pretty_printer_result
