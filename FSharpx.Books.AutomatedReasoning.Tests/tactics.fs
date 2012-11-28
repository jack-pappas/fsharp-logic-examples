// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.tactics

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.lcfprop
open FSharpx.Books.AutomatedReasoning.folderived
open FSharpx.Books.AutomatedReasoning.tactics
open NUnit.Framework
open FsUnit

let private reslutValues = [| 
    // tactics.p005  
    // tactics.p006  // idx 0
    (   Imp
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
                And
                    (Forall
                        ("x",
                        Forall
                            ("y",
                            Imp
                                (Atom (R ("<=",[Var "x"; Var "y"])),
                                    Atom
                                        (R ("<=",[Fn ("f",[Var "x"]); Fn ("f",[Var "y"])]))))),
                        Forall
                            ("x",
                            Forall
                                ("y",
                                Imp
                                    (Atom (R ("<=",[Var "x"; Var "y"])),
                                    Atom
                                        (R ("<=",[Fn ("g",[Var "x"]); Fn ("g",[Var "y"])])))))))
    );
    // tactics.p007  // idx 1
    (
        Imp
            (And
                (Forall
                    ("x",
                    Forall
                        ("y",
                        Iff
                            (Atom (R ("<=",[Var "x"; Var "y"])),
                                Atom (R ("=",[Fn ("*",[Var "x"; Var "y"]); Var "x"]))))),
                Forall
                    ("x",
                    Forall
                        ("y",
                        Atom
                            (R ("=",
                                [Fn ("f",[Fn ("*",[Var "x"; Var "y"])]);
                                    Fn ("*",[Fn ("f",[Var "x"]); Fn ("f",[Var "y"])])]))))),
                Forall
                    ("x",
                    Forall
                        ("y",
                        Imp
                            (Atom (R ("<=",[Var "x"; Var "y"])),
                            Atom (R ("<=",[Fn ("f",[Var "x"]); Fn ("f",[Var "y"])]))))))
    );
    // tactics.p008  
    // tactics.p009  
    // tactics.p012  // idx 2
    (
        Imp
            (Exists ("x",Atom (R ("p",[Var "x"]))),
            Imp
                (Forall
                    ("x",
                    Imp
                        (Atom (R ("p",[Var "x"])),
                        Atom (R ("p",[Fn ("f",[Var "x"])])))),
                    Exists
                        ("y",
                        Atom
                            (R ("p",
                                [Fn ("f",[Fn ("f",[Fn ("f",[Fn ("f",[Var "y"])])])])])))))
    );
    // tactics.p011  
    // tactics.p014  // idx 3
    (
        Imp
            (Atom (R ("p",[Var "a"])),
                Imp
                    (Forall
                        ("x",
                        Imp
                            (Atom (R ("p",[Var "x"])),
                            Atom (R ("p",[Fn ("f",[Var "x"])])))),
                    Exists
                        ("y",
                        And
                            (Atom (R ("p",[Var "y"])),
                            Atom (R ("p",[Fn ("f",[Var "y"])]))))))
    );
    // tactics.p012  
    // tactics.p015  
    // tactics.p016  // idx 4
    (
        Forall
            ("a",
                Imp
                    (Atom (R ("p",[Var "a"])),
                    Imp
                        (Forall
                            ("x",
                            Imp
                                (Atom (R ("p",[Var "x"])),
                                    Atom (R ("p",[Fn ("f",[Var "x"])])))),
                        Exists
                            ("y",
                            And
                                (Atom (R ("p",[Var "y"])),
                                    Atom (R ("p",[Fn ("f",[Var "y"])])))))))
    );
    // tactics.p017  // idx 5
    (
        Imp
            (Or (Atom (R ("p",[Var "a"])),Atom (R ("p",[Var "b"]))),
                 Imp (Atom (R ("q",[])),Exists ("y",Atom (R ("p",[Var "y"])))))
    );
    // tactics.p018  // idx 6
    (
        Imp
            (And
                (Or (Atom (R ("p",[Var "a"])),Atom (R ("p",[Var "b"]))),
                Forall
                    ("x",
                    Imp
                        (Atom (R ("p",[Var "x"])),
                        Atom (R ("p",[Fn ("f",[Var "x"])]))))),
                Exists ("y",Atom (R ("p",[Fn ("f",[Var "y"])]))))
    );
    // tactics.p019  // idx 7
    (
        Imp
            (Exists ("x",Atom (R ("p",[Var "x"]))),
            Imp
                (Forall
                    ("x",
                    Imp
                        (Atom (R ("p",[Var "x"])),
                        Atom (R ("p",[Fn ("f",[Var "x"])])))),
                Exists ("y",Atom (R ("p",[Fn ("f",[Var "y"])])))))
    );
    // tactics.p020  // idx 8
    (
        Imp
            (Forall
                ("x",Imp (Atom (R ("p",[Var "x"])),Atom (R ("q",[Var "x"])))),
                Imp
                    (Forall
                        ("x",Imp (Atom (R ("q",[Var "x"])),Atom (R ("p",[Var "x"])))),
                    Iff (Atom (R ("p",[Var "a"])),Atom (R ("q",[Var "a"])))))
    );
    |]

// pg. 514
// ------------------------------------------------------------------------- //
// A simple example.                                                         //
// ------------------------------------------------------------------------- //

// tactics.p005
// Dijkstra #1
[<Test>]
let ``Dijkstra #1 seperate`` () = 
    let g0 = set_goal (parse @"(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ (forall x y. x <= y ==> g(x) <= g(y))")
    let g1 = imp_intro_tac "ant" g0
    let g2 = conj_intro_tac g1
    let g3 = funpow 2 (auto_tac by ["ant"]) g2
    extract_thm g3
    |> should equal reslutValues.[0]

// pg. 514
// ------------------------------------------------------------------------- //
// All packaged up together.                                                 //
// ------------------------------------------------------------------------- //

// tactics.p006
// Dijkstra #1
[<Test>]
let ``Dijkstra #1 combined``() = 
    prove (parse @"(forall x. x <= x) /\(forall x y z. x <= y /\ y <= z ==> x <= z) /\(forall x y. f(x) <= y <=> x <= g(y))==> (forall x y. x <= y ==> f(x) <= f(y)) /\ (forall x y. x <= y ==> g(x) <= g(y))")
            [imp_intro_tac "ant";
            conj_intro_tac;
            auto_tac by ["ant"];
            auto_tac by ["ant"]] 
    |> should equal reslutValues.[0]

// pg. 518
// ------------------------------------------------------------------------- //
// A simple example.                                                         //
// ------------------------------------------------------------------------- //

// tactics.p007
// Dijkstra #3
[<Test>]
let ``tactics.p007``() = 
    prove (parse @"(forall x y. x <= y <=> x * y = x) /\ (forall x y. f(x * y) = f(x) * f(y)) ==> forall x y. x <= y ==> f(x) <= f(y)") [note("eq_sym",(parse @"forall x y. x = y ==> y = x"))
    using [eq_sym (parset "x") (parset "y")];
    note("eq_trans",(parse @"forall x y z. x = y /\ y = z ==> x = z"))
    using [eq_trans (parset "x") (parset "y") (parset "z")];
    note("eq_cong",(parse @"forall x y. x = y ==> f(x) = f(y)"))
    using [axiom_funcong "f" [(parset "x")] [(parset "y")]];
    assume ["le",(parse @"forall x y. x <= y <=> x * y = x");
            "hom",(parse @"forall x y. f(x * y) = f(x) * f(y)")];
    fix "x"; fix "y";
    assume ["xy",(parse @"x <= y")];
    so have (parse @"x * y = x") by ["le"];
    so have (parse @"f(x * y) = f(x)") by ["eq_cong"];
    so have (parse @"f(x) = f(x * y)") by ["eq_sym"];
    so have (parse @"f(x) = f(x) * f(y)") by ["eq_trans"; "hom"];
    so have (parse @"f(x) * f(y) = f(x)") by ["eq_sym"];
    so conclude (parse @"f(x) <= f(y)") by ["le"];
    qed] 
    |> should equal reslutValues.[1]

// ------------------------------------------------------------------------- //
// More examples not in the main text.                                       //
// ------------------------------------------------------------------------- //

// tactics.p008
[<Test>]
let ``tactics.p008``() = 
    prove
        (parse @"(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")
        [assume ["A",(parse @"exists x. p(x)")];
        assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
        note ("C",(parse @"forall x. p(x) ==> p(f(f(f(f(x)))))"))
        proof
        [have (parse @"forall x. p(x) ==> p(f(f(x)))") by ["B"];
            so conclude (parse @"forall x. p(x) ==> p(f(f(f(f(x)))))") at once;
            qed];
        consider ("a",(parse @"p(a)")) by ["A"];
        take (parset "a");
        so conclude (parse @"p(f(f(f(f(a)))))") by ["C"];
        qed] 
    |> should equal reslutValues.[2]

// ------------------------------------------------------------------------- //
// Alternative formulation with lemma construct.                             //
// ------------------------------------------------------------------------- //

// tactics.p009
[<Test>]
let ``prove using lemma``() = 
    let lemma (s,p) = function
        | (Goals((asl,w)::gls,jfn) as gl) ->
            Goals((asl,p)::((s,p)::asl,w)::gls,
                function (thp::thw::oths) ->
                            jfn(imp_unduplicate(imp_trans thp (shunt thw)) :: oths)
                       | _ -> failwith "malformed input")
        | _ -> failwith "malformed lemma"
    prove
        (parse @"(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")
        [assume ["A",(parse @"exists x. p(x)")];
        assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
        lemma ("C",(parse @"forall x. p(x) ==> p(f(f(f(f(x)))))"));
            have (parse @"forall x. p(x) ==> p(f(f(x)))") by ["B"];
            so conclude (parse @"forall x. p(x) ==> p(f(f(f(f(x)))))") at once;
            qed;
        consider ("a",(parse @"p(a)")) by ["A"];
        take (parset "a");
        so conclude (parse @"p(f(f(f(f(a)))))") by ["C"];
        qed] 
    |> should equal reslutValues.[2]

// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// tactics.p011
[<Test>]
let ``tactics.p011``() = 
    prove (parse @"p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
            [our thesis at once;
            qed] 
    |> should equal reslutValues.[3]

// tactics.p012
[<Test>]
let ``tactics.p012``() = 
    prove
        (parse @"(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")
        [assume ["A",(parse @"exists x. p(x)")];
        assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
        note ("C",(parse @"forall x. p(x) ==> p(f(f(f(f(x)))))")) proof
        [have (parse @"forall x. p(x) ==> p(f(f(x)))") by ["B"];
            so our thesis at once;
            qed];
        consider ("a",(parse @"p(a)")) by ["A"];
        take (parset "a");
        so our thesis by ["C"];
        qed] 
    |> should equal reslutValues.[2]

// tactics.p013
[<Test>]
let ``tactics.p013``() = 
    prove (parse @"forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
            [fix "c";
            assume ["A",(parse @"p(c)")];
            assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
            take (parset "c");
            conclude (parse @"p(c)") by ["A"];
            note ("C",(parse @"p(c) ==> p(f(c))")) by ["B"];
            so our thesis by ["C"; "A"];
            qed] 
    |> should equal reslutValues.[4]

// tactics.p014
[<Test>]
let ``tactics.p014``() = 
    prove (parse @"p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
            [assume ["A",(parse @"p(a)")];
            assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
            take (parset "a");
            conclude (parse @"p(a)") by ["A"];
            our thesis by ["A"; "B"];
            qed] 
    |> should equal reslutValues.[3]

// tactics.p015
[<Test>]
let ``tactics.p015``() = 
    prove (parse @"forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
            [fix "c";
            assume ["A",(parse @"p(c)")];
            assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
            take (parset "c");
            conclude (parse @"p(c)") by ["A"];
            note ("C",(parse @"p(c) ==> p(f(c))")) by ["B"];
            our thesis by ["C"; "A"];
            qed] 
    |> should equal reslutValues.[4]

// tactics.p016
[<Test>]
let ``tactics.p016``() = 
    prove (parse @"forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
            [fix "c";
            assume ["A",(parse @"p(c)")];
            assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
            take (parset "c");
            note ("D",(parse @"p(c)")) by ["A"];
            note ("C",(parse @"p(c) ==> p(f(c))")) by ["B"];
            our thesis by ["C"; "A"; "D"];
            qed] 
    |> should equal reslutValues.[4]

// tactics.p017
[<Test>]
let ``tactics.p017``() = 
    prove (parse @"(p(a) \/ p(b)) ==> q ==> exists y. p(y)")
        [assume ["A",(parse @"p(a) \/ p(b)")];
        assume ["",(parse @"q")];
        cases (parse @"p(a) \/ p(b)") by ["A"];
            take (parset "a");
            so our thesis at once;
            qed;
            take (parset "b");
            so our thesis at once;
            qed] 
    |> should equal reslutValues.[5]
        
// tactics.p018 
[<Test>]
let ``tactics.p018``() = 
    let v1 = "A"
    let v2 = (parse @"p(a)")
    prove
        (parse @"(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))")
        [assume ["base",(parse @"p(a) \/ p(b)");
                "Step",(parse @"forall x. p(x) ==> p(f(x))")];
        cases (parse @"p(a) \/ p(b)") by ["base"]; 
            so note (v1, v2) at once; // use function app instead of value
            note ("X",(parse @"p(a) ==> p(f(a))")) by ["Step"];
            take (parset "a");
            our thesis by ["A"; "X"];
            qed;
            take (parset "b");
            so our thesis by ["Step"];
            qed] 
    |> should equal reslutValues.[6]

// tactics.p019
[<Test>]
let ``tactics.p019``() = 
    prove
        (parse @"(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))")
        [assume ["A",(parse @"exists x. p(x)")];
        assume ["B",(parse @"forall x. p(x) ==> p(f(x))")];
        consider ("a",(parse @"p(a)")) by ["A"];
        so note ("concl",(parse @"p(f(a))")) by ["B"];
        take (parset "a");
        our thesis by ["concl"];
        qed] 
    |> should equal reslutValues.[7]

// tactics.p020
[<Test>]
let ``tactics.p020``() = 
    prove (parse @"(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x))
            ==> (p(a) <=> q(a))")
        [assume ["A",(parse @"forall x. p(x) ==> q(x)")];
        assume ["B",(parse @"forall x. q(x) ==> p(x)")];
        note ("von",(parse @"p(a) ==> q(a)")) by ["A"];
        note ("bis",(parse @"q(a) ==> p(a)")) by ["B"];
        our thesis by ["von"; "bis"];
        qed] 
    |> should equal reslutValues.[8]
