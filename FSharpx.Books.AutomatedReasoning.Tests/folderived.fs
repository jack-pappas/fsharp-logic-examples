// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.folderived

open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.folderived

open NUnit.Framework
open FsUnit

let private icongruenceValues : (string * string * string * string * thm * string)[] = [| 
    (
        // idx 0
        // folderived.p001 
        @"s", 
        @"t", 
        @"f(s,g(s,t,s),u,h(h(s)))", 
        @"f(s,g(t,t,s),u,h(h(t)))",
        Imp
            (Atom (R ("=",[Var "s"; Var "t"])),
            Atom
                (R ("=",
                    [Fn
                        ("f",
                            [Var "s"; Fn ("g",[Var "s"; Var "t"; Var "s"]); Var "u";
                            Fn ("h",[Fn ("h",[Var "s"])])]);
                    Fn
                        ("f",
                            [Var "s"; Fn ("g",[Var "t"; Var "t"; Var "s"]); Var "u";
                            Fn ("h",[Fn ("h",[Var "t"])])])]))),
        @"|- s =t ==> f(s,g(s,t,s),u,h(h(s))) =f(s,g(t,t,s),u,h(h(t)))"
    );
    |]

[<TestCase(0, TestName = "folderived.p001")>]

[<Test>]
let ``icongruence ast tests`` idx = 
    let (s, _, _, _, _, _) = icongruenceValues.[idx]
    let (_, t, _, _, _, _) = icongruenceValues.[idx]
    let (_, _, stm, _, _, _) = icongruenceValues.[idx]
    let (_, _, _, ttm, _, _) = icongruenceValues.[idx]
    let (_, _, _, _, ast_result, _) = icongruenceValues.[idx]
    icongruence (parset s) (parset t) (parset stm) (parset ttm)
    |> should equal ast_result

[<TestCase(0, TestName = "folderived.p001")>]

[<Test>]
let ``icongruence pp tests`` idx = 
    let (s, _, _, _, _, _) = icongruenceValues.[idx]
    let (_, t, _, _, _, _) = icongruenceValues.[idx]
    let (_, _, stm, _, _, _) = icongruenceValues.[idx]
    let (_, _, _, ttm, _, _) = icongruenceValues.[idx]
    let (_, _, _, _, _, pretty_printer_result) = icongruenceValues.[idx]
    icongruence (parset s) (parset t) (parset stm) (parset ttm)
    |> sprint_thm
    |> should equal pretty_printer_result

let private ispecValues : (string * string * thm * string)[] = [| 
    (
        // idx 0
        // folderived.p002
        @"y", 
        @"forall x y z. x + y + z = z + y + x", 
        Imp
            (Forall
                ("x",
                Forall
                    ("y",
                    Forall
                        ("z",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
                                Fn ("+",[Var "z"; Fn ("+",[Var "y"; Var "x"])])]))))),
            Forall
                ("y'",
                Forall
                    ("z",
                    Atom
                        (R ("=",
                            [Fn ("+",[Var "y"; Fn ("+",[Var "y'"; Var "z"])]);
                            Fn ("+",[Var "z"; Fn ("+",[Var "y'"; Var "y"])])]))))),
        @"|- (forall x y z. x +y +z =z +y +x) ==> (forall y' z. y +y' +z =z +y' +y)"
    );
    (
        // idx 1
        // folderived.p005
        @"x", 
        @"forall x y z. x + y + z = y + z + z", 
        Imp
            (Forall
                ("x",
                Forall
                    ("y",
                    Forall
                        ("z",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
                                Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])]))))),
            Forall
                ("y",
                Forall
                    ("z",
                    Atom
                        (R ("=",
                            [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
                            Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])]))))),
        @"|- (forall x y z. x +y +z =y +z +z) ==> (forall y z. x +y +z =y +z +z)"
    );
    (
        // idx 2
        // folderived.p006
        @"x", 
        @"forall x. x = x", 
        Imp
            (Forall ("x",Atom (R ("=",[Var "x"; Var "x"]))),
            Atom (R ("=",[Var "x"; Var "x"]))),
        @"|- (forall x. x =x) ==> x =x"
    );
    (
        // idx 3
        // folderived.p007
        @"w + y + z", 
        @"forall x y z. x + y + z = y + z + z", 
        Imp
            (Forall
                ("x",
                Forall
                    ("y",
                    Forall
                        ("z",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
                                Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])]))))),
            Forall
                ("y'",
                Forall
                    ("z'",
                    Atom
                        (R ("=",
                            [Fn
                                ("+",
                                [Fn ("+",[Var "w"; Fn ("+",[Var "y"; Var "z"])]);
                                 Fn ("+",[Var "y'"; Var "z'"])]);
                            Fn ("+",[Var "y'"; Fn ("+",[Var "z'"; Var "z'"])])]))))),
        @"|- (forall x y z. x +y +z =y +z +z) ==> (forall y' z'. (w +y +z) +y' +z' =y' +z' +z')"
    );
    (
        // idx 4
        // folderived.p008
        @"x + y + z", 
        @"forall x y z. x + y + z = y + z + z", 
        Imp
            (Forall
                ("x",
                Forall
                    ("y",
                    Forall
                        ("z",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
                                Fn ("+",[Var "y"; Fn ("+",[Var "z"; Var "z"])])]))))),
            Forall
                ("y'",
                Forall
                    ("z'",
                    Atom
                        (R ("=",
                            [Fn
                                ("+",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])]);
                                Fn ("+",[Var "y'"; Var "z'"])]);
                             Fn ("+",[Var "y'"; Fn ("+",[Var "z'"; Var "z'"])])]))))),
        @"|- (forall x y z. x +y +z =y +z +z) ==> (forall y' z'. (x +y +z) +y' +z' =y' +z' +z')"
    );
    (
        // idx 5
        // folderived.p009
        @"x + y + z", 
        @"forall x y z. nothing_much", 
        Imp
            (Forall ("x",Forall ("y",Forall ("z",Atom (R ("nothing_much",[]))))),
            Forall ("y",Forall ("z",Atom (R ("nothing_much",[]))))),
        @"|- (forall x y z. nothing_much) ==> (forall y z. nothing_much)"
    );
    (
        // idx 6
        // folderived.p013
        @"x'", 
        @"forall x x' x''. x + x' + x'' = 0", 
        Imp
            (Forall
                ("x",
                Forall
                    ("x'",
                    Forall
                        ("x''",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
                                Fn ("0",[])]))))),
            Forall
                ("x''",
                Forall
                    ("x'''",
                    Atom
                        (R ("=",
                            [Fn ("+",[Var "x'"; Fn ("+",[Var "x''"; Var "x'''"])]);
                            Fn ("0",[])]))))),
        @"|- (forall x x' x''. x +x' +x'' =0) ==> (forall x'' x'''. x' +x'' +x''' =0)"
    );
    (
        // idx 7
        // folderived.p014
        @"x''", 
        @"forall x x' x''. x + x' + x'' = 0", 
        Imp
            (Forall
                ("x",
                Forall
                    ("x'",
                    Forall
                        ("x''",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
                                Fn ("0",[])]))))),
            Forall
                ("x'",
                Forall
                    ("x'''",
                    Atom
                        (R ("=",
                            [Fn ("+",[Var "x''"; Fn ("+",[Var "x'"; Var "x'''"])]);
                            Fn ("0",[])]))))),
        @"|- (forall x x' x''. x +x' +x'' =0) ==> (forall x' x'''. x'' +x' +x''' =0)"
    );
    (
        // idx 8
        // folderived.p015
        @"x' + x''", 
        @"forall x x' x''. x + x' + x'' = 0", 
        Imp
            (Forall
                ("x",
                Forall
                    ("x'",
                    Forall
                        ("x''",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
                                Fn ("0",[])]))))),
            Forall
                ("x'''",
                Forall
                    ("x''''",
                    Atom
                        (R ("=",
                            [Fn
                                ("+",
                                [Fn ("+",[Var "x'"; Var "x''"]);
                                 Fn ("+",[Var "x'''"; Var "x''''"])]); Fn ("0",[])]))))),
        @"|- (forall x x' x''. x +x' +x'' =0) ==> (forall x''' x''''. (x' +x'') +x''' +x'''' =0)"
    );
    (
        // idx 9
        // folderived.p016
        @"x + x' + x''", 
        @"forall x x' x''. x + x' + x'' = 0", 
        Imp
            (Forall
                ("x",
                Forall
                    ("x'",
                    Forall
                        ("x''",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
                                Fn ("0",[])]))))),
            Forall
                ("x'''",
                Forall
                    ("x''''",
                    Atom
                        (R ("=",
                            [Fn
                                ("+",
                                [Fn ("+",[Var "x"; Fn ("+",[Var "x'"; Var "x''"])]);
                                Fn ("+",[Var "x'''"; Var "x''''"])]); Fn ("0",[])]))))),
        @"|- (forall x x' x''. x +x' +x'' =0) ==> (forall x''' x''''. (x +x' +x'') +x''' +x'''' =0)"
    );
    (
        // idx 10
        // folderived.p017
        @"2 * x", 
        @"forall x x'. x + x' = x' + x", 
        Imp
            (Forall
                ("x",
                Forall
                    ("x'",
                    Atom
                        (R ("=",
                            [Fn ("+",[Var "x"; Var "x'"]);
                            Fn ("+",[Var "x'"; Var "x"])])))),
            Forall
                ("x'",
                Atom
                    (R ("=",
                        [Fn ("+",[Fn ("*",[Fn ("2",[]); Var "x"]); Var "x'"]);
                        Fn ("+",[Var "x'"; Fn ("*",[Fn ("2",[]); Var "x"])])])))),
        @"|- (forall x x'. x +x' =x' +x) ==> (forall x'. 2 *x +x' =x' +2 *x)"
    );
    |]

[<TestCase(0, TestName = "folderived.p002")>]
[<TestCase(1, TestName = "folderived.p005")>]
[<TestCase(2, TestName = "folderived.p006")>]
[<TestCase(3, TestName = "folderived.p007")>]
[<TestCase(4, TestName = "folderived.p008")>]
[<TestCase(5, TestName = "folderived.p009")>]
[<TestCase(6, TestName = "folderived.p013")>]
[<TestCase(7, TestName = "folderived.p014")>]
[<TestCase(8, TestName = "folderived.p015")>]
[<TestCase(9, TestName = "folderived.p016")>]
[<TestCase(10, TestName = "folderived.p017")>]

[<Test>]
let ``ispec ast tests`` idx = 
    let (term, _, _, _) = ispecValues.[idx]
    let (_, formula, _, _) = ispecValues.[idx]
    let (_, _, ast_result, _) = ispecValues.[idx]
    ispec (parset term) (parse formula)
    |> should equal ast_result

[<TestCase(0, TestName = "folderived.p002")>]
[<TestCase(1, TestName = "folderived.p005")>]
[<TestCase(2, TestName = "folderived.p006")>]
[<TestCase(3, TestName = "folderived.p007")>]
[<TestCase(4, TestName = "folderived.p008")>]
[<TestCase(5, TestName = "folderived.p009")>]
[<TestCase(6, TestName = "folderived.p013")>]
[<TestCase(7, TestName = "folderived.p014")>]
[<TestCase(8, TestName = "folderived.p015")>]
[<TestCase(9, TestName = "folderived.p016")>]
[<TestCase(10, TestName = "folderived.p017")>]

[<Test>]
let ``ispec pp tests`` idx = 
    let (term, _, _, _) = ispecValues.[idx]
    let (_, formula, _, _) = ispecValues.[idx]
    let (_, _, _, pretty_printer_result) = ispecValues.[idx]
    ispec (parset term) (parse formula)
    |> sprint_thm
    |> should equal pretty_printer_result


let private isubstValues : (string * string * string * string * thm * string)[] = [| 
    (
        // idx 0
        // folderived.p003 
        @"x + x", 
        @"2 * x", 
        @"x + x = x ==> x = 0", 
        @"2 * x = x ==> x = 0",
        Imp
            (Atom
                (R ("=",
                    [Fn ("+",[Var "x"; Var "x"]); Fn ("*",[Fn ("2",[]); Var "x"])])),
            Imp
                (Imp
                    (Atom (R ("=",[Fn ("+",[Var "x"; Var "x"]); Var "x"])),
                    Atom (R ("=",[Var "x"; Fn ("0",[])]))),
                Imp
                    (Atom (R ("=",[Fn ("*",[Fn ("2",[]); Var "x"]); Var "x"])),
                    Atom (R ("=",[Var "x"; Fn ("0",[])]))))),
        @"|- x +x =2 *x ==> (x +x =x ==> x =0) ==> 2 *x =x ==> x =0"
    );
    (
        // idx 1
        // folderived.p004
        @"x + x", 
        @"2 * x", 
        @"(x + x = y + y) ==> (y + y + y = x + x + x)", 
        @"2 * x = y + y ==> y + y + y = x + 2 * x",
        Imp
            (Atom
                (R ("=",
                    [Fn ("+",[Var "x"; Var "x"]); Fn ("*",[Fn ("2",[]); Var "x"])])),
            Imp
                (Imp
                    (Atom
                        (R ("=",
                            [Fn ("+",[Var "x"; Var "x"]);
                            Fn ("+",[Var "y"; Var "y"])])),
                    Atom
                        (R ("=",
                            [Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])]);
                            Fn ("+",[Var "x"; Fn ("+",[Var "x"; Var "x"])])]))),
                Imp
                    (Atom
                        (R ("=",
                            [Fn ("*",[Fn ("2",[]); Var "x"]);
                            Fn ("+",[Var "y"; Var "y"])])),
                    Atom
                        (R ("=",
                            [Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])]);
                            Fn ("+",[Var "x"; Fn ("*",[Fn ("2",[]); Var "x"])])]))))),
        @"|- x +x =2 *x ==> (x +x =y +y ==> y +y +y =x +x +x) ==> 2 *x =y +y ==> y +y +y =x +2 *x"
    );
    (
        // idx 2
        // folderived.p010
        // TODO: This is missing a formula in original OCaml code. Need update from John.
        @"x + x", 
        @"2 * x", 
        "(x + x = y + y) <=> (something \/ y + y + y = x + x + x)", 
        @"missing formula",
        formula<fol>.False,
        @"place_holder"
    );
    (
        // idx 3
        // folderived.p011
        @"x + x", 
        @"2 * x", 
        @"(exists x. x = 2) <=> exists y. y + x + x = y + y + y", 
        @"(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)",
        Imp
            (Atom
                (R ("=",
                    [Fn ("+",[Var "x"; Var "x"]); Fn ("*",[Fn ("2",[]); Var "x"])])),
            Imp
               (Iff
                    (Exists ("x",Atom (R ("=",[Var "x"; Fn ("2",[])]))),
                    Exists
                        ("y",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "y"; Fn ("+",[Var "x"; Var "x"])]);
                                Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])])])))),
                Iff
                    (Exists ("x",Atom (R ("=",[Var "x"; Fn ("2",[])]))),
                    Exists
                        ("y",
                        Atom
                            (R ("=",
                                [Fn ("+",[Var "y"; Fn ("*",[Fn ("2",[]); Var "x"])]);
                                Fn ("+",[Var "y"; Fn ("+",[Var "y"; Var "y"])])])))))),
        @"|- x +x =2 *x ==> ((exists x. x =2) <=> (exists y. y +x +x =y +y +y)) ==> ((exists x. x =2) <=> (exists y. y +2 *x =y +y +y))"
    );
    (
        // idx 4
        // folderived.p012
        @"x", 
        @"y", 
        @"(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)", 
        @"(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)",
        Imp
            (Atom (R ("=",[Var "x"; Var "y"])),
            Imp
                (Iff
                    (Forall ("z",Atom (R ("=",[Var "x"; Var "z"]))),
                    And
                        (Exists ("x",Atom (R ("<",[Var "y"; Var "z"]))),
                        Forall ("y",Atom (R ("<",[Var "y"; Var "x"]))))),
                Iff
                    (Forall ("z",Atom (R ("=",[Var "y"; Var "z"]))),
                    And
                        (Exists ("x",Atom (R ("<",[Var "y"; Var "z"]))),
                        Forall ("y'",Atom (R ("<",[Var "y'"; Var "y"]))))))),
        @"|- x =y ==> ((forall z. x =z) <=> (exists x. y <z) /\ (forall y. y <x)) ==> ((forall z. y =z) <=> (exists x. y <z) /\ (forall y'. y' <y))"
    );
    |]

[<TestCase(0, TestName = "folderived.p003")>]
[<TestCase(1, TestName = "folderived.p004")>]
[<TestCase(3, TestName = "folderived.p011")>]
[<TestCase(4, TestName = "folderived.p012")>]

[<Test>]
let ``isubst ast tests`` idx = 
    let (s, _, _, _, _, _) = isubstValues.[idx]
    let (_, t, _, _, _, _) = isubstValues.[idx]
    let (_, _, stm, _, _, _) = isubstValues.[idx]
    let (_, _, _, ttm, _, _) = isubstValues.[idx]
    let (_, _, _, _, ast_result, _) = isubstValues.[idx]
    isubst (parset s) (parset t) (parse stm) (parse ttm)
    |> should equal ast_result
    
[<TestCase(0, TestName = "folderived.p003")>]
[<TestCase(1, TestName = "folderived.p004")>]
[<TestCase(3, TestName = "folderived.p011")>]
[<TestCase(4, TestName = "folderived.p012")>]

[<Test>]
let ``isubst pp tests`` idx = 
    let (s, _, _, _, _, _) = isubstValues.[idx]
    let (_, t, _, _, _, _) = isubstValues.[idx]
    let (_, _, stm, _, _, _) = isubstValues.[idx]
    let (_, _, _, ttm, _, _) = isubstValues.[idx]
    let (_, _, _, _, _, pretty_printer_result) = isubstValues.[idx]
    isubst (parset s) (parset t) (parse stm) (parse ttm)
    |> sprint_thm
    |> should equal pretty_printer_result
