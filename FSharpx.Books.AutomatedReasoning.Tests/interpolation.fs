// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.interpolation

open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.interpolation

open NUnit.Framework
open FsUnit

let test_interp fm =
    let rec p = generalize (skolemize fm)
    and q = generalize (skolemize (Not fm))
    let c = interpolate p q
    meson002(Imp(And(p,q),formula.False)) |> ignore
    meson002(Imp(p,c)) |> ignore
    meson002(Imp(q,Not c)) |> ignore
    c

let private interpValues : (string * formula<fol>)[] = [| 
    (
        // idx 0
        // interpolation.p024
        @"forall x. P(x) ==> exists y. forall z. P(z) ==> Q(y)",
        Forall
          ("v_2",
           Exists
             ("v_1",
              Or
                (Or
                   (Not (Atom (R ("P",[Var "v_2"]))),
                    Or
                      (Not (Atom (R ("P",[Var "v_2"]))),
                       Atom (R ("Q",[Var "v_1"])))),
                 And
                   (Or
                      (Not (Atom (R ("P",[Var "v_2"]))),
                       Or
                         (Not (Atom (R ("P",[Var "v_2"]))),
                          Atom (R ("Q",[Var "v_1"])))),
                    Or
                      (Not (Atom (R ("P",[Var "v_2"]))),
                       Atom (R ("Q",[Var "v_1"])))))))
    );
    (
        // idx 1
        // interpolation.p025
        @"forall y. exists y. forall z. exists a. P(a,x,y,z) ==> P(x,y,z,a)",
        formula<fol>.True
    );
    |]


[<TestCase(0, TestName = "interpolation.p024")>]
[<TestCase(1, TestName = "interpolation.p025")>]

[<Test>]
let ``interp tests`` idx = 
    let (formula, _) = interpValues.[idx]
    let (_, result) = interpValues.[idx]
    test_interp (parse formula)
    |> should equal result

let private interpolationValues : (formula<fol> * formula<fol> * (formula<fol> -> formula<fol> -> formula<fol>) * int list * int list)[] = [| 
    (
        // idx 0
        // interpolation.p001
        // interpolation.p002
        // interpolation.p003
        // interpolation.p004
        // interpolation.p005
        prenex (parse @"(forall x. R(x,f(x))) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))"),
        prenex (parse @"(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(0,0)"),
        (fun x y -> urinterpolate x y),
        [2; 2],
        [3]
    );
    (
        // idx 1
        // interpolation.p006
        // interpolation.p007
        // interpolation.p008
        prenex (parse @"(forall x. R(x,f(x))) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))"),
        prenex (parse @"(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(0,0)"),
        (fun x y -> uinterpolate x y),
        [4],
        [3]
    );
    (
        // idx 2
        // interpolation.p009
        // interpolation.p010
        // interpolation.p011
        parse @"(forall x. exists y. R(x,y)) /\ (forall x y. S(v,x,y) <=> R(x,y) \/ R(y,x))",
        parse @"(forall x y z. S(v,x,y) /\ S(v,y,z) ==> T(x,z)) /\ (exists u. ~T(u,u))",
        (fun x y -> interpolate x y),
        [4],
        [3]
    );
    (
        // idx 3
        // interpolation.p026
        // interpolation.p027
        // interpolation.p028
        parse @"forall x. L(x,b)",
        parse @"(forall y. L(b,y) ==> m = y) /\ ~(m = b)",
        (fun x y -> einterpolate x y),
        [1],
        [2]
    );
    (
        // idx 4
        // interpolation.p029
        // interpolation.p030
        // interpolation.p031
        parse @"(forall x. A(x) /\ C(x) ==> B(x)) /\ (forall x. D(x) \/ ~D(x) ==> C(x))",
        parse @"~(forall x. E(x) ==> A(x) ==> B(x))",
        (fun x y -> einterpolate x y),
        [5],
        [2]
    );
    |]

[<TestCase(0, TestName = "interpolation.p005")>]
[<TestCase(1, TestName = "interpolation.p008")>]
[<TestCase(2, TestName = "interpolation.p011")>]
[<TestCase(3, TestName = "interpolation.p028")>]
[<TestCase(4, TestName = "interpolation.p028")>]

[<Test>]
let ``interpolation meson002 1 tests`` idx = 
    let (formula1, _, _, _, _) = interpolationValues.[idx]
    let (_, formula2, _, _, _) = interpolationValues.[idx]
    let (_, _, func, _, _) = interpolationValues.[idx]
    let (_, _, _, result1, _) = interpolationValues.[idx]
    let (_, _, _, _, result2) = interpolationValues.[idx]
    let formula3 = func formula1 formula2
    meson002(Imp(formula1,formula3)) |> should equal result1
    meson002(Imp(formula2,Not formula3)) |> should equal result2

let private interpolationBoolValues : (formula<fol> * formula<fol> * (formula<fol> -> formula<fol> -> formula<fol>) * bool * bool * bool)[] = [| 
    (
        // idx 3
        // interpolation.p012
        // interpolation.p013
        // interpolation.p014
        // interpolation.p015
        parse @"(p ==> q /\ r)",
        parse @"~((q ==> p) ==> s ==> (p <=> q))",
        (fun x y -> interpolate x y),
        true,
        true,
        true
    );
    |]

[<TestCase(0, TestName = "interpolation.p015")>]

[<Test>]
let ``interpolation tautology tests`` idx = 
    let (formula1, _, _, _, _, _) = interpolationBoolValues.[idx]
    let (_, formula2, _, _, _, _) = interpolationBoolValues.[idx]
    let (_, _, func, _, _, _) = interpolationBoolValues.[idx]
    let (_, _, _, result1, _, _) = interpolationBoolValues.[idx]
    let (_, _, _, _, result2, _) = interpolationBoolValues.[idx]
    let (_, _, _, _, _, result3) = interpolationBoolValues.[idx]
    let formula3 = func formula1 formula2
    tautology(Imp(And(formula1,formula2),formula<fol>.False)) |> should equal result1
    tautology(Imp(formula1,formula3)) |> should equal result2
    tautology(Imp(formula2,Not formula3)) |> should equal result3

let private interpolation2Values : (formula<fol> * formula<fol> * (formula<fol> -> formula<fol> -> formula<fol>) * int list * int list * int list)[] = [| 
    (
        // idx 0
        // interpolation.p016
        // interpolation.p017
        // interpolation.p018
        // interpolation.p019
        parse @"(forall x. exists y. R(x,y)) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))",
        parse @"(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)",
        (fun x y -> interpolate x y),
        [5],
        [4],
        [3]
    );
    (
        // idx 1
        // interpolation.p020
        // interpolation.p021
        // interpolation.p022
        // interpolation.p023
        parse @"(forall x. exists y. R(x,y)) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x)) /\ (forall v. R(u,v) ==> Q(v,u))",
        parse @"(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)",
        (fun x y -> interpolate x y),
        [5],
        [4],
        [3]
    );
    |]

[<TestCase(0, TestName = "interpolation.p019")>]
[<TestCase(1, TestName = "interpolation.p023")>]

[<Test>]
let ``interpolation meson002 2 tests`` idx = 
    let (formula1, _, _, _, _, _) = interpolation2Values.[idx]
    let (_, formula2, _, _, _, _) = interpolation2Values.[idx]
    let (_, _, func, _, _, _) = interpolation2Values.[idx]
    let (_, _, _, result1, _, _) = interpolation2Values.[idx]
    let (_, _, _, _, result2, _) = interpolation2Values.[idx]
    let (_, _, _, _, _, result3) = interpolation2Values.[idx]
    let formula3 = func formula1 formula2
    meson002(Imp(And(formula1,formula2),formula<fol>.False)) |> should equal result1
    meson002(Imp(formula1,formula3)) |> should equal result2
    meson002(Imp(formula2,Not formula3)) |> should equal result3
