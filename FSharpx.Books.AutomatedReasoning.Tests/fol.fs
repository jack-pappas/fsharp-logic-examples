// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module FSharpx.Books.AutomatedReasoning.Tests.fol

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
    
open NUnit.Framework
open FsUnit

let private termValues : (term * string)[] = [|
    (
        // idx 0
        // fol.p001
        Fn("sqrt",[Fn("-",[Fn("1",[]);
                           Fn("power",[Fn("cos",[Fn("+",[Var "x"; Var "y"])]);
                                       Fn("2",[])])])]),
        @"<<|sqrt(1 -power(cos(x +y),2))|>>"
    )
    |]

[<Test>]
[<TestCase(0, TestName = "fol.p001")>]
let ``sprint_term tests`` idx =
    let (term, _) = termValues.[idx]
    let (_, stringResult) = termValues.[idx]
    sprint_term term
    |> should equal stringResult
    
let private folFormulaValues : (formula<fol> * string)[] = [|
    (
        // idx 0
        // fol.p002
        Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"])),
        @"<<x +y <z>>"
    )
    |]

[<Test>]
[<TestCase(0, TestName = "fol.p002")>]
let ``sprint_fol_formula tests`` idx =
    let (formula, _) = folFormulaValues.[idx]
    let (_, stringResult) = folFormulaValues.[idx]
    sprint_fol_formula formula
    |> should equal stringResult

let private parsetValues : (string * term * string)[] = [|
    (
        // idx 0
        // fol.p004
        @"2 * x",
        Fn ("*",[Fn ("2",[]); Var "x"]),
        @"<<|2 *x|>>"
    )
    |]

[<Test>]
[<TestCase(0, TestName = "fol.p004")>]
let ``parset tests`` idx =
    let (term, _, _) = parsetValues.[idx]
    let (_, astResult, _) = parsetValues.[idx]
    let (_, _, stringResult) = parsetValues.[idx]
    let result = parset term 
    result
    |> should equal astResult
    sprint_term result
    |> should equal stringResult

let private parseValues : (string * formula<fol> * string)[] = [| 
    (
        // idx 0
        // fol.p005
        @"forall x y. exists z. x < z /\ y < z",
        Forall
          ("x",
           Forall
             ("y",
              Exists
                ("z",
                 And
                   (Atom (R ("<",[Var "x"; Var "z"])),
                    Atom (R ("<",[Var "y"; Var "z"])))))),
        @"<<forall x y. exists z. x <z /\ y <z>>"

    );
    (
        // idx 1
        // fol.p006
        @"~(forall x. P(x)) <=> exists y. ~P(y)",
        Iff
          (Not (Forall ("x",Atom (R ("P",[Var "x"])))),
           Exists ("y",Not (Atom (R ("P",[Var "y"]))))),
        @"<<~(forall x. P(x)) <=> (exists y. ~P(y))>>"
    );
    (
        // idx 2
        // fol.p018
        @"exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)",
        Exists ("a",
            Exists ("b",
                And (Atom (R (">", [Var "a"; Fn ("1", [])])),
                    And (Atom (R (">", [Var "b"; Fn ("1", [])])),
                        And
                            (Or (Atom (R ("=", [Fn ("*", [Fn ("2", []); Var "b"]); Var "a"])),
                                Atom
                                    (R ("=",
                                        [Fn ("*", [Fn ("2", []); Var "b"]);
                                         Fn ("+", [Fn ("*", [Fn ("3", []); Var "a"]); Fn ("1", [])])]))),
                            Atom (R ("=", [Var "a"; Var "b"]))))))),
        @"<<exists a b. a >1 /\ b >1 /\" + 
         " (2 *b =a \/ 2 *b =3 *a +1) /\ a =b>>"
    );
    (
        // idx 3
        // fol.p019
        @"((w + x)^4 + (w + y)^4 + (w + z)^4 +
           (x + y)^4 + (x + z)^4 + (y + z)^4 +
           (w - x)^4 + (w - y)^4 + (w - z)^4 +
           (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
           (w^2 + x^2 + y^2 + z^2)^2",
        Atom
          (R ("=",
              [Fn
                 ("/",
                  [Fn
                     ("+",
                      [Fn ("^",[Fn ("+",[Var "w"; Var "x"]); Fn ("4",[])]);
                       Fn
                         ("+",
                          [Fn ("^",[Fn ("+",[Var "w"; Var "y"]); Fn ("4",[])]);
                           Fn
                             ("+",
                              [Fn ("^",[Fn ("+",[Var "w"; Var "z"]); Fn ("4",[])]);
                               Fn
                                 ("+",
                                  [Fn ("^",[Fn ("+",[Var "x"; Var "y"]); Fn ("4",[])]);
                                   Fn
                                     ("+",
                                      [Fn
                                         ("^",[Fn ("+",[Var "x"; Var "z"]); Fn ("4",[])]);
                                       Fn
                                         ("+",
                                          [Fn
                                             ("^",
                                              [Fn ("+",[Var "y"; Var "z"]); Fn ("4",[])]);
                                           Fn
                                             ("+",
                                              [Fn
                                                 ("^",
                                                  [Fn ("-",[Var "w"; Var "x"]);
                                                   Fn ("4",[])]);
                                               Fn
                                                 ("+",
                                                  [Fn
                                                     ("^",
                                                      [Fn ("-",[Var "w"; Var "y"]);
                                                       Fn ("4",[])]);
                                                   Fn
                                                     ("+",
                                                      [Fn
                                                         ("^",
                                                          [Fn ("-",[Var "w"; Var "z"]);
                                                           Fn ("4",[])]);
                                                       Fn
                                                         ("+",
                                                          [Fn
                                                             ("^",
                                                              [Fn
                                                                 ("-",[Var "x"; Var "y"]);
                                                               Fn ("4",[])]);
                                                           Fn
                                                             ("+",
                                                              [Fn
                                                                 ("^",
                                                                  [Fn
                                                                     ("-",
                                                                      [Var "x"; Var "z"]);
                                                                   Fn ("4",[])]);
                                                               Fn
                                                                 ("^",
                                                                  [Fn
                                                                     ("-",
                                                                      [Var "y"; Var "z"]);
                                                                   Fn ("4",[])])])])])])])])])])])])]);
                   Fn ("6",[])]);
               Fn
                 ("^",
                  [Fn
                     ("+",
                      [Fn ("^",[Var "w"; Fn ("2",[])]);
                       Fn
                         ("+",
                          [Fn ("^",[Var "x"; Fn ("2",[])]);
                           Fn
                             ("+",
                              [Fn ("^",[Var "y"; Fn ("2",[])]);
                               Fn ("^",[Var "z"; Fn ("2",[])])])])]); Fn ("2",[])])])),
        @"<<((w +x)^4 +(w +y)^4 +(w +z)^4 +" + 
            "(x +y)^4 +(x +z)^4 +(y +z)^4 +" + 
            "(w -x)^4 +(w -y)^4 +(w -z)^4 +" + 
            "(x -y)^4 +(x -z)^4 +(y -z)^4) /6 =" + 
            "(w^2 +x^2 +y^2 +z^2)^2>>"
    )
    |]
    
[<Test>]
[<TestCase(0, TestName = "fol.p005")>]
[<TestCase(1, TestName = "fol.p006")>]
[<TestCase(2, TestName = "fol.p018")>]
[<TestCase(3, TestName = "fol.p019")>]
let ``parse tests`` (idx) =
    let (text, _, _) = parseValues.[idx]
    let (_, astResult, _) = parseValues.[idx]
    let (_, _, stringResult) = parseValues.[idx]
    let result = parse text
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult

let private holdsBoolValues : ((bool list * (string -> bool list -> bool) * (string -> bool list -> bool)) * func<string,bool> * string * bool)[] = [| 
    (
        // idx 0
        // fol.p007
        // Harrison #06 
        bool_interp,
        undefined,
        @"forall x. (x = 0) \/ (x = 1)",
        true
    );    
    |]
    
[<Test>]
[<TestCase(0, TestName = "fol.p007")>]
let ``holds tests (bool)`` idx = 
    let (interpretation, _, _, _) = holdsBoolValues.[idx]
    let (_, valuation, _, _) = holdsBoolValues.[idx]
    let (_, _, fol_formula, _) = holdsBoolValues.[idx]
    let (_, _, _, result) = holdsBoolValues.[idx]
    holds interpretation valuation (parse fol_formula)
    |> should equal result

let private holdIntValues : ((int list * (string -> int list -> int) * (string -> int list -> bool)) * func<string,int> * string * bool)[] = [| 
    (
        // idx 0
        // fol.p008
        // Harrison #06  
        (mod_interp 2),
        undefined,
        @"forall x. (x = 0) \/ (x = 1)",
        true
    );
    (
        // idx 1
        // fol.p009
        // Harrison #06  
        (mod_interp 3),
        undefined,
        @"forall x. (x = 0) \/ (x = 1)",
        false
    );
    (
        // idx 2
        // fol.p011
        (mod_interp 3),
        undefined,
        "(forall x. x = 0) ==> 1 = 0",
        true
    );
    (
        // idx 3
        // fol.p012
        (mod_interp 3),
        undefined,
        "forall x. x = 0 ==> 1 = 0",
        false
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "fol.p008")>]
[<TestCase(1, TestName = "fol.p009")>]
[<TestCase(2, TestName = "fol.p011")>]
[<TestCase(3, TestName = "fol.p012")>]
let ``holds tests (int)`` idx = 
    let (interpretation, _, _, _) = holdIntValues.[idx]
    let (_, valuation, _, _) = holdIntValues.[idx]
    let (_, _, fol_formula, _) = holdIntValues.[idx]
    let (_, _, _, result) = holdIntValues.[idx]
    holds interpretation valuation (parse fol_formula)
    |> should equal result

let private holdRangeValues : ((int -> int list * (string -> int list -> int) * (string -> int list -> bool)) * func<string,int> * string * int list * int list )[] = [|
    (
        // idx 0
        // fol.p010 
        (fun n -> (mod_interp n)),
        undefined,
        @"forall x. ~(x = 0) ==> exists y. x * y = 1",
        (1--45),
        [1; 2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43]
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "fol.p010")>]
let ``holds tests (int range)`` idx = 
    let (interpretation, _, _, _, _) = holdRangeValues.[idx]
    let (_, valuation, _, _, _) = holdRangeValues.[idx]
    let (_, _, fol_formula, _, _) = holdRangeValues.[idx]
    let (_, _, _, range, _) = holdRangeValues.[idx]
    let (_, _, _, _, result) = holdRangeValues.[idx]
    List.filter (fun n -> holds (interpretation n) valuation (parse fol_formula)) (range)
    |> should equal result

let private variantValues : (string * string list * string)[] = [| 
    (
        // idx 0
        // fol.p013
        "x",
        ["y"; "z"],
        "x"
    );    
    (
        // idx 1
        // fol.p014
        "x",
        ["x"; "y"],
        "x'"
    ); 
    (
        // idx 2
        // fol.p015
        "x",
        ["x"; "x'"],
        "x''"
    ); 
    |]
    
[<Test>]
[<TestCase(0, TestName = "fol.p013")>]
[<TestCase(1, TestName = "fol.p014")>]
[<TestCase(2, TestName = "fol.p015")>]
let ``variant tests`` idx = 
    let (x, _, _) = variantValues.[idx]
    let (_, vars, _) = variantValues.[idx]
    let (_, _, result) = variantValues.[idx]
    variant x vars
    |> should equal result

let private substValues : (func<string,term> * string * formula<fol> * string)[] = [| 
    (
        // idx 0
        // fol.p016
        ("y" |=> Var "x"),
        @"forall x. x = y",
        Forall ("x'", Atom (R ("=", [Var "x'"; Var "x"]))),
        @"<<forall x'. x' =x>>"
    );
    (
        // idx 1
        // fol.p017
        ("y" |=> Var "x"),
        @"forall x x'. x = y ==> x = x'",
        Forall
            ("x'",
             Forall
               ("x''",
                Imp
                  (Atom (R ("=",[Var "x'"; Var "x"])),
                   Atom (R ("=",[Var "x'"; Var "x''"]))))),
        @"<<forall x' x''. x' =x ==> x' =x''>>"
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "fol.p016")>]
[<TestCase(1, TestName = "fol.p017")>]
let ``subst tests`` idx = 
    let (subfn, _, _, _) = substValues.[idx]
    let (_, fm, _, _) = substValues.[idx]
    let (_, _, astResult, _) = substValues.[idx]
    let (_, _, _, stringResult) = substValues.[idx]
    let result = subst subfn (parse fm)
    result
    |> should equal astResult
    sprint_fol_formula result
    |> should equal stringResult