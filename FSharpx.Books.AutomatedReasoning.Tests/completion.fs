// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.completion

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.unif
open FSharpx.Books.AutomatedReasoning.meson
open FSharpx.Books.AutomatedReasoning.equal
open FSharpx.Books.AutomatedReasoning.rewrite
open FSharpx.Books.AutomatedReasoning.order
open FSharpx.Books.AutomatedReasoning.completion

open NUnit.Framework
open FsUnit

let private criticalPairValues =  
    [|
        ( // completion.p001  // idx 0
            (parse @"f(f(x)) = g(x)"), 
            [Atom
                (R ("=",
                    [Fn ("f", [Fn ("g", [Var "x0"])]);
                        Fn ("g", [Fn ("f", [Var "x0"])])]));
            Atom (R ("=", [Fn ("g", [Var "x1"]); Fn ("g", [Var "x1"])]))]
        );
    |]

// completion.p001
[<TestCase(0, TestName = "completion.p001")>]

let ``critical pairs`` idx =
    let (eq, _) = criticalPairValues.[idx]
    let (_, result) = criticalPairValues.[idx]
    critical_pairs eq eq
    |> should equal result
    
let eqs =
    [parse @"1 * x = x";
    parse @"i(x) * x = 1";
    parse @"(x * y) * z = x * y * z"; ]
let ord = lpo_ge (weight ["1"; "*"; "i"])

// Note: eqs' takes about 30 seconds to evaluate. 
// So that it will run only when needed
// and not at initilization for every test
// including those that don't need it, 
// it will be evaluated using lazy evaluation.
//
// In ohter words, running a single short test
// won't have to wait 30 seconds for eqs' to be
// evaluated during initilization.
let eqs' =
    lazy ( 
        complete ord (eqs, [], unions (allpairs critical_pairs eqs eqs))
    )   

let private rewriteValues =  
    [|
        ( // completion.p002  // idx 0
            (eqs'.Force()),
            (parset @"i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))"),
            Var "z"
        );
    |]

// completion.p002
// long running
[<TestCase(0, Category = "LongRunning", TestName = "completion.p002")>]

let ``rewrite test`` idx =
    let (eqs, _, _) = rewriteValues.[idx]
    let (_, tm, _) = rewriteValues.[idx]
    let (_, _, result) = rewriteValues.[idx]
    rewrite eqs tm
    |> should equal result
    
let private interreduceValues =  
    [|
        ( // completion.p003  // idx 0
            [],
            (eqs'.Force()),
            [Atom
                (R ("=",
                    [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
                    Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
            Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
            Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
            Atom
                (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
                    Var "x3"]));
            Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
                    Var "x2"]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
        );
    |]

// completion.p003
[<TestCase(0, TestName = "completion.p003")>]

let ``interreduce test`` idx =
    let (dun, _, _) = interreduceValues.[idx]
    let (_, eqs, _) = interreduceValues.[idx]
    let (_, _, result) = interreduceValues.[idx]
    interreduce dun eqs
    |> should equal result
    
let private equivalentValues =  
    [|
        ( // completion.p005  // idx 0
            (parse @" (forall x y z. x * y = x * z ==> y = z) <=> 
            (forall x z. exists w. forall y. z = x * y ==> w = y)"),
            [5; 4]
        );
    |]

// completion.p005
[<TestCase(0, TestName = "completion.p005")>]

// completion.p010 is completion.p005

let ``equivalent`` idx =
    let (eqs, _) = equivalentValues.[idx]
    let (_, result) = equivalentValues.[idx]
    (meson002 << equalitize) eqs
    |> should equal result

let private skolemizeEquivalentValues =  
    [|
        ( // completion.p006  // idx 0
            (parse @"forall x z. exists w. forall y. z = x * y ==> w = y"),
            Or (Not (Atom (R ("=", [Var "z"; Fn ("*", [Var "x"; Var "y"])]))),
                Atom (R ("=", [Fn ("f_w", [Var "x"; Var "z"]); Var "y"])))
        );
    |]

// completion.p006
[<TestCase(0, TestName = "completion.p006")>]

// completion.p011 is completion.p006

let ``skolemize equivalent`` idx =
    let (eqs, _) = skolemizeEquivalentValues.[idx]
    let (_, result) = skolemizeEquivalentValues.[idx]
    skolemize eqs
    |> should equal result
    
let private completeAndSimplifyCantOrientValues =  
    [|
        ( // K&B #7    // idx 0
            ["f"], 
            [(parse @"f(a,f(b,c,a),d) = c")]
        );
        ( // K&B #8    // idx 1
            ["*"], 
            [(parse @"(a * b) * (c * b * a) = b")]
        );
        ( // completion.p041    // idx 2
            ["*"; "one"; "two"], 
            [(parse @"(a*a * a) = one(a)");
            (parse @"(a * a*a) = two(a)");
            (parse @"(a*b * b*c) = b")]
        );
        ( // completion.p044    // idx 3
            ["1"; "/"], 
            [(parse @"((1 / (x / (y / (((x / x) / x) / z)))) / z) = y")]
        );
    |]

// completion.p013
// K&B #7
[<TestCase(0, TestName = "K&B #7")>]

// completion.p025
// K&B #8
[<TestCase(1, TestName = "K&B #8")>]

// completion.p040
[<TestCase(2, TestName = "completion.p040")>]

// completion.p023 is  completion.p013

// completion.p0??
[<TestCase(3, TestName = "completion.p0??")>]

[<ExpectedException("System.Collections.Generic.KeyNotFoundException")>]
let ``complete and simplify can't orient`` idx =
    let (wts, _) = completeAndSimplifyCantOrientValues.[idx]
    let (_, eqs) = completeAndSimplifyCantOrientValues.[idx]
    complete_and_simplify wts eqs
    |> should equal ()
    
// ------------------------------------------------------------------------- //
// Another random axiom (K&B example 8).                                     //
// ------------------------------------------------------------------------- //

// completion.p025 - fails

// ====================================================================================================

let private completeAndSimplifyValues =  
    [|
        ( // K&B #4    // old idx 0
            ["1"; "*"; "i"], 
            [parse @"i(a) * (a * b) = b"],
            [Atom
            (R ("=",
                [Fn ("*", [Var "x0"; Fn ("*", [Fn ("i", [Var "x0"]); Var "x3"])]);
                    Var "x3"]));
            Atom
            (R ("=",
                [Fn ("*", [Fn ("i", [Fn ("i", [Var "x0"])]); Var "x1"]);
                    Fn ("*", [Var "x0"; Var "x1"])]));
            Atom
            (R ("=",
                [Fn ("*", [Fn ("i", [Var "a"]); Fn ("*", [Var "a"; Var "b"])]);
                    Var "b"]))] 
        );
        ( // K&B #6    // old idx 1
            ["*"], 
            [parse @"(a * b) * (b * c) = b"],
            [Atom
                (R ("=",
                    [Fn
                    ("*",
                        [Fn ("*",[Var "x3"; Fn ("*",[Var "x0"; Var "x1"])]);
                        Var "x1"]); Fn ("*",[Var "x0"; Var "x1"])]));
            Atom
                (R ("=",
                    [Fn
                    ("*",
                        [Var "x1";
                        Fn ("*",[Fn ("*",[Var "x1"; Var "x2"]); Var "x5"])]);
                    Fn ("*",[Var "x1"; Var "x2"])]));
            Atom
                (R ("=",
                    [Fn
                    ("*",
                        [Fn ("*",[Var "a"; Var "b"]); Fn ("*",[Var "b"; Var "c"])]);
                    Var "b"]))]            
        );
        ( // K&B #12    // old idx 2
            ["1"; "*"; "i"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x"); 
            (parse @"x * i(x) = 1")],
            [Atom
                (R ("=",
                    [Fn ("i",[Fn ("*",[Var "x1"; Var "x2"])]);
                    Fn ("*",[Fn ("i",[Var "x2"]); Fn ("i",[Var "x1"])])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x0"]); Fn ("1",[])]);
                    Fn ("i",[Var "x0"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x3"])]);
                    Var "x3"]));
            Atom
                (R ("=",
                    [Fn ("i",[Fn ("i",[Var "x0"])]);
                    Fn ("*",[Var "x0"; Fn ("1",[])])]));
            Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x2"])]);
                    Var "x2"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Var "x"; Fn ("i",[Var "x"])]); Fn ("1",[])]))]
        );
        ( // K&B #10    // old idx 3
            ["1"; "*"; "\\"; "/"],
            [parse @"a * \(a,b) = b";
            parse @"/(a,b) * b = a";
            parse @"1 * a = a";
            parse @"a * 1 = a"; ],
            [Atom (R ("=",[Fn (@"\",[Fn ("1",[]); Var "x1"]); Var "x1"]));
            Atom (R ("=",[Fn ("/",[Var "x0"; Fn ("1",[])]); Var "x0"]));
            Atom
                (R ("=",[Fn ("*",[Var "a"; Fn (@"\",[Var "a"; Var "b"])]); Var "b"]));
            Atom
                (R ("=",[Fn ("*",[Fn ("/",[Var "a"; Var "b"]); Var "b"]); Var "a"]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "a"]); Var "a"]));
            Atom (R ("=",[Fn ("*",[Var "a"; Fn ("1",[])]); Var "a"]))]
        );
        ( // K&B #7    // old idx 4
            ["h"; "g"; "f"],
            [parse @"f(a,f(b,c,a),d) = c";
            parse @"f(a,b,c) = g(a,b)";
            parse @"g(a,b) = h(b)"; ],
            [Atom (R ("=",[Fn ("h",[Fn ("h",[Var "x2"])]); Var "x2"]));
            Atom
                (R ("=",[Fn ("f",[Var "a"; Var "b"; Var "c"]); Fn ("h",[Var "b"])]));
            Atom (R ("=",[Fn ("g",[Var "a"; Var "b"]); Fn ("h",[Var "b"])]))]
        );
        ( // completion.p012    // old idx 5
            ["1"; "*"; "f"; "g"],
            [parse @"f(a,a*b) = b";
            parse @"g(a*b,b) = a";
            parse @"1 * a = a";
            parse @"a * 1 = a"; ],
            [Atom (R ("=",[Fn ("g",[Var "x1"; Var "x1"]); Fn ("1",[])]));
            Atom (R ("=",[Fn ("g",[Var "x0"; Fn ("1",[])]); Var "x0"]));
            Atom (R ("=",[Fn ("f",[Fn ("1",[]); Var "x1"]); Var "x1"]));
            Atom (R ("=",[Fn ("f",[Var "x0"; Var "x0"]); Fn ("1",[])]));
            Atom
                (R ("=",[Fn ("f",[Var "a"; Fn ("*",[Var "a"; Var "b"])]); Var "b"]));
            Atom
                (R ("=",[Fn ("g",[Fn ("*",[Var "a"; Var "b"]); Var "b"]); Var "a"]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "a"]); Var "a"]));
            Atom (R ("=",[Fn ("*",[Var "a"; Fn ("1",[])]); Var "a"]))]
        );
        ( // K&B #1    // old idx 6
            ["1"; "*"; "i"],
            [parse @"1 * x = x";
            parse @"i(x) * x = 1";
            parse @"(x * y) * z = x * y * z"; ],
            [Atom
                (R ("=",
                    [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
                    Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
            Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
            Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
            Atom
                (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
                    Var "x3"]));
            Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
                    Var "x2"]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]))]
        );
        ( // completion.p016    // old idx 7
            ["1"; "*"; "i"],
            [parse @"(x * y) * z = x * y * z";
            parse @"1 * x = x";
            parse @"i(x) * x = 1"; ],
            [Atom
                (R ("=",
                    [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
                    Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
            Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
            Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
            Atom
                (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
                    Var "x3"]));
            Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
                    Var "x2"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]))]
        );
        (    // old idx 8
            ["1"; "*"; "i"],
            [parse @"a * (i(a) * b) = b"],
            [Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x3"])]);
                    Var "x3"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Fn ("i",[Var "x2"])]); Var "x1"]);
                    Fn ("*",[Var "x2"; Var "x1"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "a"; Fn ("*",[Fn ("i",[Var "a"]); Var "b"])]);
                    Var "b"]))]
        );
        ( // K&B #5    // old idx 9
            ["1"; "11"; "*"; "i"; "j"],
            [parse @"(x * y) * z = x * y * z";
            parse @"1 * x = x";
            parse @"11 * x = x";
            parse @"i(x) * x = 1";
            parse @"j(x) * x = 11"; ],
            [Atom
                (R ("=",
                    [Fn ("i",[Fn ("*",[Var "x4"; Var "x5"])]);
                    Fn ("*",[Fn ("i",[Var "x5"]); Fn ("i",[Var "x4"])])]));
            Atom (R ("=",[Fn ("j",[Var "x0"]); Fn ("i",[Var "x0"])]));
            Atom (R ("=",[Fn ("i",[Fn ("i",[Var "x1"])]); Var "x1"]));
            Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
            Atom (R ("=",[Fn ("11",[]); Fn ("1",[])]));
            Atom
                (R ("=",[Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x3"])]);
                    Var "x3"]));
            Atom (R ("=",[Fn ("*",[Var "x1"; Fn ("1",[])]); Var "x1"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
                    Var "x2"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]))]
        );
        ( // K&B #9    // old idx 10
            ["*"; "f"; "g"],
            [parse @"f(a,a*b) = b";
            parse @"g(a*b,b) = a"; ],
            [Atom
                (R ("=",[Fn ("f",[Var "a"; Fn ("*",[Var "a"; Var "b"])]); Var "b"]));
            Atom
                (R ("=",[Fn ("g",[Fn ("*",[Var "a"; Var "b"]); Var "b"]); Var "a"]))]
        );
        ( // completion.p032    // old idx 11
            ["1"; "*"; "\\"; "/"; "f"; "g"],
            [parse @"a * \(a,b) = b";
            parse @"/(a,b) * b = a";
            parse @"1 * a = a";
            parse @"a * 1 = a";
            parse @"f(a,a*b) = b";
            parse @"g(a*b,b) = a"; ],
            [Atom
                (R ("=",
                    [Fn ("/",[Fn ("*",[Var "x2"; Var "x1"]); Var "x1"]); Var "x2"]));
            Atom
                (R ("=",
                    [Fn (@"\",[Var "x0"; Fn ("*",[Var "x0"; Var "x3"])]); Var "x3"]));
            Atom
                (R ("=",
                    [Fn ("/",[Var "x1"; Fn (@"\",[Var "x2"; Var "x1"])]); Var "x2"]));
            Atom (R ("=",[Fn ("/",[Var "x1"; Var "x1"]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("g",[Var "x0"; Var "x3"]); Fn ("/",[Var "x0"; Var "x3"])]));
            Atom
                (R ("=",
                    [Fn (@"\",[Fn ("/",[Var "x0"; Var "x3"]); Var "x0"]); Var "x3"]));
            Atom (R ("=",[Fn (@"\",[Var "x1"; Var "x1"]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("f",[Var "x0"; Var "x3"]); Fn (@"\",[Var "x0"; Var "x3"])]));
            Atom (R ("=",[Fn (@"\",[Fn ("1",[]); Var "x1"]); Var "x1"]));
            Atom (R ("=",[Fn ("/",[Var "x0"; Fn ("1",[])]); Var "x0"]));
            Atom
                (R ("=",[Fn ("*",[Var "a"; Fn (@"\",[Var "a"; Var "b"])]); Var "b"]));
            Atom
                (R ("=",[Fn ("*",[Fn ("/",[Var "a"; Var "b"]); Var "b"]); Var "a"]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "a"]); Var "a"]));
            Atom (R ("=",[Fn ("*",[Var "a"; Fn ("1",[])]); Var "a"]))]
        );
        ( // K&B #13    // old idx 12
            ["1"; "*"; "i"],
            [parse @"(x * y) * z = x * y * z";
            parse @"x * 1 = x";
            parse @"i(x) * x = 1"; ],
            [Atom
                (R ("=",
                    [Fn ("i",[Fn ("*",[Var "x2"; Var "x3"])]);
                    Fn ("*",[Fn ("i",[Var "x3"]); Fn ("i",[Var "x2"])])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("1",[]); Fn ("i",[Var "x3"])]);
                    Fn ("i",[Var "x3"])]));
            Atom
                (R ("=",
                    [Fn
                    ("*",[Fn ("1",[]); Fn ("*",[Fn ("i",[Var "x0"]); Var "x1"])]);
                    Fn ("*",[Fn ("i",[Var "x0"]); Var "x1"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x1"; Fn ("*",[Var "x0"; Fn ("i",[Var "x0"])])]);
                    Var "x1"]));
            Atom
                (R ("=",
                    [Fn
                    ("*",
                        [Var "x2";
                        Fn
                        ("*",
                            [Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x1"])])]);
                    Fn ("*",[Var "x2"; Var "x1"])]));
            Atom
                (R ("=",
                    [Fn ("i",[Fn ("i",[Var "x0"])]);
                    Fn ("*",[Fn ("1",[]); Var "x0"])]));
            Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
                    Fn ("*",[Fn ("1",[]); Var "x2"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x0"; Fn ("*",[Fn ("1",[]); Var "x2"])]);
                    Fn ("*",[Var "x0"; Var "x2"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("*",[Var "x"; Fn ("1",[])]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Fn ("i",[Var "x"]); Var "x"]); Fn ("1",[])]))]
        );
        ( // K&B #14    // old idx 13
            ["1"; "11"; "*"; "i"; "j"],
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x"); 
            (parse @"11 * x = x"); 
            (parse @"x * i(x) = 1"); 
            (parse @"x * j(x) = 11")],
            [Atom
                (R ("=",
                    [Fn ("i",[Fn ("*",[Var "x1"; Var "x2"])]);
                    Fn ("*",[Fn ("i",[Var "x2"]); Fn ("i",[Var "x1"])])]));
            Atom
                (R ("=",
                    [Fn ("j",[Var "x0"]);
                    Fn ("*",[Fn ("i",[Var "x0"]); Fn ("11",[])])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x0"]); Fn ("1",[])]);
                    Fn ("i",[Var "x0"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("i",[Var "x1"]); Fn ("*",[Var "x1"; Var "x3"])]);
                    Var "x3"]));
            Atom
                (R ("=",
                    [Fn ("i",[Fn ("i",[Var "x0"])]);
                    Fn ("*",[Var "x0"; Fn ("1",[])])]));
            Atom (R ("=",[Fn ("i",[Fn ("11",[])]); Fn ("1",[])]));
            Atom (R ("=",[Fn ("i",[Fn ("1",[])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x0"; Fn ("*",[Fn ("i",[Var "x0"]); Var "x2"])]);
                    Var "x2"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Fn ("11",[]); Var "x"]); Var "x"]));
            Atom (R ("=",[Fn ("*",[Var "x"; Fn ("i",[Var "x"])]); Fn ("1",[])]))]
        );
        ( // K&B #15    // old idx 14
            ["1"; "*"; "star"; "prime"],
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x");  
            (parse @"prime(a) * a = star(a)"); 
            (parse @"star(a) * b = b")],
            [Atom
                (R ("=",
                    [Fn
                    ("*",
                        [Fn ("prime",[Fn ("*",[Var "x4"; Var "x3"])]); Var "x0"]);
                    Fn
                    ("*",
                        [Fn ("prime",[Var "x3"]);
                        Fn ("*",[Fn ("prime",[Var "x4"]); Var "x0"])])]));
            Atom
                (R ("=",
                    [Fn ("star",[Fn ("star",[Var "x1"])]); Fn ("star",[Var "x1"])]));
            Atom
                (R ("=",
                    [Fn ("star",[Fn ("*",[Var "x2"; Var "x3"])]);
                    Fn ("star",[Var "x3"])]));
            Atom (R ("=",[Fn ("star",[Fn ("1",[])]); Fn ("1",[])]));
            Atom
                (R ("=",
                    [Fn ("star",[Fn ("prime",[Var "x0"])]);
                    Fn ("*",[Var "x0"; Fn ("prime",[Var "x0"])])]));
            Atom
                (R ("=",
                    [Fn
                    ("*",
                        [Var "x0"; Fn ("*",[Fn ("prime",[Var "x0"]); Var "x3"])]);
                    Var "x3"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("prime",[Fn ("star",[Var "x2"])]); Var "x1"]);
                    Var "x1"]));
            Atom
                (R ("=",[Fn ("*",[Var "x1"; Fn ("star",[Var "x1"])]); Var "x1"]));
            Atom
                (R ("=",[Fn ("*",[Fn ("prime",[Fn ("1",[])]); Var "x1"]); Var "x1"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("prime",[Fn ("prime",[Var "x0"])]); Var "x1"]);
                    Fn ("*",[Var "x0"; Var "x1"])]));
            Atom
                (R ("=",
                    [Fn
                    ("*",
                        [Fn ("prime",[Var "x1"]); Fn ("*",[Var "x1"; Var "x2"])]);
                    Var "x2"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("*",[Var "x"; Fn ("*",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("*",[Fn ("1",[]); Var "x"]); Var "x"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("prime",[Var "a"]); Var "a"]);
                    Fn ("star",[Var "a"])]));
            Atom (R ("=",[Fn ("*",[Fn ("star",[Var "a"]); Var "b"]); Var "b"]))]
        );
        ( // The commutativity example (of course it fails...).  // old idx 15
            ["1"; "*"; "i"], 
            [parse @"(x * y) * z = x * (y * z)";
            parse @"1 * x = x";
            parse @"x * 1 = x";
            parse @"x * x = 1"],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p017  // old idx 16
            ["1"; "i"; "*"], 
            [(parse @"1 * x = x"); 
            (parse @"i(x) * x = 1"); 
            (parse @"(x * y) * z = x * y * z")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p018  // old idx 17
            ["1"; "*"; "i"], 
            [parse @"(x * y) * z = x * y * z";
            parse @"x * 1 = x";
            parse @"x * i(x) = 1"; ],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p028  // old idx 18
            ["1"; "*"; "f"; "g"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"f(a,a*b) = b"); 
            (parse @"g(a*b,b) = a"); 
            (parse @"1 * a = a"); 
            (parse @"a * 1 = a")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p029  // old idx 19
            ["*"; "f"; "g"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"f(a,a*b) = b"); 
            (parse @"g(a*b,b) = a"); 
            (parse @"1 * a = a"); 
            (parse @"a * 1 = a")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p030  // old idx 20
            ["f"; "g"; "*"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"f(a,a*b) = b"); 
            (parse @"g(a*b,b) = a"); 
            (parse @"1 * a = a"); 
            (parse @"a * 1 = a")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // K&B 11  // old idx 21
            ["1"; "g"; "f"; "*"; "i"], 
            [(parse @"(x * y) * z = x * y * z");
            (parse @"1 * 1 = 1");
            (parse @"a * i(a) = 1");
            (parse @"f(1,a,b) = a");
            (parse @"f(a*b,a,b) = g(a*b,b)")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // K&B 12  // old idx 22
            ["1"; "*"; "i"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x"); 
            (parse @"x * i(x) = 1")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p038  // old idx 23
            ["1"; "hash"; "star"; "*"; "dollar"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x");  
            (parse @"hash(a) * dollar(a) * a = star(a)"); 
            (parse @"star(a) * b = b"); 
            (parse @"a * hash(a) = 1"); 
            (parse @"a * 1 = hash(hash(a))"); 
            (parse @"hash(hash(hash(a))) = hash(a)")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p039  // old idx 24
            ["1"; "star"; "*"; "hash"; "dollar"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x"); 
            (parse @"hash(a) * dollar(a) * a = star(a)"); 
            (parse @"star(a) * b = b"); 
            (parse @"a * hash(a) = 1"); 
            (parse @"hash(hash(a)) = a * 1"); 
            (parse @"hash(hash(hash(a))) = hash(a)")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p040 // K&B #16 // old idx 25
            ["one"; "two"; "*"], 
            [parse @"(a * a) * a = one(a)";
            parse @"a * (a * a) = two(a)";
            parse @"(a * b) * (b * c) = b";
            parse @"two(a) * b = a * b"; ],
            [Atom
                (R ("=",
                    [Fn ("*",[Fn ("*",[Var "x0"; Var "x4"]); Var "x2"]);
                    Fn ("*",[Fn ("one",[Var "x4"]); Var "x2"])]));
            Atom
                (R ("=",
                    [Fn ("one",[Fn ("*",[Var "x3"; Var "x2"])]);
                    Fn ("two",[Var "x3"])]));
            Atom
                (R ("=",
                    [Fn ("two",[Fn ("*",[Var "x3"; Var "x2"])]);
                    Fn ("one",[Var "x2"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x1"; Fn ("one",[Var "x0"])]);
                    Fn ("*",[Var "x1"; Var "x0"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x3"; Fn ("*",[Var "x0"; Var "x5"])]);
                    Fn ("*",[Var "x3"; Fn ("two",[Var "x0"])])]));
            Atom
                (R ("=",[Fn ("one",[Fn ("one",[Var "x1"])]); Fn ("one",[Var "x1"])]));
            Atom
                (R ("=",[Fn ("two",[Fn ("one",[Var "x3"])]); Fn ("one",[Var "x3"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("one",[Var "x0"]); Var "x0"]);
                    Fn ("one",[Var "x0"])]));
            Atom
                (R ("=",[Fn ("one",[Fn ("two",[Var "x2"])]); Fn ("two",[Var "x2"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Var "x1"; Fn ("two",[Var "x1"])]);
                    Fn ("two",[Var "x1"])]));
            Atom
                (R ("=",[Fn ("two",[Fn ("two",[Var "x1"])]); Fn ("two",[Var "x1"])]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("one",[Var "x1"]); Fn ("two",[Var "x1"])]);
                    Var "x1"]));
            Atom
                (R ("=",
                    [Fn ("*",[Fn ("two",[Var "a"]); Var "b"]);
                    Fn ("*",[Var "a"; Var "b"])]))]
        );
        ( // completion.p042 // old idx 26
            ["1"; "f"], 
            [parse @"f(f(f(f(f(1))))) = 1";
            parse @"f(f(f(1))) = 1"; ],
            [Atom (R ("=",[Fn ("f",[Fn ("1",[])]); Fn ("1",[])]))]
        );
        ( // completion.p043 // old idx 27
            ["1"; "*"; "i"], 
            [(parse @"x * i(y * (((z * i(z)) * i(u * y)) * x)) = u")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p045 // old idx 28
            ["*"; "i"], 
            [(parse @"i(x * i(x)) * (i(i((y * z) * u) * y) * i(u)) = z")],
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p046 // Baader & Nipkow #1 // old idx 29
            ["g"; "f"], 
            [parse @"f(f(x)) = g(x)"],
            [Atom
                (R ("=",
                    [Fn ("f",[Fn ("g",[Var "x0"])]); Fn ("g",[Fn ("f",[Var "x0"])])]));
            Atom (R ("=",[Fn ("f",[Fn ("f",[Var "x"])]); Fn ("g",[Var "x"])]))]
        );
        ( // completion.p049 // Baader & Nipkow #4 // old idx 30
            ["f"; "g"], 
            [parse @"f(f(x)) = f(x)";
            parse @"g(g(x)) = f(x)";
            parse @"f(g(x)) = g(x)";
            parse @"g(f(x)) = f(x)"; ],
            [Atom (R ("=",[Fn ("g",[Var "x0"]); Fn ("f",[Var "x0"])]));
            Atom (R ("=",[Fn ("f",[Fn ("f",[Var "x"])]); Fn ("f",[Var "x"])]))]
        );
        ( // completion.p050 // Baader & Nipkow #5 // old idx 31
            ["f"; "g"], 
            [parse @"f(g(f(x))) = g(x)"],
            [Atom
                (R ("=",
                    [Fn ("g",[Fn ("g",[Fn ("f",[Var "x0"])])]);
                    Fn ("f",[Fn ("g",[Fn ("g",[Var "x0"])])])]));
            Atom
                (R ("=",
                    [Fn ("f",[Fn ("g",[Fn ("f",[Var "x"])])]); Fn ("g",[Var "x"])]))]
        );
        ( // completion.p051 // old idx 32
            ["0"; "nil"; "SUC"; "::"; "+"; "length"; "append"; "rev"], 
            [parse @"0 + y = y";
            parse @"SUC(x) + y = SUC(x + y)";
            parse @"append(nil,l) = l";
            parse @"append(h::t,l) = h::append(t,l)";
            parse @"length(nil) = 0";
            parse @"length(h::t) = SUC(length(t))";
            parse @"rev(nil) = nil";
            parse @"rev(h::t) = append(rev(t),h::nil)"; ],
            [Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
    |]

// completion.p007
// commutativity example
[<TestCase(15, Category = "LongRunning", TestName = "commutativity example")>]

// completion.p015
// K&B #1
[<TestCase(6, TestName = "K&B #1")>]

// completion.p004
// K&B #4
[<TestCase(0, TestName = "K&B #4")>]

// completion.p019 is completion.p005

// completion.p021
// K&B #5
[<TestCase(9, TestName = "K&B #5")>]

// completion.p008
// K&B #6
[<TestCase(1, TestName = "K&B #6")>]

// completion.p022 is completion.p008

// completion.p006
// K&B #7
[<TestCase(4, TestName = "K&B #7")>]

// completion.p014 is completion.p006
// completion.p024 is completion.p006 

// completion.p026
// K&B #9
[<TestCase(10, TestName = "K&B #9")>]

// completion.p031
// K&B #10
[<TestCase(3, TestName = "K&B #10")>]

// completion.p033
// K&B 11
[<TestCase(21, Category = "LongRunning", TestName = "K&B 11")>]

// completion.p034
// K&B 12
[<TestCase(22, Category = "LongRunning", TestName = "K&B 12")>]

// completion.p009
// K&B #12
[<TestCase(2, Category = "LongRunning", TestName = "K&B #12")>]

// completion.p035
// K&B #13
[<TestCase(12, Category = "LongRunning", TestName = "K&B #13")>]

// completion.p036
// K&B #14
[<TestCase(13, Category = "LongRunning", TestName = "K&B #14")>]

// completion.p037
// K&B #15
[<TestCase(14, TestName = "K&B #15")>]

// completion.p040
// K&B #16
[<TestCase(25, TestName = "K&B #16")>]

// completion.p012
[<TestCase(5, TestName = "completion p012")>]

// completion.p027 is completion.p012

// completion.p016
[<TestCase(7, TestName = "completion p016")>]

// completion.p017
[<TestCase(16, Category = "LongRunning", TestName = "completion.p017")>]

// completion.p018
[<TestCase(17, Category = "LongRunning", TestName = "completion.p018")>]

// completion.p020
[<TestCase(8, TestName = "completion p020")>]

// completion.p028
[<TestCase(18, Category = "LongRunning", TestName = "completion.p028")>]

// completion.p029
[<TestCase(19, Category = "LongRunning", TestName = "completion.p029")>]

// completion.p030
[<TestCase(20, Category = "LongRunning", TestName = "completion.p030")>]

// completion.p032
[<TestCase(11, TestName = "completion p032")>]

// completion.p038
[<TestCase(23, Category = "LongRunning", TestName = "completion.p038")>]

// completion.p039
[<TestCase(24, Category = "LongRunning", TestName = "completion.p039")>]

// completion.p042
[<TestCase(26, TestName = "completion.p043")>]

// completion.p043
[<TestCase(27, Category = "LongRunning", TestName = "completion.p044")>]

// completion.p045
[<TestCase(28, Category = "LongRunning", TestName = "completion.p045")>]

// completion.p046
// Baader & Nipkow #1
[<TestCase(29, TestName = "Baader & Nipkow #1")>]

// completion.p049
// Baader & Nipkow #4
[<TestCase(30, TestName = "Baader & Nipkow #4")>]

// completion.p050
// Baader & Nipkow #5
[<TestCase(31, TestName = "Baader & Nipkow #5")>]

// completion.p051
[<TestCase(32, TestName = "completion.p052")>]

let ``complete and simplify`` idx =
    let (wts, _, _) = completeAndSimplifyValues.[idx]
    let (_, eqs, _) = completeAndSimplifyValues.[idx]
    let (_, _, result) = completeAndSimplifyValues.[idx]
    complete_and_simplify wts eqs
    |> should equal result


// completion.p047
// Baader & Nipkow #2
//[<Test>]
//let ``funpow`` idx =
//    let eqs036 =  [parse @"f(f(x)) = g(x)"]
//    let (eqs1,def1,crits1) = funpow 122 (complete1 ord) (eqs036,def,crits)
//    ()
//    |> should equal  (
//        formula<fol>.False,
//        formula<fol>.False,
//        formula<fol>.False
//    )

let private iproveValues  =  
    [|
        ( // completion.p053  // idx 0
            [],
            (parse @"x + 0 = x"),
            [Atom (R ("=",[Fn ("+",[Var "x"; Fn ("0",[])]); Var "x"]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p054  // idx 1
            [],
            (parse @"x + SUC(y) = SUC(x + y)"),
            [Atom
                (R ("=",
                    [Fn ("+",[Var "x"; Fn ("SUC",[Var "y"])]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p055  // idx 2
            [],
            (parse @"(x + y) + z = x + y + z"),
            [Atom
                (R ("=",
                    [Fn ("+",[Fn ("+",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("+",[Var "x"; Fn ("+",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p056  // idx 3
            [],
            (parse @"length(append(x,y)) = length(x) + length(y)"),
            [Atom
                (R ("=",
                    [Fn ("length",[Fn ("append",[Var "x"; Var "y"])]);
                    Fn ("+",[Fn ("length",[Var "x"]); Fn ("length",[Var "y"])])]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p057  // idx 4
            [],
            (parse @"append(append(x,y),z) = append(x,append(y,z))"),
            [Atom
                (R ("=",
                    [Fn ("append",[Fn ("append",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("append",[Var "x"; Fn ("append",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p058  // idx 5
            [],
            (parse @"append(x,nil) = x"),
            [Atom (R ("=",[Fn ("append",[Var "x"; Fn ("nil",[])]); Var "x"]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p059  // idx 6
            [parse @"append(append(x,y),z) = append(x,append(y,z))";
            parse @"append(x,nil) = x";],
            (parse @"rev(append(x,y)) = append(rev(y),rev(x))"),
            [Atom
                (R ("=",
                    [Fn ("rev",[Fn ("append",[Var "x"; Var "y"])]);
                    Fn ("append",[Fn ("rev",[Var "y"]); Fn ("rev",[Var "x"])])]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("append",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("append",[Var "x"; Fn ("append",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("append",[Var "x"; Fn ("nil",[])]); Var "x"]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));        
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p060  // idx 7
            [parse @"rev(append(x,y)) = append(rev(y),rev(x))";
            parse @"append(x,nil) = x";
            parse @"append(append(x,y),z) = append(x,append(y,z))"; ],
            (parse @"rev(rev(x)) = x"),
            [Atom (R ("=",[Fn ("rev",[Fn ("rev",[Var "x"])]); Var "x"]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("append",[Var "x"; Var "y"])]);
                    Fn ("append",[Fn ("rev",[Var "y"]); Fn ("rev",[Var "x"])])]));
            Atom (R ("=",[Fn ("append",[Var "x"; Fn ("nil",[])]); Var "x"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("append",[Var "x"; Var "y"]); Var "z"]);
                    Fn ("append",[Var "x"; Fn ("append",[Var "y"; Var "z"])])]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p061  // idx 8
            [],
            (parse @"rev(rev(x)) = x"),
            [Atom
                (R ("=",
                    [Fn
                    ("rev",
                        [Fn
                        ("append",
                            [Var "x2"; Fn ("::",[Var "x0"; Fn ("nil",[])])])]);
                    Fn ("::",[Var "x0"; Fn ("rev",[Var "x2"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("rev",[Var "x"])]); Var "x"]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom
                (R ("=",
                    [Fn ("+",[Fn ("SUC",[Var "x"]); Var "y"]);
                    Fn ("SUC",[Fn ("+",[Var "x"; Var "y"])])]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("length",[Fn ("nil",[])]); Fn ("0",[])]));
            Atom
                (R ("=",
                    [Fn ("length",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn ("SUC",[Fn ("length",[Var "t"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]
        );
        ( // completion.p062  // idx 9
            [(parse @"rev(append(x,y)) = append(rev(y),rev(x))")],
            (parse @"rev(rev(x)) = x"),
            [formula<fol>.False]        // The result was unknown when test created. False used as place holder.
        );
        ( // completion.p063  // idx 10
            [],
            (parse @"length(append(x,y)) = length(x)"),
            [Atom (R ("=",[Fn ("SUC",[Var "x1"]); Var "x1"]));
            Atom (R ("=",[Fn ("length",[Var "x1"]); Fn ("0",[])]));
            Atom (R ("=",[Fn ("+",[Fn ("0",[]); Var "y"]); Var "y"]));
            Atom (R ("=",[Fn ("append",[Fn ("nil",[]); Var "l"]); Var "l"]));
            Atom
                (R ("=",
                    [Fn ("append",[Fn ("::",[Var "h"; Var "t"]); Var "l"]);
                    Fn ("::",[Var "h"; Fn ("append",[Var "t"; Var "l"])])]));
            Atom (R ("=",[Fn ("rev",[Fn ("nil",[])]); Fn ("nil",[])]));
            Atom
                (R ("=",
                    [Fn ("rev",[Fn ("::",[Var "h"; Var "t"])]);
                    Fn
                    ("append",
                        [Fn ("rev",[Var "t"]); Fn ("::",[Var "h"; Fn ("nil",[])])])]))]    
        );
    |]

let eqs039 =
        [parse @"0 + y = y";
        parse @"SUC(x) + y = SUC(x + y)";
        parse @"append(nil,l) = l";
        parse @"append(h::t,l) = h::append(t,l)";
        parse @"length(nil) = 0";
        parse @"length(h::t) = SUC(length(t))";
        parse @"rev(nil) = nil";
        parse @"rev(h::t) = append(rev(t),h::nil)"; ]

// completion.p053
[<TestCase(0, TestName = "completion.p053")>]

// completion.p054
[<TestCase(1, TestName = "completion.p054")>]

// completion.p055
[<TestCase(2, TestName = "completion.p055")>]

// completion.p056
[<TestCase(3, TestName = "completion.p056")>]

// completion.p057
[<TestCase(4, TestName = "completion.p057")>]

// completion.p058
[<TestCase(5, TestName = "completion.p058")>]

// completion.p059
[<TestCase(6, TestName = "completion.p059")>]

// completion.p060
[<TestCase(7, TestName = "completion.p060")>]

// completion.p061
[<TestCase(8, TestName = "completion.p061")>]

// completion.p062
[<TestCase(9, Category = "LongRunning", TestName = "completion.p062")>]

// completion.p063
[<TestCase(10, TestName = "completion.p064")>]

let ``iprove 1`` idx =
    let iprove eqs' tm =
        complete_and_simplify
            ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
            (tm :: eqs' @ eqs039)
    let (eqs', _, _) = iproveValues.[idx]
    let (_, tm, _) = iproveValues.[idx]
    let (_, _, result) = iproveValues.[idx]
    iprove eqs' tm
    |> should equal result
