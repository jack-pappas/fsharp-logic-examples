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

let private criticalPairValues : (formula<fol> * formula<fol> list)[] =  [|
    ( 
        // idx 0
        // completion.p001  
        (parse @"f(f(x)) = g(x)"), 
        [Atom
           (R ("=",
               [Fn ("f",[Fn ("g",[Var "x0"])]); Fn ("g",[Fn ("f",[Var "x0"])])]));
         Atom (R ("=",[Fn ("g",[Var "x1"]); Fn ("g",[Var "x1"])]))] 
    );
    |]

// completion.p001
[<Test>]
[<TestCase(0, TestName = "completion.p001")>]
let ``critical pairs tests`` idx =
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
        complete ord (eqs, [], unions (allpairs critical_pairs eqs eqs)))

let private rewriteValues : (formula<fol> list * term * term)[] = [|
    ( 
        // idx 0
        // completion.p002  
        (eqs'.Force()),
        (parset @"i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))"),
        Var "z"
    );
    |]

[<Test>]
[<TestCase(0, TestName = "completion.p002")>]
let ``rewrite tests`` idx =
    let (eqs, _, _) = rewriteValues.[idx]
    let (_, tm, _) = rewriteValues.[idx]
    let (_, _, result) = rewriteValues.[idx]
    rewrite eqs tm
    |> should equal result
    
let private interreduceValues : (formula<fol> list * formula<fol> list * formula<fol> list)[] = [|
    ( 
        // idx 0
        // completion.p003  
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

[<Test>]
[<TestCase(0, TestName = "completion.p003")>]
let ``interreduce tests`` idx =
    let (dun, _, _) = interreduceValues.[idx]
    let (_, eqs, _) = interreduceValues.[idx]
    let (_, _, result) = interreduceValues.[idx]
    interreduce dun eqs
    |> should equal result
    
let private equivalentValues = [|
    ( 
        // idx 0
        // completion.p005  
        (parse @" (forall x y z. x * y = x * z ==> y = z) <=> 
        (forall x z. exists w. forall y. z = x * y ==> w = y)"),
        [5; 4]
    );
    |]

[<Test>]
[<TestCase(0, TestName = "completion.p005")>]   // completion.p010 is completion.p005
let ``equivalent tests`` idx =
    let (eqs, _) = equivalentValues.[idx]
    let (_, result) = equivalentValues.[idx]
    (meson002 << equalitize) eqs
    |> should equal result

let private skolemizeEquivalentValues = [|
    ( 
        // idx 0
        // completion.p006  
        (parse @"forall x z. exists w. forall y. z = x * y ==> w = y"),
        Or (Not (Atom (R ("=", [Var "z"; Fn ("*", [Var "x"; Var "y"])]))),
          Atom (R ("=", [Fn ("f_w", [Var "x"; Var "z"]); Var "y"])))
    );
    |]

[<Test>]
[<TestCase(0, TestName = "completion.p006")>] // completion.p011 is completion.p006
let ``skolemize tests`` idx =
    let (eqs, _) = skolemizeEquivalentValues.[idx]
    let (_, result) = skolemizeEquivalentValues.[idx]
    skolemize eqs
    |> should equal result    
    
let private completeAndSimplifyValues : (string list * formula<fol> list * formula<fol> list)[] =  
    [|
        ( 
            // idx 0
            // completion.p004
            // completion.p019
            // K&B #4    
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
        ( 
            // idx 1
            // completion.p008
            // completion.p022
            // K&B #6    
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
        ( 
            // idx 2
            // completion.p009
            // completion.p034
            // K&B #12    
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
        ( 
            // idx 3
            // completion.p031
            // K&B #10    
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
        ( 
            //idx 4
            // completion.p014
            // completion.p024
            // K&B #7   
            ["h"; "g"; "f"],
            [parse @"f(a,f(b,c,a),d) = c";
            parse @"f(a,b,c) = g(a,b)";
            parse @"g(a,b) = h(b)"; ],
            [Atom (R ("=",[Fn ("h",[Fn ("h",[Var "x2"])]); Var "x2"]));
            Atom
                (R ("=",[Fn ("f",[Var "a"; Var "b"; Var "c"]); Fn ("h",[Var "b"])]));
            Atom (R ("=",[Fn ("g",[Var "a"; Var "b"]); Fn ("h",[Var "b"])]))]
        );
        ( 
            //idx 5
            // completion.p012    
            // completion.p027
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
        ( 
            //idx 6
            // K&B #1    
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
        ( 
            //idx 7
            // completion.p016    
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
        (   //idx 8
            // completion.p020
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
        (    
            // idx 9
            // completion.p021
            // K&B #5   
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
        ( 
            // idx 10
            // completion.p026
            // K&B #9    
            ["*"; "f"; "g"],
            [parse @"f(a,a*b) = b";
            parse @"g(a*b,b) = a"; ],
            [Atom
                (R ("=",[Fn ("f",[Var "a"; Fn ("*",[Var "a"; Var "b"])]); Var "b"]));
            Atom
                (R ("=",[Fn ("g",[Fn ("*",[Var "a"; Var "b"]); Var "b"]); Var "a"]))]
        );
        ( 
            // idx 11
            // completion.p032    
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
        ( 
            // idx 12
            // completion.p035
            // K&B #13    
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
        (  
            // idx 13
            // completion.p036
            // K&B #14   
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
        (   
            // idx 14
            // completion.p037
            // K&B #15    
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
        ( 
            // idx 15
            // completion.p007
            // commutativity example
            ["1"; "*"; "i"], 
            [parse @"(x * y) * z = x * (y * z)";
            parse @"1 * x = x";
            parse @"x * 1 = x";
            parse @"x * x = 1"],
            []  // Dummy value used as place holder
        );
        (   
            // idx 16
            // completion.p017  
            ["1"; "i"; "*"], 
            [(parse @"1 * x = x"); 
            (parse @"i(x) * x = 1"); 
            (parse @"(x * y) * z = x * y * z")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 17
            // completion.p018  
            // K&B #3
            ["1"; "*"; "i"], 
            [parse @"(x * y) * z = x * y * z";
            parse @"x * 1 = x";
            parse @"x * i(x) = 1"; ],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 18
            // completion.p028  
            ["1"; "*"; "f"; "g"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"f(a,a*b) = b"); 
            (parse @"g(a*b,b) = a"); 
            (parse @"1 * a = a"); 
            (parse @"a * 1 = a")],
            []  // Dummy value used as place holder
        );
        (  
            // idx 19
            // completion.p029 
            ["*"; "f"; "g"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"f(a,a*b) = b"); 
            (parse @"g(a*b,b) = a"); 
            (parse @"1 * a = a"); 
            (parse @"a * 1 = a")],
            []  // Dummy value used as place holder
        );
        (   
            // idx 20
            // completion.p030  
            ["f"; "g"; "*"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"f(a,a*b) = b"); 
            (parse @"g(a*b,b) = a")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 21
            // completion.p033
            // K&B 11  
            ["1"; "g"; "f"; "*"; "i"], 
            [(parse @"(x * y) * z = x * y * z");
            (parse @"1 * 1 = 1");
            (parse @"a * i(a) = 1");
            (parse @"f(1,a,b) = a");
            (parse @"f(a*b,a,b) = g(a*b,b)")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 22
            // K&B 12  
            ["1"; "*"; "i"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x"); 
            (parse @"x * i(x) = 1")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 23
            // completion.p038  
            ["1"; "hash"; "star"; "*"; "dollar"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x");  
            (parse @"hash(a) * dollar(a) * a = star(a)"); 
            (parse @"star(a) * b = b"); 
            (parse @"a * hash(a) = 1"); 
            (parse @"a * 1 = hash(hash(a))"); 
            (parse @"hash(hash(hash(a))) = hash(a)")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 24
            // completion.p039  
            ["1"; "star"; "*"; "hash"; "dollar"], 
            [(parse @"(x * y) * z = x * y * z"); 
            (parse @"1 * x = x"); 
            (parse @"hash(a) * dollar(a) * a = star(a)"); 
            (parse @"star(a) * b = b"); 
            (parse @"a * hash(a) = 1"); 
            (parse @"hash(hash(a)) = a * 1"); 
            (parse @"hash(hash(hash(a))) = hash(a)")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 25
            // completion.p040 
            // K&B #16 
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
        (   
            // idx 26
            // completion.p042 
            ["1"; "f"], 
            [parse @"f(f(f(f(f(1))))) = 1";
            parse @"f(f(f(1))) = 1"; ],
            [Atom (R ("=",[Fn ("f",[Fn ("1",[])]); Fn ("1",[])]))]
        );
        (   
            // idx 27
            // completion.p043 
            ["1"; "*"; "i"], 
            [(parse @"x * i(y * (((z * i(z)) * i(u * y)) * x)) = u")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 28
            // completion.p045 
            ["*"; "i"], 
            [(parse @"i(x * i(x)) * (i(i((y * z) * u) * y) * i(u)) = z")],
            []  // Dummy value used as place holder
        );
        ( 
            // idx 29
            // completion.p046 
            // Baader & Nipkow #1 
            ["g"; "f"], 
            [parse @"f(f(x)) = g(x)"],
            [Atom
                (R ("=",
                    [Fn ("f",[Fn ("g",[Var "x0"])]); Fn ("g",[Fn ("f",[Var "x0"])])]));
            Atom (R ("=",[Fn ("f",[Fn ("f",[Var "x"])]); Fn ("g",[Var "x"])]))]
        );
        ( 
            // idx 30
            // completion.p049 
            // Baader & Nipkow #4 
            ["f"; "g"], 
            [parse @"f(f(x)) = f(x)";
            parse @"g(g(x)) = f(x)";
            parse @"f(g(x)) = g(x)";
            parse @"g(f(x)) = f(x)"; ],
            [Atom (R ("=",[Fn ("g",[Var "x0"]); Fn ("f",[Var "x0"])]));
            Atom (R ("=",[Fn ("f",[Fn ("f",[Var "x"])]); Fn ("f",[Var "x"])]))]
        );
        ( 
            // idx 31
            // completion.p050 
            // Baader & Nipkow #5 
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
        ( 
            // idx 32
            // completion.p051 
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
    (   
        // idx 33
        // completion.p013
        // completion.p023
        // K&B #7    
        ["f"], 
        [(parse @"f(a,f(b,c,a),d) = c")],
        [] // Dummy value used as place holder
    );
    (     
        // idx 34
        // completion.p025
        // K&B #8  
        ["*"], 
        [(parse @"(a * b) * (c * b * a) = b")],
        [] // Dummy value used as place holder
    );
    ( 
        // idx 35
        // completion.p041 
        // K&B #17   
        ["*"; "one"; "two"], 
        [(parse @"(a*a * a) = one(a)");
        (parse @"(a * a*a) = two(a)");
        (parse @"(a*b * b*c) = b")],
        [] // Dummy value used as place holder
    );
    (   
        // idx 36
        // completion.p044  
        ["1"; "/"], 
        [(parse @"((1 / (x / (y / (((x / x) / x) / z)))) / z) = y")],
        [] // Dummy value used as place holder
    );
    |]
    
[<Test>]
[<TestCase(15, TestName = "commutativity example", Category = "LongRunning")>]
[<TestCase(6, TestName = "K&B #1")>]
[<TestCase(17, TestName = "K&B #3", Category = "LongRunning")>]
[<TestCase(0, TestName = "K&B #4")>]
[<TestCase(9, TestName = "K&B #5")>]
[<TestCase(1, TestName = "K&B #6")>]
[<TestCase(4, TestName = "K&B #7")>]
[<TestCase(33, TestName = "K&B #7", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(34, TestName = "K&B #8", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(10, TestName = "K&B #9")>]
[<TestCase(3, TestName = "K&B #10")>]
[<TestCase(21, TestName = "K&B 11", Category = "LongRunning")>]
[<TestCase(22, TestName = "K&B 12", Category = "LongRunning")>]
[<TestCase(2, TestName = "K&B #12", Category = "LongRunning")>]
[<TestCase(12, TestName = "K&B #13", Category = "LongRunning")>]
[<TestCase(13, TestName = "K&B #14", Category = "LongRunning")>]
[<TestCase(14, TestName = "K&B #15")>]
[<TestCase(25, TestName = "K&B #16")>]
[<TestCase(35, TestName = "K&B #17", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(29, TestName = "Baader & Nipkow #1")>]
[<TestCase(30, TestName = "Baader & Nipkow #4")>]
[<TestCase(31, TestName = "Baader & Nipkow #5")>]
[<TestCase(5, TestName = "completion.p012")>]
[<TestCase(7, TestName = "completion.p016")>]
[<TestCase(16, TestName = "completion.p017 ", Category = "LongRunning")>]
[<TestCase(8, TestName = "completion.p020")>]
[<TestCase(11, TestName = "completion p032")>]
[<TestCase(18, TestName = "completion.p028", Category = "LongRunning")>]
[<TestCase(19, TestName = "completion.p029", Category = "LongRunning")>]
[<TestCase(20, TestName = "completion.p030", Category = "LongRunning")>]
[<TestCase(23, TestName = "completion.p038", Category = "LongRunning")>]
[<TestCase(24, TestName = "completion.p039", Category = "LongRunning")>]
[<TestCase(26, TestName = "completion.p042")>]
[<TestCase(27, TestName = "completion.p043", Category = "LongRunning")>]
[<TestCase(36, TestName = "completion.p044", ExpectedException=typeof<System.Collections.Generic.KeyNotFoundException>)>]
[<TestCase(28, TestName = "completion.p045", Category = "LongRunning")>]
[<TestCase(32, TestName = "completion.p051")>]
let ``complete and simplify tests`` idx =
    let (wts, _, _) = completeAndSimplifyValues.[idx]
    let (_, eqs, _) = completeAndSimplifyValues.[idx]
    let (_, _, result) = completeAndSimplifyValues.[idx]
    complete_and_simplify wts eqs
    |> should equal result    

let private funpowValues : ( int * (formula<fol> list * formula<fol> list * formula<fol> list -> formula<fol> list * formula<fol> list * formula<fol> list) * (formula<fol> list * formula<fol> list * formula<fol> list) * string list * string list * int)[] = [|
    ( 
        // idx 0
        // completion.p047
        // Baader & Nipkow #2 
        122, 
        (complete1 (lpo_ge (weight ["1"; "*"; "i"]))),
        ([parse @"f(f(x)) = g(x)"], [],unions (allpairs critical_pairs eqs eqs)),
        ["<<x2 *1 *x3 =x2 *x3>>";
        "<<i(x3 *x4 *i(1)) *x3 *x4 *x0 *x1 =x0 *x1>>";
        "<<i(x1 *x2 *1) *x1 *x2 *x4 *x5 =x4 *x5>>";
        "<<x1 *x2 *x3 *1 *x0 =x1 *x2 *x3 *x0>>";
        "<<i(x1 *x2 *i(x4)) *x1 *x2 *1 *x5 =x4 *x5>>";
        "<<i(x4 *x5 *x6 *x7 *x8 *x3) *x4 *x5 *x6 *x7 *x8 *x3 *x0 =1 *x0>>";
        "<<i(x4 *x5 *x2 *x7 *x8) *x4 *x5 *x2 *x7 *x8 *x0 =1 *x0>>";
        "<<i(x1 *x4 *x5 *x6 *x7 *x8 *x9) *x1 *x4 *x5 *x6 *x7 *x8 *x9 *x0 =1 *x0>>";
        "<<i(x4 *x3) *x4 *x3 *x0 =1 *x0>>";
        "<<i(x1 *x2 *i(i(x4))) *x1 *x2 *x4 *x5 =1 *x5>>";
        "<<i(x6 *x5 *x3) *x6 *x5 *x3 *x0 =1 *x0>>";
        "<<i(x1 *x6 *x5 *x7) *x1 *x6 *x5 *x7 *x0 =1 *x0>>";
        "<<i(x1 *x2 *x6 *i(x4)) *x1 *x2 *x6 *x5 *x7 =x4 *x5 *x7>>";
        "<<i(x5 *x6 *i(x1 *x2 *x3)) *x5 *x6 *1 *x0 =x1 *x2 *x3 *x0>>";
        "<<i(i(x1 *x2 *x3) *x1 *x2 *x3 *x0 *x7) *x0 *x7 *x4 =1 *x4>>";
        "<<i(1 *x0) *x0 *x4 =1 *x4>>";
        "<<i(x5 *1 *x0) *x5 *x0 *x4 =1 *x4>>";
        "<<x2 *i(x4 *x5 *x6) *x4 *x5 *x6 *x1 *x3 =x2 *x1 *x3>>";
        "<<i(x2 *i(x0)) *x2 *x1 *x3 =x0 *x1 *x3>>";
        "<<x2 *i(x4 *x5 *x6) *x4 *x5 *x6 *x7 *x8 *x9 *x3 =x2 *x7 *x8 *x9 *x3>>";
        "<<x2 *i(x4 *x5) *x4 *x5 *x1 *x7 *x8 *x9 =x2 *x1 *x7 *x8 *x9>>";
        "<<x6 *i(x2 *i(x0)) *x2 *x1 *x3 *x7 =x6 *x0 *x1 *x3 *x7>>";
        "<<i(i(x0)) *x2 *x3 =x0 *x2 *x3>>";
        "<<x2 *i(i(x0)) *x1 *x5 =x2 *x0 *x1 *x5>>";
        "<<i(i(i(x0))) *x0 *x1 =1 *x1>>";
        "<<x2 *x3 *x4 *i(i(x0)) *x1 *x7 =x2 *x3 *x4 *x0 *x1 *x7>>";
        "<<i(i(x0)) *x1 *x4 *x5 *x6 *x7 =x0 *x1 *x4 *x5 *x6 *x7>>";
        "<<(x3 *x4) *x5 =x3 *x4 *x5>>";
        "<<((x0 *x1) *x2) *i(x6) *(x6 *x7) *x5 =((x0 *x1) *x2) *x7 *x5>>";
        "<<((x6 *x7) *x8) *x0 *x1 *x10 *(x3 *x4) *x5 =((x6 *x7) *x8) *x0 *x1 *x10 *x3 *x4 *x5>>";
        "<<((x6 *x7) *x8) *x0 *x1 *x2 *((x3 *x4) *x5) *x11 =((x6 *x7) *x8) *x0 *x1 *x2 *(x3 *x4) *x5 *x11>>";
        "<<i(1) *x2 *x3 =x2 *x3>>";
        "<<i(x2 *x3 *x4) *(x2 *x3) *x4 *x1 =1 *x1>>";
        "<<(x2 *i(x0)) *(x0 *x1) *x5 =(x2 *1) *x1 *x5>>";
        "<<i(i(x0)) *1 *x1 =x0 *x1>>";
        "<<((x0 *x1) *x2) *(x5 *x6) *x7 =((x0 *x1) *x2) *x5 *x6 *x7>>";
        "<<i(x1) *x1 *x2 =1 *x2>>";
        "<<(x0 *x1 *x4) *x5 =(x0 *x1) *x4 *x5>>";
        "<<1 *x1 *x2 =x1 *x2>>";
        "<<f(f(x)) =g(x)>>"],
        ["<<((1 *x7) *x2) *(x3 *x4) *x5 =((i(x6) *x6 *x7) *x2) *x3 *x4 *x5>>";
         "<<(1 *x4) *x5 =(i(x3) *x3) *x4 *x5>>"; "<<(x1 *x2) *x3 =(1 *x1) *x2 *x3>>";
         "<<(x0 *x4 *x5) *x3 =(x0 *1) *(x4 *x5) *x3>>";
         "<<(x4 *(x0 *x1) *x2 *x6) *x7 =(x4 *x0 *x1 *x2) *x6 *x7>>"],
         6329   // Note: Only count is given as full list is just unwarranted
    );
    ( 
        // idx 1
        // completion.p048
        // Baader & Nipkow #3
        123, 
        (complete1 (lpo_ge (weight ["1"; "*"; "i"]))),
        ([parse @"f(f(x)) = g(x)"], [],unions (allpairs critical_pairs eqs eqs)),
        ["<<x2 *1 *x3 =x2 *x3>>"; "<<i(x3 *x4 *i(1)) *x3 *x4 *x0 *x1 =x0 *x1>>";
         "<<i(x1 *x2 *1) *x1 *x2 *x4 *x5 =x4 *x5>>";
         "<<x1 *x2 *x3 *1 *x0 =x1 *x2 *x3 *x0>>";
         "<<i(x1 *x2 *i(x4)) *x1 *x2 *1 *x5 =x4 *x5>>";
         "<<i(x4 *x5 *x6 *x7 *x8 *x3) *x4 *x5 *x6 *x7 *x8 *x3 *x0 =1 *x0>>";
         "<<i(x4 *x5 *x2 *x7 *x8) *x4 *x5 *x2 *x7 *x8 *x0 =1 *x0>>";
         "<<i(x1 *x4 *x5 *x6 *x7 *x8 *x9) *x1 *x4 *x5 *x6 *x7 *x8 *x9 *x0 =1 *x0>>";
         "<<i(x4 *x3) *x4 *x3 *x0 =1 *x0>>";
         "<<i(x1 *x2 *i(i(x4))) *x1 *x2 *x4 *x5 =1 *x5>>";
         "<<i(x6 *x5 *x3) *x6 *x5 *x3 *x0 =1 *x0>>";
         "<<i(x1 *x6 *x5 *x7) *x1 *x6 *x5 *x7 *x0 =1 *x0>>";
         "<<i(x1 *x2 *x6 *i(x4)) *x1 *x2 *x6 *x5 *x7 =x4 *x5 *x7>>";
         "<<i(x5 *x6 *i(x1 *x2 *x3)) *x5 *x6 *1 *x0 =x1 *x2 *x3 *x0>>";
         "<<i(i(x1 *x2 *x3) *x1 *x2 *x3 *x0 *x7) *x0 *x7 *x4 =1 *x4>>";
         "<<i(1 *x0) *x0 *x4 =1 *x4>>"; "<<i(x5 *1 *x0) *x5 *x0 *x4 =1 *x4>>";
         "<<x2 *i(x4 *x5 *x6) *x4 *x5 *x6 *x1 *x3 =x2 *x1 *x3>>";
         "<<i(x2 *i(x0)) *x2 *x1 *x3 =x0 *x1 *x3>>";
         "<<x2 *i(x4 *x5 *x6) *x4 *x5 *x6 *x7 *x8 *x9 *x3 =x2 *x7 *x8 *x9 *x3>>";
         "<<x2 *i(x4 *x5) *x4 *x5 *x1 *x7 *x8 *x9 =x2 *x1 *x7 *x8 *x9>>";
         "<<x6 *i(x2 *i(x0)) *x2 *x1 *x3 *x7 =x6 *x0 *x1 *x3 *x7>>";
         "<<i(i(x0)) *x2 *x3 =x0 *x2 *x3>>"; "<<x2 *i(i(x0)) *x1 *x5 =x2 *x0 *x1 *x5>>";
         "<<i(i(i(x0))) *x0 *x1 =1 *x1>>";
         "<<x2 *x3 *x4 *i(i(x0)) *x1 *x7 =x2 *x3 *x4 *x0 *x1 *x7>>";
         "<<i(i(x0)) *x1 *x4 *x5 *x6 *x7 =x0 *x1 *x4 *x5 *x6 *x7>>";
         "<<(x3 *x4) *x5 =x3 *x4 *x5>>";
         "<<((x0 *x1) *x2) *i(x6) *(x6 *x7) *x5 =((x0 *x1) *x2) *x7 *x5>>";
         "<<((x6 *x7) *x8) *x0 *x1 *x10 *(x3 *x4) *x5 =((x6 *x7) *x8) *x0 *x1 *x10 *x3 *x4 *x5>>";
         "<<((x6 *x7) *x8) *x0 *x1 *x2 *((x3 *x4) *x5) *x11 =((x6 *x7) *x8) *x0 *x1 *x2 *(x3 *x4) *x5 *x11>>";
         "<<i(1) *x2 *x3 =x2 *x3>>"; "<<i(x2 *x3 *x4) *(x2 *x3) *x4 *x1 =1 *x1>>";
         "<<(x2 *i(x0)) *(x0 *x1) *x5 =(x2 *1) *x1 *x5>>"; "<<i(i(x0)) *1 *x1 =x0 *x1>>";
         "<<((x0 *x1) *x2) *(x5 *x6) *x7 =((x0 *x1) *x2) *x5 *x6 *x7>>";
         "<<i(x1) *x1 *x2 =1 *x2>>"; "<<(x0 *x1 *x4) *x5 =(x0 *x1) *x4 *x5>>";
         "<<1 *x1 *x2 =x1 *x2>>"; "<<f(f(x)) =g(x)>>"],
        ["<<((1 *x7) *x2) *(x3 *x4) *x5 =((i(x6) *x6 *x7) *x2) *x3 *x4 *x5>>";
         "<<(1 *x4) *x5 =(i(x3) *x3) *x4 *x5>>"; "<<(x1 *x2) *x3 =(1 *x1) *x2 *x3>>";
         "<<(x0 *x4 *x5) *x3 =(x0 *1) *(x4 *x5) *x3>>";
         "<<(x4 *(x0 *x1) *x2 *x6) *x7 =(x4 *x0 *x1 *x2) *x6 *x7>>"],
         6328   // Note: Only count is given as full list is just unwarranted
    );
    |]

[<Test>]
[<TestCase(0, TestName = "Baader & Nipkow #2")>]
[<TestCase(1, TestName = "Baader & Nipkow #3")>]
let ``funpow tests`` idx =
    let (n, _, _, _, _, _) = funpowValues.[idx]
    let (_, f, _, _, _, _) = funpowValues.[idx]
    let (_, _, x, _, _, _) = funpowValues.[idx]
    let (_, _, _, eqsResult, _, _) = funpowValues.[idx]
    let (_, _, _, _, defResult, _) = funpowValues.[idx]
    let (_, _, _, _, _, critsCount) = funpowValues.[idx]
    let eqs,def,crits = funpow n f x
    // Note: AST is not used here because they are just to large to be practical here.
    // Could store them in a seperate file and then use them.
    List.map sprint_fol_formula eqs
    |> should equal eqsResult
    List.map sprint_fol_formula def
    |> should equal defResult
    List.length crits
    |> should equal critsCount

// ========================================================================================


// ----------------------------------------------------------------------------------------

let private iproveValues : (formula<fol> list * formula<fol> * formula<fol> list)[] =  
    [|
        ( 
            // idx 0
            // completion.p053  
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
        ( 
            // idx 1
            // completion.p054  
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
        ( 
            // idx 2
            // completion.p055  
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
        ( 
            // idx 3
            // completion.p056  
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
        ( 
            // idx 4
            // completion.p057  
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
        ( 
            // idx 5
            // completion.p058  
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
        ( 
            // idx 6
            // completion.p059  
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
        ( 
            // idx 7
            // completion.p060  
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
        ( 
            // idx 8
            // completion.p061  
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
        ( 
            // idx 9
            // completion.p062  
            [(parse @"rev(append(x,y)) = append(rev(y),rev(x))")],
            (parse @"rev(rev(x)) = x"),
            [] // Dummy value used as place holder
        );
        ( 
            // idx 10
            // completion.p063  
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

[<Test>]
[<TestCase(0, TestName = "completion.p053")>]
[<TestCase(1, TestName = "completion.p054")>]
[<TestCase(2, TestName = "completion.p055")>]
[<TestCase(3, TestName = "completion.p056")>]
[<TestCase(4, TestName = "completion.p057")>]
[<TestCase(5, TestName = "completion.p058")>]
[<TestCase(6, TestName = "completion.p059")>]
[<TestCase(7, TestName = "completion.p060")>]
[<TestCase(8, TestName = "completion.p061")>]
[<TestCase(9, TestName = "completion.p062", Category = "LongRunning")>]
[<TestCase(10, TestName = "completion.p063")>]
let ``iprove tests`` idx =
    let eqs039 =
        [parse @"0 + y = y";
        parse @"SUC(x) + y = SUC(x + y)";
        parse @"append(nil,l) = l";
        parse @"append(h::t,l) = h::append(t,l)";
        parse @"length(nil) = 0";
        parse @"length(h::t) = SUC(length(t))";
        parse @"rev(nil) = nil";
        parse @"rev(h::t) = append(rev(t),h::nil)"; ]
    let iprove eqs' tm =
        complete_and_simplify
            ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
            (tm :: eqs' @ eqs039)
    let (eqs', _, _) = iproveValues.[idx]
    let (_, tm, _) = iproveValues.[idx]
    let (_, _, result) = iproveValues.[idx]
    iprove eqs' tm
    |> should equal result
