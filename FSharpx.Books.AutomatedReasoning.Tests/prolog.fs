// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.Tests.prolog

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.intro
open FSharpx.Books.AutomatedReasoning.formulas
open FSharpx.Books.AutomatedReasoning.prop
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.skolem
open FSharpx.Books.AutomatedReasoning.unif
open FSharpx.Books.AutomatedReasoning.tableaux
open FSharpx.Books.AutomatedReasoning.resolution
open FSharpx.Books.AutomatedReasoning.prolog

open NUnit.Framework
open FsUnit

let private hornproveValues : (string * (func<string,term> * int))[] = [| 
    (
        // idx 0
        // prolog.p001
        // Pelletier #32
        @"(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
        (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
        (forall x. R(x) ==> H(x)) 
        ==> (forall x. P(x) /\ R(x) ==> J(x))",
        (Branch
           (47089,65536,
            Branch
              (47089,131072,Leaf (-843532303,[("_2", Var "_0")]),
               Leaf (-843401231,[("_0", Fn ("c_x",[]))])),
            Branch
              (112625,131072,Leaf (-843466767,[("_1", Var "_0")]),
               Leaf (-843597839,[("_3", Var "_2")]))), 8)
    );
    (
        // idx 1
        // prolog.p002
        // Pelletier #09
        @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)",
        (undefined, -99) // Dummy value used as place holder
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "prolog.p001")>]
[<TestCase(1, TestName = "prolog.p002",
    ExpectedException = typeof<System.Exception>,
    ExpectedMessage = "non-Horn clause")>]
let ``hornprove tests`` (idx) =
    let (formula, _) = hornproveValues.[idx]
    let (_, result) = hornproveValues.[idx]
    let (proof,size) = hornprove (parse formula)
    (proof,size)
    |> should equal result

let private simpleprologValues : (string list * string * func<string,term>)[] = [| 
    (
        // idx 0
        // prolog.p003
        ["0 <= X"; "S(X) <= S(Y) :- X <= Y"],
        @"S(S(0)) <= S(S(S(0)))",
        Branch
          (47089,65536,
           Branch
             (47089,131072,Leaf (-843532303,[("_2", Fn ("0",[]))]),
              Branch
                (178161,262144,
                 Leaf (-843401231,[("_0", Fn ("S",[Fn ("0",[])]))]),
                 Leaf (-843663375,[("_4", Var "_3")]))),
           Branch
             (112625,131072,
              Leaf (-843466767,[("_1", Fn ("S",[Fn ("S",[Fn ("0",[])])]))]),
              Leaf (-843597839,[("_3", Fn ("S",[Fn ("0",[])]))])))
    );
    (
        // idx 1
        // prolog.p004
        ["0 <= X"; "S(X) <= S(Y) :- X <= Y"],
        @"S(S(0)) <= S(0)",
        undefined // Dummy value used as place holder
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "prolog.p003")>]
[<TestCase(1, TestName = "prolog.p004",
    ExpectedException = typeof<System.Exception>,
    ExpectedMessage = "tryfind")>]
let ``simpleprolog tests`` (idx) =
    let (rules, _, _) = simpleprologValues.[idx]
    let (_,  gl, _) = simpleprologValues.[idx]
    let (_, _, result) = simpleprologValues.[idx]
    simpleprolog rules gl
    |> should equal result

let private applyValues : (func<string,term> * string * term)[] = [| 
    (
        // idx 0
        // prolog.p005
        (simpleprolog ["0 <= X"; "S(X) <= S(Y) :- X <= Y"] @"S(S(0)) <= X" ),
        "X",
        Fn ("S",[Var "_1"])
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "prolog.p005")>]
let ``apply tests`` (idx) =
    let (formula, _, _) = applyValues.[idx]
    let (_, x, _) = applyValues.[idx]
    let (_, _, result) = applyValues.[idx]
    apply formula x
    |> should equal result

// TODO: Modify printers to handle list of type also.
// i.e. sprint_fol_formula should handle formula<fol> and formula<fol> list
let private prologValues : (string list * string * formula<fol> list)[] =  [| 
    (
        // idx 0
        // prolog.p006
        ["0 <= X"; "S(X) <= S(Y) :- X <= Y"],
        @"S(S(0)) <= X",
        [Atom (R ("=",[Var "X"; Fn ("S",[Fn ("S",[Var "_3"])])]))]
    );
    (
        // idx 1
        // prolog.p007
        [@"append(nil,L,L)";
        @"append(H::T,L,H::A) :- append(T,L,A)";],
        @"append(1::2::nil,3::4::nil,Z)",
        [Atom
            (R ("=",
                [Var "Z";
                Fn
                ("::",
                    [Fn ("1",[]);
                    Fn
                    ("::",
                        [Fn ("2",[]);
                        Fn
                        ("::",
                            [Fn ("3",[]);
                            Fn ("::",[Fn ("4",[]); Fn ("nil",[])])])])])]))]
    );
    (
        // idx 2
        // prolog.p008
        [@"append(nil,L,L)";
        @"append(H::T,L,H::A) :- append(T,L,A)";],
        @"append(1::2::nil,Y,1::2::3::4::nil)",
        [Atom
           (R ("=",
               [Var "Y";
                Fn
                  ("::",[Fn ("3",[]); Fn ("::",[Fn ("4",[]); Fn ("nil",[])])])]))]
    );
    (
        // idx 3
        // prolog.p009
        [@"append(nil,L,L)";
        @"append(H::T,L,H::A) :- append(T,L,A)";],
        @"append(X,3::4::nil,1::2::3::4::nil)",
        [Atom
           (R ("=",
               [Var "X";
                Fn
                  ("::",[Fn ("1",[]); Fn ("::",[Fn ("2",[]); Fn ("nil",[])])])]))]
    );
    (
        // idx 4
        // prolog.p010
        [@"append(nil,L,L)";
        @"append(H::T,L,H::A) :- append(T,L,A)";],
        @"append(X,Y,1::2::3::4::nil)",
        [Atom (R ("=",[Var "X"; Fn ("nil",[])]));
         Atom
           (R ("=",
               [Var "Y";
                Fn
                  ("::",
                   [Fn ("1",[]);
                    Fn
                      ("::",
                       [Fn ("2",[]);
                        Fn
                          ("::",
                           [Fn ("3",[]);
                            Fn ("::",[Fn ("4",[]); Fn ("nil",[])])])])])]))]
    );
    (
        // idx 5
        // prolog.p011
        [@"append(nil,L,L)";
        @"append(H::T,L,H::A) :- append(T,L,A)";],
        @"append(X,3::4::nil,X)",
        [] // Dummy value used as place holder
        // Note: Causes StackOverflowException which NUnit can't handle correctly.
        // Tried using try with around prolog, but NUnit still captures exceptions and aborts.
    );
    (
        // idx 6
        // prolog.p012
        [@"sort(X,Y) :- perm(X,Y),sorted(Y)";
        @"sorted(nil)";
        @"sorted(X::nil)";
        @"sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
        @"perm(nil,nil)";
        @"perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
        @"delete(X,X::Y,Y)";
        @"delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
        @"0 <= X";
        @"S(X) <= S(Y) :- X <= Y"; ],
        @"sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)",
        [Atom
           (R ("=",
               [Var "X";
                Fn
                  ("::",
                   [Fn ("0",[]);
                    Fn
                      ("::",
                       [Fn ("S",[Fn ("0",[])]);
                        Fn
                          ("::",
                           [Fn ("S",[Fn ("0",[])]);
                            Fn
                              ("::",
                               [Fn ("S",[Fn ("S",[Fn ("0",[])])]);
                                Fn
                                  ("::",
                                   [Fn
                                      ("S",
                                       [Fn
                                          ("S",
                                           [Fn ("S",[Fn ("S",[Fn ("0",[])])])])]);
                                    Fn ("nil",[])])])])])])]))]
    );
    (
        // idx 7
        // prolog.p013
        [@"sort(X,Y) :- sorted(Y), perm(X,Y)";
        @"sorted(nil)";
        @"sorted(X::nil)";
        @"sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
        @"perm(nil,nil)";
        @"perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
        @"delete(X,X::Y,Y)";
        @"delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
        @"0 <= X";
        @"S(X) <= S(Y) :- X <= Y"; ],
        @"sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)",
        [] // Dummy value used as place holder
        // Note: Causes StackOverflowException which NUnit can't handle correctly.
        // Tried using try with around prolog, but NUnit still captures exceptions and aborts.
    );
    |]
    
[<Test>]
[<TestCase(0, TestName = "prolog.p006")>]
[<TestCase(1, TestName = "prolog.p007")>]
[<TestCase(2, TestName = "prolog.p008")>]
[<TestCase(3, TestName = "prolog.p009")>]
[<TestCase(4, TestName = "prolog.p010")>]
[<TestCase(6, TestName = "prolog.p012")>]
let ``prolog tests`` (idx) =
    let (rules, _, _) = prologValues.[idx]
    let (_, gl, _) = prologValues.[idx]
    let (_, _, resultAst) = prologValues.[idx]
    let result = prolog rules gl
    result
    |> should equal resultAst
