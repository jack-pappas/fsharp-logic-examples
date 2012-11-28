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

// pg. 208
// ------------------------------------------------------------------------- //
// A Horn example.                                                           //
// ------------------------------------------------------------------------- //

// prolog.p001
// Pelletier #32
[<Test>]
let ``Pelletier #32``() =    
    hornprove (parse @" 
        (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
        (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
        (forall x. R(x) ==> H(x)) 
        ==> (forall x. P(x) /\ R(x) ==> J(x))")
    |> should equal (Branch
                         (47089,65536,
                          Branch
                            (47089,131072,Leaf (-843532303,[("_2", Var "_0")]),
                             Leaf (-843401231,[("_0", Fn ("c_x",[]))])),
                          Branch
                            (112625,131072,Leaf (-843466767,[("_1", Var "_0")]),
                             Leaf (-843597839,[("_3", Var "_2")]))), 8)

// pg. 208
// ------------------------------------------------------------------------- //
// A non-Horn example.                                                       //
// ------------------------------------------------------------------------- //

// prolog.p002
// System.Exception: non-Horn clause. - This is the expected result.
// Pelletier #09
// TODO: Figure out how to get NUnit to work with exception
//[<Test>]
//let ``non-Horn``() = 
//    hornprove (parse @"(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)") 

// pg. 210
// ------------------------------------------------------------------------- //
// Ordering example.                                                         //
// ------------------------------------------------------------------------- //

let lerules = ["0 <= X"; "S(X) <= S(Y) :- X <= Y"]

// prolog.p003
[<Test>]
let ``backchaining``() =  
    simpleprolog lerules @"S(S(0)) <= S(S(S(0)))"
    |> should equal (Branch
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
                            Leaf (-843597839,[("_3", Fn ("S",[Fn ("0",[])]))]))))

// prolog.p005
[<Test>]
let ``apply``() = 
    let env = simpleprolog lerules @"S(S(0)) <= X"
    apply env "X"
    |> should equal (Fn ("S",[Var "_1"]))

// pg. 211
// ------------------------------------------------------------------------- //
// Example again.                                                            //
// ------------------------------------------------------------------------- //
   
// prolog.p006
[<Test>]
let ``binding``() = 
    prolog lerules @"S(S(0)) <= X"
    |> should equal [Atom (R ("=",[Var "X"; Fn ("S",[Fn ("S",[Var "_3"])])]))]


// pg. 211
// ------------------------------------------------------------------------- //
// Append example, showing symmetry between inputs and outputs.              //
// ------------------------------------------------------------------------- //

let appendrules = [
    @"append(nil,L,L)";
    @"append(H::T,L,H::A) :- append(T,L,A)";]

// prolog.p007
[<Test>]
let ``appened 1``() = 
    prolog appendrules @"append(1::2::nil,3::4::nil,Z)"
    |> should equal [Atom
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

// prolog.p008
[<Test>]
let ``appened 2``() = 
    prolog appendrules @"append(1::2::nil,Y,1::2::3::4::nil)"
    |> should equal [Atom
                            (R ("=",
                                [Var "Y";
                                Fn
                                ("::",[Fn ("3",[]); Fn ("::",[Fn ("4",[]); Fn ("nil",[])])])]))]

// prolog.p009
[<Test>]
let ``appened 3``() = 
    prolog appendrules @"append(X,3::4::nil,1::2::3::4::nil)"
    |> should equal [Atom
                            (R ("=",
                                [Var "X";
                                Fn
                                ("::",[Fn ("1",[]); Fn ("::",[Fn ("2",[]); Fn ("nil",[])])])]))]

// prolog.p010
[<Test>]
let ``appened 4``() = 
    prolog appendrules @"append(X,Y,1::2::3::4::nil)"
    |> should equal [Atom (R ("=",[Var "X"; Fn ("nil",[])]));
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

let sortrules = [
    @"sort(X,Y) :- perm(X,Y),sorted(Y)";
    @"sorted(nil)";
    @"sorted(X::nil)";
    @"sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
    @"perm(nil,nil)";
    @"perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
    @"delete(X,X::Y,Y)";
    @"delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
    @"0 <= X";
    @"S(X) <= S(Y) :- X <= Y"; ];;

// prolog.p012
[<Test>]
let ``sort``() = 
    prolog sortrules
        @"sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)"
    |> should equal [Atom
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
