// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.Tests.prolog

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.resolution
open Reasoning.Automated.Harrison.Handbook.prolog

open NUnit.Framework
open FsUnit

// pg. 208
// ------------------------------------------------------------------------- //
// A Horn example.                                                           //
// ------------------------------------------------------------------------- //

[<Test>]
let ``hornprove``() =    
    hornprove (parse @" 
        (forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\ 
        (forall x. Q(x) /\ H(x) ==> J(x)) /\ 
        (forall x. R(x) ==> H(x)) 
        ==> (forall x. P(x) /\ R(x) ==> J(x))")
        |> should equal
        <| (Map.ofList [
                ("_0", Fn ("c_x", []));
                ("_1", Var "_0");
                ("_2", Var "_0");
                ("_3", Var "_2");],
                8)

// pg. 210
// ------------------------------------------------------------------------- //
// Ordering example.                                                         //
// ------------------------------------------------------------------------- //

let lerules = ["0 <= X"; "S(X) <= S(Y) :- X <= Y"]

[<Test>]
let ``simple prolog``() =  
    simpleprolog lerules @"S(S(0)) <= S(S(S(0)))"
    |> should equal
    <| Map.ofList [
            ("_0", Fn ("S", [Fn ("0", [])]));
            ("_1", Fn ("S", [Fn ("S", [Fn ("0", [])])]));
            ("_2", Fn ("0", []));
            ("_3", Fn ("S", [Fn ("0", [])]));
            ("_4", Var "_3"); ]

[<Test>]
let ``apply``() = 
    let env = simpleprolog lerules @"S(S(0)) <= X"
    apply env "X"
    |> should equal (Fn ("S",[Var "_1"]))

// pg. 211
// ------------------------------------------------------------------------- //
// Example again.                                                            //
// ------------------------------------------------------------------------- //
   
[<Test>]
let ``prolog all``() = 
    prolog lerules @"S(S(0)) <= X"
    |> should equal [Atom (R ("=",[Var "X"; Fn ("S",[Fn ("S",[Var "_3"])])]))]


// pg. 211
// ------------------------------------------------------------------------- //
// Append example, showing symmetry between inputs and outputs.              //
// ------------------------------------------------------------------------- //

let appendrules = [
    @"append(nil,L,L)";
    @"append(H::T,L,H::A) :- append(T,L,A)";]

[<Test>]
let ``prolog appenedrules 1``() = 
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

[<Test>]
let ``prolog appenedrules 2``() = 
    prolog appendrules @"append(1::2::nil,Y,1::2::3::4::nil)"
    |> should equal [Atom
                            (R ("=",
                                [Var "Y";
                                Fn
                                ("::",[Fn ("3",[]); Fn ("::",[Fn ("4",[]); Fn ("nil",[])])])]))]

[<Test>]
let ``prolog appenedrules 3``() = 
    prolog appendrules @"append(X,3::4::nil,1::2::3::4::nil)"
    |> should equal [Atom
                            (R ("=",
                                [Var "X";
                                Fn
                                ("::",[Fn ("1",[]); Fn ("::",[Fn ("2",[]); Fn ("nil",[])])])]))]

[<Test>]
let ``prolog appenedrules 4``() = 
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

