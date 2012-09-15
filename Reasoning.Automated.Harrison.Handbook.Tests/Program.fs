// IMPORTANT:  READ BEFORE DOWNLOADING, COPYING, INSTALLING OR USING.
// By downloading, copying, installing or using the software you agree
// to this license.  If you do not agree to this license, do not
// download, install, copy or use the software.
// 
// Copyright (c) 2003-2007, John Harrison
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of John Harrison may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
// FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
// CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
// USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.
//
// ===================================================================
//
// Converted to F# 2.0
//
// Copyright (c) 2012, Eric Taucher
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the previous disclaimer.
// 
// * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the previous disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// * The name of Eric Taucher may not be used to endorse or promote
// products derived from this software without specific prior written
// permission.
//
// ===================================================================

namespace Reasoning.Automated.Harrison.Handbook.Tests

open Reasoning.Automated.Harrison.Handbook.compatibility

open Reasoning.Automated.Harrison.Handbook.lib
open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
open Reasoning.Automated.Harrison.Handbook.propexamples
open Reasoning.Automated.Harrison.Handbook.defcnf
open Reasoning.Automated.Harrison.Handbook.dp
open Reasoning.Automated.Harrison.Handbook.stal
open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand
open Reasoning.Automated.Harrison.Handbook.unif
open Reasoning.Automated.Harrison.Handbook.tableaux
open Reasoning.Automated.Harrison.Handbook.resolution
open Reasoning.Automated.Harrison.Handbook.prolog
open Reasoning.Automated.Harrison.Handbook.meson
open Reasoning.Automated.Harrison.Handbook.skolems
open Reasoning.Automated.Harrison.Handbook.equal
open Reasoning.Automated.Harrison.Handbook.rewrite
open Reasoning.Automated.Harrison.Handbook.order
open Reasoning.Automated.Harrison.Handbook.completion
open Reasoning.Automated.Harrison.Handbook.eqelim
open Reasoning.Automated.Harrison.Handbook.paramodulation
open Reasoning.Automated.Harrison.Handbook.decidable
open Reasoning.Automated.Harrison.Handbook.qelim
open Reasoning.Automated.Harrison.Handbook.cooper
open Reasoning.Automated.Harrison.Handbook.complex
open Reasoning.Automated.Harrison.Handbook.real
open Reasoning.Automated.Harrison.Handbook.grobner
open Reasoning.Automated.Harrison.Handbook.geom
open Reasoning.Automated.Harrison.Handbook.interpolation
open Reasoning.Automated.Harrison.Handbook.combining
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
open Reasoning.Automated.Harrison.Handbook.folderived
open Reasoning.Automated.Harrison.Handbook.lcffol
open Reasoning.Automated.Harrison.Handbook.tactics

module Program =
    open System

    let pause () =
        Console.WriteLine ""
        Console.WriteLine "Press any key to continue."
        Console.ReadKey () |> ignore

    do
        let str = "(p ==> q) \/ (q ==> p)"
        let qq = default_parser str
        let theorem = lcftaut qq
        let qwomwef = "wfewplf".Length
        ()

    let [<Literal>] testString_0001 = ""
    let [<Literal>] testString_0002 = "false"
    let [<Literal>] testString_0003 = "true"
    let [<Literal>] testString_0004 = "(true)"
    let [<Literal>] testString_0005 = "~false"
    let [<Literal>] testString_0006 = "~true"
    let [<Literal>] testString_0007 = "~(true)"
    let [<Literal>] testString_0008 = "(~true)"
    let [<Literal>] testString_0009 = "true <=> false"
    let [<Literal>] testString_0010 = "true ==> false"
    let [<Literal>] testString_0011 = "true \/ false"
    let [<Literal>] testString_0012 = "true /\ false"
    let [<Literal>] testString_0013 = "a"
    let [<Literal>] testString_0014 = "a <=> b"
    let [<Literal>] testString_0015 = "a ==> b"
    let [<Literal>] testString_0016 = "a \/ b"
    let [<Literal>] testString_0017 = "a /\ b"
    let [<Literal>] testString_0018 = "forall x. x"
    let [<Literal>] testString_0019 = "(forall x. x)"
    let [<Literal>] testString_0020 = "(forall x. (x))"
    let [<Literal>] testString_0021 = "exists x. x"
    let [<Literal>] testString_0022 = "(exists x. x)"
    let [<Literal>] testString_0023 = "(exists x. (x))"
    let [<Literal>] testString_0024 = "true /\ false \/ true"
    let [<Literal>] testString_0025 = "forall x. x ==> true"
    let [<Literal>] testString_0026 = "forall x. (x ==> true)"

    let test_parse_prop_formula inp =
        let result = parse_prop_formula inp
        printfn "%A" result

//    let test0001 () = test_parse_prop_formula testString_0001    // this test will fail to parse
    let test0002 () = test_parse_prop_formula testString_0002
    let test0003 () = test_parse_prop_formula testString_0003
    let test0004 () = test_parse_prop_formula testString_0004
    let test0005 () = test_parse_prop_formula testString_0005
    let test0006 () = test_parse_prop_formula testString_0006
    let test0007 () = test_parse_prop_formula testString_0007
    let test0008 () = test_parse_prop_formula testString_0008
    let test0009 () = test_parse_prop_formula testString_0009
    let test0010 () = test_parse_prop_formula testString_0010
    let test0011 () = test_parse_prop_formula testString_0011
    let test0012 () = test_parse_prop_formula testString_0012
    let test0013 () = test_parse_prop_formula testString_0013
    let test0014 () = test_parse_prop_formula testString_0014
    let test0015 () = test_parse_prop_formula testString_0015
    let test0016 () = test_parse_prop_formula testString_0016
    let test0017 () = test_parse_prop_formula testString_0017
    let test0018 () = test_parse_prop_formula testString_0018
    let test0019 () = test_parse_prop_formula testString_0019
    let test0020 () = test_parse_prop_formula testString_0020
    let test0021 () = test_parse_prop_formula testString_0021
    let test0022 () = test_parse_prop_formula testString_0022
    let test0023 () = test_parse_prop_formula testString_0023
    let test0024 () = test_parse_prop_formula testString_0024
    let test0025 () = test_parse_prop_formula testString_0025
    let test0026 () = test_parse_prop_formula testString_0026
    
    let pfn = print_propvar

    let test_print_prop_formula inp =
        let parse_result = parse_prop_formula inp
        let print_result = print_formula pfn parse_result
        printfn ""

    let test1002 () = test_print_prop_formula testString_0002
    let test1003 () = test_print_prop_formula testString_0003
    let test1004 () = test_print_prop_formula testString_0004
    let test1005 () = test_print_prop_formula testString_0005
    let test1006 () = test_print_prop_formula testString_0006
    let test1007 () = test_print_prop_formula testString_0007
    let test1008 () = test_print_prop_formula testString_0008
    let test1009 () = test_print_prop_formula testString_0009
    let test1010 () = test_print_prop_formula testString_0010
    let test1011 () = test_print_prop_formula testString_0011
    let test1012 () = test_print_prop_formula testString_0012
    let test1013 () = test_print_prop_formula testString_0013
    let test1014 () = test_print_prop_formula testString_0014
    let test1015 () = test_print_prop_formula testString_0015
    let test1016 () = test_print_prop_formula testString_0016
    let test1017 () = test_print_prop_formula testString_0017
    let test1018 () = test_print_prop_formula testString_0018
    let test1019 () = test_print_prop_formula testString_0019
    let test1020 () = test_print_prop_formula testString_0020
    let test1021 () = test_print_prop_formula testString_0021
    let test1022 () = test_print_prop_formula testString_0022
    let test1023 () = test_print_prop_formula testString_0023
    let test1024 () = test_print_prop_formula testString_0024
    let test1025 () = test_print_prop_formula testString_0025
    let test1026 () = test_print_prop_formula testString_0026


    let formula0030String = "p"
    let formula0030 = parse_prop_formula formula0030String
    let formual0030Values p = 
        match p with
        | P("p") -> true
        | _               -> failwith "How did we get here?" 
    let test0030 () = 
        let result = eval formula0030 formual0030Values
        printfn "%O" result

    let formula0031String = "q"
    let formula0031 = parse_prop_formula formula0031String
    let formual0031Values p = 
        match p with
        | P("q") -> false
        | _               -> failwith "How did we get here?" 
    let test0031 () = 
        let result = eval formula0031 formual0031Values
        printfn "%O" result

    let formula0032String = "p /\ q"
    let formula0032 = parse_prop_formula formula0032String
    let formual0032Values p = 
        match p with
        | P("p") -> true
        | P("q") -> false
        | _               -> failwith "How did we get here?"
    let test0032 () = 
        let result = eval formula0032 formual0032Values
        printfn "%O" result

    let test0040 () =
        let sum = itlist (+) [1;2;3] 0
        printfn "sum: %O" sum

    let test0041 () =
        let word = itlist (+) ["a";"b";"c"] ""
        printfn "concatenate: %O" word

    let test0042 () =
        let concatFun (x : string) (y : string) =
            x + y
        let word = itlist (concatFun) ["a";"b";"c"] ""
        printfn "concatenate: %O" word

    let test0043 () =
        let widthFun x y =
           max (String.length x)  y
        let word = itlist (widthFun) ["a";"bbbbbbbb";"cc"] 0
        printfn "concatenate: %O" word

    let test0044 () =
        let ats = [P "p"; P "q"; P "r"]
        let widthFun x y =
            max (String.length (pname x)) y
        let width = itlist (widthFun) ats 6
        printfn "Width: %A" width

    let test0045 () =
          let test0045String = "p /\ q ==> q /\ r"
          let formula0045 = parse_prop_formula test0045String
          print_truthtable formula0045

    // Note to access operators defined in a seperator module need to reference full name of module
    // i.e. open Reasoning.Automated.Harrison.Handbook.lib
    let test0046 () =
        let nums = [1;2;3]
        let func1 x = x + 1          // first function takes one value
        let func2 x = x + 10         // fucntions other than last takes one value
        let func3 x y = x + y + 100  // last function takes two values
        let width = itlist (func3 >>|> func2 >>|> func1) nums 0
        printfn "Width: %A" width

    let test0047 () =
        let letters = ["a";"b";"c"]
        let func1 x = x + ":"        // first function takes one value
        let func2 x = x + "#"        // fucntions other than last takes one value
        let func3 x y = x + "&&" + y        // last function takes two values
        let width = itlist (func3 >>|> func2 >>|> func1) letters ""
        printfn "Width: %A" width

    let test0048 () =
        let ats = [P "p"; P "q"; P "r"]
        let width = itlist (max >>|> String.length >>|> pname) ats 6
        printfn "Width: %A" width

    let test0050 () =
        let z = halfsum True False
        printfn "halfsum True False: %A" z
    // Iff (True,Not False)

    let test0051 () =
        let z = halfcarry True False
        printfn "halfcarry True False: %A" z
    // And (True,False)

    let test0052 () =
        let z = ha True False True False
        printfn "ha True False True False: %A" z
    // And (Iff (True,Iff (True,Not False)),Iff (False,And (True,False)))

    let test0053 () =
        let z = carry True False True
        printfn "carry True False True: %A" z
    // Or (And (True,False),And (Or (True,False),True))

    let test0054 () =
        let z = sum True False True
        printfn "sum True False True: %A" z
    // Iff (Iff (True,Not False),Not True)

    let test0055 () =
        let z = fa True False True False True
        printfn "fa True False True False True: %A" z
    // And
    //   (Iff (False,Iff (Iff (True,Not False),Not True)),
    //    Iff (True,Or (And (True,False),And (Or (True,False),True))))

    let test0056 () =
        let z = mk_index "X" 0
        printfn "mk_index \"X\" 2: %A" z
    // Atom (P "X_0")

    let test0057 () =
        let z = mk_index2 "X" 0 1
        printfn "mk_index \"X\" 0 1 : %A" z
    // Atom (P "X_0_1")
        
    let test0058 () =
        let z = 0 -- 5
        printfn "0 -- 5 : %A" z
    // [0; 1; 2; 3; 4; 5]
            
    let test0059 () =
        let z = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        printfn "map mk_index [\"X\"; \"Y\"; \"OUT\"; \"C\"] : %A" z
    // [<fun:Invoke@2920>; <fun:Invoke@2920>; <fun:Invoke@2920>; <fun:Invoke@2920>]

    let test0060 () =
        let z = List.map mk_index ["X";]
        printfn "map mk_index [\"X\"] : %A" z
    // [<fun:Invoke@2920>]

    let test0061 () =
        let notX x = Not x
        let z = notX 
        printfn "notX : %A" z
    //  <fun:notX@291T>

    let test0062 () =
        let notX x = Not x
        let z = notX 
        printfn "notX : %A" (z True)
    //  Not True

    let test0063 () =
        let a = mk_index "X";
        let b = List.map a
        printfn "map mk_index \"X\" [1] : %A" (b [1])
    // [Atom (P "X_1")]

    let test0064 () =
        let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let rec visit x =
            match x with
            | [] -> ()
            | h::t -> 
                printfn "%A" h
                visit t
        visit funcs
    // <fun:Invoke@2920>
    // <fun:Invoke@2920>
    // <fun:Invoke@2920>
    // <fun:Invoke@2920>

    let test0065 () =
        let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let rec visit x =
            match x with
            | [] -> ()
            | h::t -> 
                let z = h 1
                printfn "%A" z
                visit t
        visit funcs
    // Atom (P "X_1")
    // Atom (P "Y_1")
    // Atom (P "OUT_1")
    // Atom (P "C_1")

    let test0066 () =
        let funcList = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let funcArray = List.toArray funcList
        for i in 0 .. funcArray.Length - 1 do
            let func = Array.get funcArray i
            let z = func 1
            printfn "%A" z
    // Atom (P "X_1")
    // Atom (P "Y_1")
    // Atom (P "OUT_1")
    // Atom (P "C_1")

    let test0067 () =
        let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let x =  funcs.[0]
        let y = funcs.[1]
        let out = funcs.[2]
        let c = funcs.[3]
        printfn "%A" (x 0)
        printfn "%A" (y 0)
        printfn "%A" (out 0)
        printfn "%A" (c 0)
    // Atom (P "X_0")
    // Atom (P "Y_0")
    // Atom (P "OUT_0")
    // Atom (P "C_0")

    let test0068 () =
        let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let x = funcs.[0]
        let y = funcs.[1]
        let out = funcs.[2]
        let c = funcs.[3]
        let z = fa (x 1) (y 1) (c 1) (out 1) (c 2) 
        printfn "%A" z
    // And
    //   (Iff
    //      (Atom (P "OUT_1"),
    //       Iff (Iff (Atom (P "X_1"),Not (Atom (P "Y_1"))),Not (Atom (P "C_1")))),
    //    Iff
    //      (Atom (P "C_2"),
    //       Or
    //         (And (Atom (P "X_1"),Atom (P "Y_1")),
    //          And (Or (Atom (P "X_1"),Atom (P "Y_1")),Atom (P "C_1")))))

    let test0069 () =
        let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let x = funcs.[0]
        let y = funcs.[1]
        let out = funcs.[2]
        let c = funcs.[3]
        let z = ripplecarry x y c out 2
        printfn "%A" z
    // And
    //   (And
    //      (Iff
    //         (Atom (P "OUT_0"),
    //          Iff (Iff (Atom (P "X_0"),Not (Atom (P "Y_0"))),Not (Atom (P "C_0")))),
    //       Iff
    //         (Atom (P "C_1"),
    //          Or
    //            (And (Atom (P "X_0"),Atom (P "Y_0")),
    //             And (Or (Atom (P "X_0"),Atom (P "Y_0")),Atom (P "C_0"))))),
    //    And
    //      (Iff
    //         (Atom (P "OUT_1"),
    //          Iff (Iff (Atom (P "X_1"),Not (Atom (P "Y_1"))),Not (Atom (P "C_1")))),
    //       Iff
    //         (Atom (P "C_2"),
    //          Or
    //            (And (Atom (P "X_1"),Atom (P "Y_1")),
    //             And (Or (Atom (P "X_1"),Atom (P "Y_1")),Atom (P "C_1"))))))

    let test0070 () =
        let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let x = funcs.[0]
        let y = funcs.[1]
        let out = funcs.[2]
        let c = funcs.[3]
        let z = ripplecarry0 x y c out 2
        printfn "%A" z
    // And
    //  (And
    //     (Iff (Atom (P "OUT_0"),Iff (Atom (P "X_0"),Not (Atom (P "Y_0")))),
    //      Iff (Atom (P "C_1"),And (Atom (P "X_0"),Atom (P "Y_0")))),
    //   And
    //     (Iff
    //        (Atom (P "OUT_1"),
    //         Iff (Iff (Atom (P "X_1"),Not (Atom (P "Y_1"))),Not (Atom (P "C_1")))),
    //      Iff
    //        (Atom (P "C_2"),
    //         Or
    //           (And (Atom (P "X_1"),Atom (P "Y_1")),
    //            And (Or (Atom (P "X_1"),Atom (P "Y_1")),Atom (P "C_1"))))))

    let test0071 () =
        let funcs = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        let x = funcs.[0]
        let y = funcs.[1]
        let out = funcs.[2]
        let c = funcs.[3]
        let f = ripplecarry x y c out 2
        print_formula pfn f
    // ((OUT_0<=>(X_0<=>~Y_0)<=>~C_0)/\(C_1<=>X_0/\Y_0\/(X_0\/Y_0)/\C_0))/\(OUT_1<=>(X_1<=>~Y_1)<=>~C_1)/\(C_2<=>X_1/\Y_1\/(X_1\/Y_1)/\C_1)

//    let test0072 () =
//        // Note: This causes a warning because of imcomoplete pattern matching.
//        let [x; y; out; c] = List.map mk_index ["X"; "Y"; "OUT"; "C"]
//        let f = ripplecarry x y c out 2
//        print_formula pfn f
    // ((OUT_0<=>(X_0<=>~Y_0)<=>~C_0)/\(C_1<=>X_0/\Y_0\/(X_0\/Y_0)/\C_0))/\(OUT_1<=>(X_1<=>~Y_1)<=>~C_1)/\(C_2<=>X_1/\Y_1\/(X_1\/Y_1)/\C_1)

    let test0073 () =
        let l = List.map mk_index ["X"; "Y"; "OUT"; "C"]
        match l with
        | [x; y; out; c;] -> 
            let f = ripplecarry x y c out 2
            print_formula pfn f
        | _ -> failwith "test0074"
    // ((OUT_0<=>(X_0<=>~Y_0)<=>~C_0)/\(C_1<=>X_0/\Y_0\/(X_0\/Y_0)/\C_0))/\(OUT_1<=>(X_1<=>~Y_1)<=>~C_1)/\(C_2<=>X_1/\Y_1\/(X_1\/Y_1)/\C_1)

    let test0074 () =
        let x, y, out, c = mapTuple4 mk_index ("X", "Y", "OUT", "C")
        let f = ripplecarry x y c out 2
        print_formula pfn f

    let test0100 () =
        let data = [("Cats",4); ("Dogs",5); ("Mice", 3); ("Elephants", 2)]
        let count = List.fold (fun acc (nm,x) -> acc + x) 0 data
        printfn "Total number of animals: %d" count 

    let test0101 () =
        let data = [4; 5; 3; 2]
        let count = itlist (+) data 0
        printfn "Total number of animals: %d" count 

    let test0102 () =
        let data = [1; 2; 3; 4]
        let result = List.fold (fun acc x -> acc * x) 1 data
        // 1 * 4 * 3 * 2 * 1 = 24
        printfn "test0102 result: %d" result 

    let test0103 () =
        let data = ["a"; "b"; "c"; "d"]
        let result = List.fold (fun acc x -> acc + x) "" data
        printfn "test0103 result: %s" result 

    let test0104 () =
        let data = ["a"; "b"; "c"; "d"]
        let result = itlist (+) data ""
        printfn "test0104 result: %s" result 

    let test0105 () =
        let data = ["a"; "b"; "c"; "d"]
        let result = itlist (fun acc x -> acc + x) data ""
        printfn "test0105 result: %s" result 

    let test0106 () =
        let data = ["a"; "b"; "c"; "d"]
        let result = List.fold (+) "" data
        printfn "test0106 result: %s" result 

    let test0120 () =
//        let query = fun cl ->  List.length cl = 1
        // From Microsoft List.find<'T> Function (F#)
        let isDivisibleBy number elem = elem % number = 0
        let result = List.find (isDivisibleBy 5) [ 1 .. 100 ]
        printfn "%d " result

    let test0121 () =
        let formulaString =  "(q \/ r) /\ (~q \/ ~r) /\ (u \/ x) /\ (u \/ ~x) /\ (q \/ ~u) /\ (~r \/ ~u)"
        let formula = parse_prop_formula formulaString
        print_prop_formula formula
        printfn "%A" formula
        let cnf = defcnfs formula
        print_cnf cnf
        printfn "%A" cnf
        let query = fun cl ->  List.length cl = 1
        match List.tryFind query cnf  with
        | Some value -> printfn "%A " value
        | None -> printfn "No value found"

    let test0122 () =
        let formulaString =  "(q \/ r) /\ (~q \/ ~r) /\ (u \/ x) /\ (u \/ ~x) /\ (q \/ ~u) /\ (~r \/ ~u)"
        let formula = parse_prop_formula formulaString
        print_prop_formula formula
        let result = dptaut(formula)
        printfn "test0122 result: %b" result 

    let test0123 () =
        let formula = prime 11
        print_prop_formula formula
        let result = dptaut(formula)
        printfn "test0123 result: %b" result 

    let test0124 () =
        let result = dplitaut(prime 101)
        printfn "test0124 result: %b" result 

//    let test0130 () =
//        let pfun = (fun x -> x % 2 = 0)                 // Is divisable by 2
//        let even,odd = partition pfun [1 .. 10]         // use partition in lib.ml not F# 
//        printfn "odd: %A, even: %A" odd even

    let test0131 () =
        let pfun = (fun x -> x % 2 = 0)                 // Is divisable by 2
        let even,odd = List.partition pfun [1 .. 10]    // use partition in F# not lib.ml
        printfn "odd: %A, even: %A" odd even

    // TODO: Delete this once ebddtaut is working
    let test0132 () =
        let fm = prime 11
        let l,r = 
            try dest_nimp fm  with
            | Failure _ -> True,fm
//        printfn "l: %A" l
//        printfn "r: %A" r
        let con = conjuncts l
//        printfn "con: %A" con
        let rec dest_iffdef fm =
            match fm with
            | Iff(Atom(x),r) 
            | Iff(r,Atom(x)) -> x,r
            | _              -> failwith "not a defining equivalence"
        let parFun fm = 
            try 
                let result = dest_iffdef fm
                true
            with
            | Failure _ -> false
        let eqs,noneqs =  List.partition parFun con
//        printfn "eqs: %A" eqs
//        printfn "noneqs: %A" noneqs
        let defs = List.map dest_iffdef eqs
//        printfn "defs: %A" defs
        let fm1 = itlist mk_imp noneqs r
        printfn "fm1: %A" fm1
        let restore_iffdef (x,e) fm = 
            Imp(Iff(Atom(x),e),fm)
        let rev =
            let rec rev_append acc l =
                match l with
                | [] -> acc
                | h::t -> rev_append (h::acc) t
            fun l -> rev_append [] l
        let rec itlist f l b =
            match l with
            | []     -> b
            | (h::t) -> f h (itlist f t b)
        let rec sort_defs acc defs fm =
            try 
                let (x,e) = List.find (suitable_iffdef defs) defs
                let ps,nonps = List.partition (fun (x',_) -> x' = x) defs
                let ps' = subtract ps [x,e]
                sort_defs ((x,e)::acc) nonps (itlist restore_iffdef ps' fm)
            with 
            | Failure _ -> 
                    let newList = 
                        itlist restore_iffdef defs fm
                    printfn "acc:     %A" acc
                    printfn "newList: %A" newList
                    rev acc,newList
        let defs,fm' = sort_defs [] defs fm1
        printfn "defs: %A" defs
        printfn "fm': %A" fm'

    let test0140 () =
        let formulaString = "forall x y. exists x. x < x /\ y < z"
        let formula = parse formulaString
        print_fol_formula formula

    let test0141 () =
        // Note: | is removed by quotexpander in original version
        // i.e. "|2 * x|"  become "2 * x"
        let formulaString = "2 * x"
        let formula = parset formulaString
        printert formula

    let test0150 () =
        let formulaString = "exists x. forall y. P(x) ==> P(y)"
        let formula = parse formulaString
        gilmore formula

    let test0160 () = 
        let p45 = gilmore (parse "(forall x. P(x) 
            /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) 
            /\ ~(exists y. L(y) /\ R(y)) 
            /\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) 
            /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))")
        printfn "%A" p45

    let test0170 () =
        // let ( |> ) x f = f x
       let result = [1;2;3] |> List.map (fun x -> x * x * x)
       printfn "%A" result

    let test0171 () =
        // let ( >> ) f g x = g(f(x))
        let increment x = x + 1
        let square x = x * x
        let print x = printfn "The number is: %d" x
        let f = square >> increment >> print
        // (2 * 2) + 1 = 5
        f 2
        
    let test0172 () =
        // let ( << ) = fun f g x -> ???
        let increment x = x + 1
        let square x = x * x
        let print x = printfn "The number is: %d" x
        let f = print << increment << square
        // (2 * 2) + 1 = 5
        f 2
        
    let test0173 () =
        // let ( ** ) = fun f g x -> f(g x)
        let increment x = x + 1
        let square x = x * x
        let print x = printfn "The number is: %d" x
        let f = print >>|> increment >>|> square
        // (2 * 2) + 1 = 5
        f 2

    let test0180 () =
        print_fol_formula_list (function_congruence ("f",3))

    let test0190 () =
        TestSets001.test000 ()

    let test0191 () =
        TestSets001.test001 ()

    let test0192 () =
        TestSets001.test002 ()

    let test0193 () =
        TestSets001.test003 ()

    let test0194 () =
        TestSets001.test004 ()

    let test0200 () =
        TestSets001.test100 ()

    let test0201 () =
        TestSets001.test101 ()

    let test0202 () =
        TestSets001.test500 ()

    let test0203 () =
        TestSets001.test501 ()

    let test0204 () =
        TestSets001.test502 ()

    let test0205 () =
        TestSets001.test503 ()

    let test0206 () =
        TestSets001.test504 ()

    let test0300 () =
        TestSets002.tests ()
        
    let tests () =
        (*
//        test0001 ()
        test0002 ()
        test0003 ()
        test0004 ()
        test0005 ()
        test0006 ()
        test0007 ()
        test0008 ()
        test0009 ()
        test0010 ()
        test0011 ()
        test0012 ()
        test0013 ()
        test0014 ()
        test0015 ()
        test0016 ()
        test0017 ()
        test0018 ()
        test0019 ()
        test0020 ()
        test0021 ()
        test0022 ()
        test0023 ()
        test0024 ()
        test0025 ()
        test0026 ()
        test1002 ()
        test1003 ()
        test1004 ()
        test1005 ()
        test1006 ()
        test1007 ()
        test1008 ()
        test1009 ()
        test1010 ()
        test1011 ()
        test1012 ()
        test1013 ()
        test1014 () 
        test1015 ()
        test1016 ()
        test1017 ()
        test1018 ()
        test1019 ()
        test1020 ()
        test1021 ()
        test1022 ()
        test1023 ()
        test1024 ()
        test1025 ()
        test1026 ()
        test0030 ()
        test0031 ()
        test0032 ()
        test0040 ()
        test0041 ()
        test0042 ()
        test0043 ()
        test0044 ()
        test0045 ()
        test0046 ()
        test0047 ()
        test0050 ()
        test0051 ()
        test0052 ()
        test0053 ()
        test0054 ()
        test0055 ()
        test0056 ()
        test0057 ()
        test0058 ()
        test0059 ()
        test0060 ()
        test0061 ()
        test0062 ()
        test0063 ()
        test0064 ()
        test0065 ()
        test0066 ()
        test0067 ()
        test0068 ()
        test0069 ()
        test0070 ()
        test0071 ()
//        test0072 ()
        test0073 ()
        test0074 ()
        test0100 ()
        test0101 ()
        test0102 ()
        test0103 ()
        test0104 ()
        test0105 ()
        test0106 ()
        test0120 ()
        test0121 ()
        test0122 ()
        test0123 ()
        *)

//        test0124 ()   // Currently bogs down (and doesn't complete?) due to overhead of thrown exceptions in the parser
//        test0130 ()
        test0131 ()
//        test0132 ()   // Throws a KeyNotFoundException
        test0140 ()
        test0141 ()
//        test0150 ()
//        test0160 ()   // Throws a StackOverflowException
        test0170 ()
        test0171 ()
        test0172 ()
        test0173 ()
        test0180 ()
        test0190 ()
        test0191 ()
        test0192 ()
        test0193 ()
        test0194 ()
        test0200 ()
        test0201 ()
        test0202 ()
        test0203 ()
        test0204 ()
        test0205 ()
//        test0206 ()   // Test currently fails
//        test0300 ()   // Seems to get caught in an infinite loop

        pause ()

    tests ()  