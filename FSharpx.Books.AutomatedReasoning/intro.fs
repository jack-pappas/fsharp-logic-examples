// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.intro

open System

// pg.14
// ========================================================================= //
// Simple algebraic expression example from the introductory chapter.        //
// ========================================================================= //

type expression =
    | Var of string
    | Const of int
    | Add of expression * expression
    | Mul of expression * expression

// pg. 15
// ------------------------------------------------------------------------- //
// Simplification example.                                                   //
// ------------------------------------------------------------------------- //

let simplify1 expr =
    match expr with
    | Mul (Const 0, x)
    | Mul (x, Const 0) ->
        Const 0
    | Add (Const 0, x)
    | Add (x, Const 0)        
    | Mul (Const 1, x)
    | Mul (x, Const 1) ->
        x
    | Add (Const m, Const n) ->
        Const (m + n)
    | Mul (Const m, Const n) ->
        Const (m * n)
    | _ -> expr

let rec simplify expr =
    match expr with
    | Add (e1, e2) ->
        Add (simplify e1, simplify e2)
        |> simplify1
    | Mul (e1, e2) ->
        Mul (simplify e1, simplify e2)
        |> simplify1
    | _ ->
        simplify1 expr

// pg. 17
// ------------------------------------------------------------------------- //
// Lexical analysis.                                                         //
// ------------------------------------------------------------------------- //

let matches str (c : string) =
    // Preconditions
    if String.length c > 1 then
        invalidArg "c" "The character string contains more than one (1) character."

    let len = String.length str
    let c' = char c

    let mutable idx = 0
    let mutable foundMatch = false
    while idx < len && not foundMatch do
        if str.[idx] = c' then
            foundMatch <- true
        idx <- idx + 1

    foundMatch
        
let space = matches " \t\n\r"

let punctuation = matches "()[]{},"

let symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"

let numeric = matches "0123456789"

let alphanumeric = matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

let rec lexwhile prop inp =
    match inp with
    | c :: cs when prop c ->
        let tok, rest = lexwhile prop cs
        c + tok, rest
    | _ -> "", inp

let rec lex inp =
    match snd <| lexwhile space inp with
    | [] -> []
    | c :: cs ->
        let prop =
            if alphanumeric c then alphanumeric
            else if symbolic c then symbolic
            else fun c -> false
        let toktl, rest = lexwhile prop cs
        (c + toktl) :: lex rest

// pg. 19
// ------------------------------------------------------------------------- //
// Parsing.                                                                  //
// ------------------------------------------------------------------------- //

let rec parse_expression i =
    match parse_product i with
    | e1, "+" :: i1 ->
        let e2, i2 = parse_expression i1
        Add (e1, e2), i2
    | x -> x

and parse_product i =
    match parse_atom i with
    | e1, "*" :: i1 ->
        let e2, i2 = parse_product i1
        Mul (e1, e2), i2
    | x -> x

and parse_atom i =
    match i with
    | [] ->
        failwith "Expected an expression at end of input"
    | "(" :: i1 ->
        match parse_expression i1 with
        | e2, ")" :: i2 -> e2, i2
        | _ -> failwith "Expected closing bracket"
    | tok :: i1 ->
        if List.forall numeric (explode tok) then
            Const (int tok), i1
        else Var tok, i1

// pg. 20
// ------------------------------------------------------------------------- //
// Generic function to impose lexing and exhaustion checking on a parser.    //
// ------------------------------------------------------------------------- //

let make_parser pfn (s : string) =
    let tokens =
        // Replace newlines with spaces so the lexer and parser
        // work correctly on multi-line strings.
        // TODO : This could probably be optimized to make the replacements
        // in a single pass using a Regex.
        s.Replace('\r', ' ')
            .Replace('\n', ' ')
        // Reduce multiple spaces to single spaces to help the parser.
            .Replace("  ", " ")
        |> explode
        |> lex

    match pfn tokens with
    | expr, [] ->
        expr
    | _, rest ->
        failwithf "Unparsed input: %i tokens remaining in buffer."
            <| List.length rest

let parse_exp =
    make_parser parse_expression
    
// pg. 21
// ------------------------------------------------------------------------- //
// Conservatively bracketing first attempt at printer.                       //
// ------------------------------------------------------------------------- //

let rec string_of_exp e =
    match e with
    | Var s -> s
    | Const n -> string n
    | Add (e1, e2) ->
        "(" + (string_of_exp e1) + " + " + (string_of_exp e2) + ")"
    | Mul (e1, e2) ->
        "(" + (string_of_exp e1) + " * " + (string_of_exp e2) + ")"

// pg. 22
// ------------------------------------------------------------------------- //
// Somewhat better attempt.                                                  //
// ------------------------------------------------------------------------- //

let rec string_of_exp_2 pr e =
    match e with
    | Var s -> s
    | Const n -> string n
    | Add (e1, e2) ->
        let s = (string_of_exp_2 3 e1) + " + " + (string_of_exp_2 2 e2)
        if 2 < pr then "(" + s + ")" 
        else s
    | Mul (e1, e2) ->
        let s = (string_of_exp_2 5 e1) + " * " + (string_of_exp_2 4 e2)
        if 4 < pr then "(" + s + ")" 
        else s

let print_exp e =
    printfn "%O" ("<<" + string_of_exp_2 0 e + ">>")

let sprint_exp e =
    "<<" + string_of_exp_2 0 e + ">>"