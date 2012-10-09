// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module Reasoning.Automated.Harrison.Handbook.intro

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


(* TODO :   Maybe simplify this a bit by breaking 'simplifyImpl' into two mutually-recursive
            functions -- one with the simplification rules, and another with the recursive
            traversal rules. *)

//
let rec private simplify002Impl expr cont =
    match expr with
    | Mul (Const 0, x)
    | Mul (x, Const 0) ->
        cont <| Const 0
    | Add (Const 0, x)
    | Add (x, Const 0)
    | Mul (Const 1, x)
    | Mul (x, Const 1) ->
        cont x
    | Add (Const m, Const n) ->
        cont <| Const (m + n)
    | Mul (Const m, Const n) ->
        cont <| Const (m * n)

    (* Cases which need to be simplified recursively. *)
    | Add (e1, e2) ->
        // Try to simplify each of the sub-expressions.
        simplify002Impl e1 <| fun e1' ->
        simplify002Impl e2 <| fun e2' ->
        // Create a new Add using the (possibly) simplified sub-expressions,
        // then try to simplify it as well.
        simplify002Impl (Add (e1', e2')) <| fun expr' ->
            // Apply the now-simplified expression to the continuation to
            // continue simplifying any remaining parts of the complete expression
            // (i.e., the expression originally passed to 'simplify').
            cont expr'

    | Mul (e1, e2) ->
        simplify002Impl e1 <| fun e1' ->
        simplify002Impl e2 <| fun e2' ->
        simplify002Impl (Mul (e1', e2')) <| fun expr' ->
            cont expr'

    (* None of the remaining cases can be simplified. *)
    | _ ->
        cont expr

// OCaml: val simplify : expression -> expression = <fun>
// F#:    val simplify002 : expression -> expression
let simplify002 expr =
    simplify002Impl expr id

// pg. 17
// ------------------------------------------------------------------------- //
// Lexical analysis.                                                         //
// ------------------------------------------------------------------------- //

// OCaml: val matches : string -> string -> bool = <fun>
// F#:    val matches : string -> (string -> bool)
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
        
// OCaml: val space : string -> bool = <fun>
// F#:    val space : (string -> bool)
let space = matches " \t\n\r"

// OCaml: val punctuation : string -> bool = <fun>
// F#:    val punctuation : (string -> bool)
let punctuation = matches "()[]{},"

// OCaml: val symbolic : string -> bool = <fun>
// F#:    val symbolic : (string -> bool)
let symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"

// OCaml: val numeric : string -> bool = <fun>
// F#:    val numeric : (string -> bool)
let numeric = matches "0123456789"

// OCaml: val alphanumeric : string -> bool = <fun>
// F#:    val alphanumeric : (string -> bool)
let alphanumeric = matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

//
let rec private lexwhileImpl prop inp cont =
    match inp with
    | c :: cs when prop c ->
        lexwhileImpl prop cs <| fun (tok, rest) ->
            cont (c + tok, rest)
    | _ ->
        cont ("", inp)

// OCaml: val lexwhile : (string -> bool) -> string list -> string * string list = <fun>
// F#:    val lexwhile : (string -> bool) -> string list -> string * string list
let lexwhile prop inp =
    lexwhileImpl prop inp id

//
let rec private lexImpl inp cont =
    match snd <| lexwhile space inp with
    | [] ->
        cont []
    | c :: cs ->
        let toktl, rest =
            let prop =
                if alphanumeric c then alphanumeric
                else if symbolic c then symbolic
                else fun _ -> false                
            lexwhile prop cs

        lexImpl rest <| fun tail ->
            cont ((c + toktl) :: tail)

//
let lex inp =
    lexImpl inp id

// pg. 19
// ------------------------------------------------------------------------- //
// Parsing.                                                                  //
// ------------------------------------------------------------------------- //

// OCaml: val parse_expression : string list -> expression * string list = <fun>
// F#:    val parse_expression : string list -> expression * string list
let rec parse_expression i =
    parseExpressionImpl i id

and private parseExpressionImpl i cont =
    match parse_product i with
    | e1, "+" :: i1 ->
        parseExpressionImpl i1 <| fun (e2, i2) ->
            cont (Add (e1, e2), i2)
    | x ->
        cont x

// OCaml: val parse_product : string list -> expression * string list = <fun>
// F#:    val parse_product : string list -> expression * string list
and parse_product i =
    parseProductImpl i id

and private parseProductImpl i cont =
    match parse_atom i with
    | e1, "*" :: i1 ->
        parseProductImpl i1 <| fun (e2, i2) ->
            cont (Mul (e1, e2), i2)
    | x ->
        cont x

// OCaml: val parse_atom : string list -> expression * string list = <fun>
// F#:    val parse_atom : string list -> expression * string list
and parse_atom i =
    parseAtomImpl i id

and private parseAtomImpl i cont =
    match i with
    | [] ->
        failwith "Expected an expression at end of input"
    | "(" :: i1 ->
        match parse_expression i1 with
        | e2, ")" :: i2 ->
            cont (e2, i2)
        | _ -> failwith "Expected closing bracket"
    | tok :: i1 ->
        if List.forall numeric (explode tok) then
            Const (int tok), i1
        else Var tok, i1
        |> cont

// pg. 20
// ------------------------------------------------------------------------- //
// Generic function to impose lexing and exhaustion checking on a parser.    //
// ------------------------------------------------------------------------- //

// OCaml: val make_parser : (string list -> 'a * 'b list) -> string -> 'a = <fun>
// F#:    val make_parser : (string list -> 'a * 'b list) -> string -> 'a
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

let rec private stringOfExpImpl e cont =
    match e with
    | Var s ->
        cont s
    | Const n ->
        cont (string n)
    | Add (e1, e2) ->
        stringOfExpImpl e1 <| fun e1' ->
        stringOfExpImpl e2 <| fun e2' ->
            cont (sprintf "(%s + %s)" e1' e2')
    | Mul (e1, e2) ->
        stringOfExpImpl e1 <| fun e1' ->
        stringOfExpImpl e2 <| fun e2' ->
            cont (sprintf "(%s * %s)" e1' e2')

// OCaml: val string_of_exp : expression -> string = <fun>
// F#:    val string_of_exp : expression -> string
let string_of_exp e =
    stringOfExpImpl e id

// pg. 22
// ------------------------------------------------------------------------- //
// Somewhat better attempt.                                                  //
// ------------------------------------------------------------------------- //

let rec private stringOfExp2Impl pr e cont =
    match e with
    | Var s ->
        cont s
    | Const n ->
        cont (string n)
    | Add (e1, e2) ->
        stringOfExp2Impl 3 e1 <| fun e1' ->
        stringOfExp2Impl 2 e2 <| fun e2' ->
            let s = e1' + " + " + e2'
            cont <| if 2 < pr then "(" + s + ")" else s
    | Mul (e1, e2) ->
        stringOfExp2Impl 3 e1 <| fun e1' ->
        stringOfExp2Impl 2 e2 <| fun e2' ->
            let s = e1' + " * " + e2'
            cont <| if 2 < pr then "(" + s + ")" else s

// OCaml: val string_of_exp   : int -> expression -> string = <fun>
// F#:    val string_of_exp_2 : int -> expression -> string
let string_of_exp_2 pr e =
    stringOfExp2Impl pr e id

// OCaml: val print_exp : expression -> unit = <fun>
// F#:    val print_exp : expression -> unit
let print_exp e =
    printfn "%O" ("<<" + string_of_exp_2 0 e + ">>")