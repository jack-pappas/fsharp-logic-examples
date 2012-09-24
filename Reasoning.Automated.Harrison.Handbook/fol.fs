// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

namespace Reasoning.Automated.Harrison.Handbook

module folMod =
    open intro
    open formulas

// ========================================================================= //
// Basic stuff for first order logic.                                        //
// ========================================================================= //

// pg. 119
// ------------------------------------------------------------------------- //
// Terms.                                                                    //
// ------------------------------------------------------------------------- //

    type term = 
        | Var of string
        | Fn of string * term list

// pg. 119
// ------------------------------------------------------------------------- //
// Abbreviation for FOL formula.                                             //
// ------------------------------------------------------------------------- //

    type fol = R of string * term list

// pg. ???
// ------------------------------------------------------------------------- //
// Special case of applying a subfunction to the top *terms*.                //
// ------------------------------------------------------------------------- //

    let onformula f =
        onatoms <| fun (R (p, a)) ->
            Atom (R (p, List.map f a))

// pg. 628
// ------------------------------------------------------------------------- //
// Parsing of terms.                                                         //
// ------------------------------------------------------------------------- //

    let is_const_name s =
        s = "nil"
        || List.forall numeric (explode s)

    let rec parse_atomic_term vs inp =
        match inp with
        | [] -> failwith "term expected"
        | "(" :: rest ->
            parse_bracketed (parse_term vs) ")" rest
        | "-" :: rest ->
            parse_atomic_term vs rest
            |> papply (fun t -> Fn ("-", [t]))
        | f :: "(" :: ")" :: rest ->
            Fn (f, []), rest
        | f :: "(" :: rest ->
            parse_bracketed (parse_list "," (parse_term vs)) ")" rest
            |> papply (fun args -> Fn (f, args))
        | a :: rest ->
            (if is_const_name a && not (mem a vs) then Fn (a, []) else Var a), rest

    and parse_term vs inp =
        parse_right_infix "::" (fun (e1,e2) -> Fn ("::",[e1;e2]))
            (parse_right_infix "+" (fun (e1,e2) -> Fn ("+",[e1;e2]))
                (parse_left_infix "-" (fun (e1,e2) -> Fn ("-",[e1;e2]))
                    (parse_right_infix "*" (fun (e1,e2) -> Fn ("*",[e1;e2]))
                        (parse_left_infix "/" (fun (e1,e2) -> Fn ("/",[e1;e2]))
                        (parse_left_infix "^" (fun (e1,e2) -> Fn ("^",[e1;e2]))
                            (parse_atomic_term vs)))))) inp

    let parset = make_parser (parse_term [])

// pg. 628
// ------------------------------------------------------------------------- //
// Parsing of formulas.                                                      //
// ------------------------------------------------------------------------- //

    let parse_infix_atom vs inp =
        let tm, rest = parse_term vs inp
        if List.exists (nextin rest) ["="; "<"; "<="; ">"; ">="] then
            papply (fun tm' -> Atom (R (List.head rest, [tm; tm'])))
                    (parse_term vs (List.tail rest))
        else failwith ""

    let parse_atom vs inp =
        try parse_infix_atom vs inp
        with _ ->
        match inp with
        | p :: "(" :: ")" :: rest ->
            Atom (R (p, [])), rest
        | p :: "(" :: rest ->
            parse_bracketed (parse_list "," (parse_term vs)) ")" rest
            |> papply (fun args -> Atom (R (p, args)))
        | p::rest when p <> "(" ->
            Atom (R (p, [])), rest
        | _ -> failwith "parse_atom"

    let parse =
        parse_formula (parse_infix_atom, parse_atom) []
        |> make_parser

// pg. 629
// ------------------------------------------------------------------------- //
// Set up parsing of quotations.                                             //
// ------------------------------------------------------------------------- //

    let default_parser = parse

    let secondary_parser = parset

// pg. 629
// ------------------------------------------------------------------------- //
// Printing of terms.                                                        //
// ------------------------------------------------------------------------- //

    let rec print_term prec fm =
        match fm with
        | Var x ->
            printf "%s" x
        | Fn ("^", [tm1; tm2;]) ->
            print_infix_term true prec 24 "^" tm1 tm2
        | Fn ("/", [tm1; tm2;]) ->
            print_infix_term true prec 22 " /" tm1 tm2
        | Fn ("*", [tm1; tm2;]) ->
            print_infix_term false prec 20 " *" tm1 tm2
        | Fn ("-", [tm1; tm2;]) ->
            print_infix_term true prec 18 " -" tm1 tm2
        | Fn ("+", [tm1; tm2;]) ->
            print_infix_term false prec 16 " +" tm1 tm2
        | Fn ("::", [tm1; tm2;]) ->
            print_infix_term false prec 14 "::" tm1 tm2
        | Fn (f, args) ->
            print_fargs f args

    and print_fargs f args =
        printf "%s" f
        if args = [] then () else
        (printf "(";
//        open_box 0;
        print_term 0 (List.head args); 
//        print_break 0 0;
        List.iter (
                  fun t -> 
                    printf ","
    //                print_break 0 0;
                    print_term 0 t)
            (List.tail args);
//        close_box();
        printf ")")

    and print_infix_term isleft oldprec newprec sym p q =
        if oldprec > newprec then 
            printf "(";
//             open_box 0
        else ();
        print_term (if isleft then newprec else newprec+1) p;
        printf "%s" sym;
//        print_break (if String.sub sym 0 1 = " " then 1 else 0) 0;
        print_term (if isleft then newprec+1 else newprec) q;
        if oldprec > newprec then 
//            close_box()
            printf ")"
        else ()

    let printert tm =
//        open_box 0; 
        printf "<<|";
//        open_box 0; 
        print_term 0 tm; 
//        close_box();
        printf "|>>"; 
//        close_box()

    // Added by EGT
    let rec print_term_list x =
        match x with
        | []   -> ()
        | h::t -> 
            print_term 0 h
            print_term_list t

//#install_printer printert
//
// pg. 630
// ------------------------------------------------------------------------- //
// Printing of formulas.                                                     //
// ------------------------------------------------------------------------- //

    let print_atom prec (R(p,args)) : unit =
        if mem p ["="; "<"; "<="; ">"; ">="] && List.length args = 2
        then print_infix_term false 12 12 (" " + p) (List.nth args 0) (List.nth args 1)
        else print_fargs p args

    let print_fol_formula =
        print_qformula print_atom

    // Added by EGT
    let rec print_fol_formula_list x =
        match x with
        | [] -> ()
        | h :: t -> 
            print_qformula print_atom h
            print_fol_formula_list t
        
// pg. 125
// ------------------------------------------------------------------------- //
// Semantics, implemented of course for finite domains only.                 //
// ------------------------------------------------------------------------- //

    let rec termval (domain,func,pred as m) v tm =
        match tm with
        | Var x ->
            apply v x
        | Fn (f, args) ->
            func f (List.map (termval m v) args)

    let rec holds (domain,func,pred as m) v fm =
        match fm with
        | False -> false
        | True -> true
        | Atom (R (r, args)) ->
            pred r (List.map (termval m v) args)
        | Not p ->
            not(holds m v p)
        | And (p, q) ->
            (holds m v p) && (holds m v q)
        | Or (p, q) ->
            (holds m v p) || (holds m v q)
        | Imp (p, q) ->
            not(holds m v p) || (holds m v q)
        | Iff (p, q) ->
            (holds m v p = holds m v q)
        | Forall (x, p) ->
            List.forall (fun a -> holds m ((x |-> a) v) p) domain
        | Exists (x, p) ->
            List.exists (fun a -> holds m ((x |-> a) v) p) domain

// pg. 125
// ------------------------------------------------------------------------- //
// Examples of particular interpretations.                                   //
// ------------------------------------------------------------------------- //

    let bool_interp =
        let func f args =
            match f, args with
            | "0", [] -> false
            | "1", [] -> true
            | "+", [x; y] -> not (x = y)
            | "*", [x; y] -> x && y
            | _ -> failwith "uninterpreted function"

        let pred p args =
            match p, args with
            | "=", [x; y] -> x = y
            | _ -> failwith "uninterpreted predicate"

        [false; true], func, pred

    let mod_interp n =
        let func f args =
            match f, args with
            | "0", [] -> 0
            | "1", [] -> 1 % n
            | "+", [x; y] -> (x + y) % n
            | "*", [x; y] -> (x * y) % n
            | _ -> failwith "uninterpreted function"

        let pred p args =
            match p, args with
            | "=", [x; y] -> x = y
            | _ -> failwith "uninterpreted predicate"

        0 -- (n-1), func, pred

// pg. 127
// ------------------------------------------------------------------------- //
// Free variables in terms and formulas.                                     //
// ------------------------------------------------------------------------- //

    let rec fvt tm =
        match tm with
        | Var x -> [x]
        | Fn (f, args) ->
            unions <| List.map fvt args

    let rec var fm =
        match fm with
        | False
        | True -> []
        | Atom (R (p, args)) ->
            unions (List.map fvt args)
        | Not p ->
            var p
        | And (p, q)
        | Or (p, q)
        | Imp (p, q)
        | Iff (p, q) ->
            union (var p) (var q)
        | Forall(x, p)
        | Exists(x, p) ->
            insert x (var p)

    let rec fv fm =
        match fm with
        | False
        | True -> []
        | Atom (R (p, args)) ->
            unions (List.map fvt args)
        | Not p ->
            fv p
        | And (p, q)
        | Or (p, q)
        | Imp (p, q)
        | Iff (p, q) ->
            union (fv p) (fv q)
        | Forall (x, p)
        | Exists (x, p) ->
            subtract (fv p) [x]

// pg. 131
// ------------------------------------------------------------------------- //
// Universal closure of a formula.                                           //
// ------------------------------------------------------------------------- //

    let generalize fm =
        List.foldBack mk_forall (fv fm) fm

// pg. 131
// ------------------------------------------------------------------------- //
// Substitution within terms.                                                //
// ------------------------------------------------------------------------- //

    let rec tsubst sfn tm =
        match tm with
        | Var x ->
            tryapplyd sfn x tm
        | Fn (f, args) ->
            Fn (f, List.map (tsubst sfn) args)

// pg. 133
// ------------------------------------------------------------------------- //
// Variant function and examples.                                            //
// ------------------------------------------------------------------------- //

    let rec variant x vars =
        if mem x vars then
            variant (x + "'") vars 
        else x

// pg. 134
// ------------------------------------------------------------------------- //
// Substitution in formulas, with variable renaming.                         //
// ------------------------------------------------------------------------- //
    
    // TODO : Optimize using continuation-passing style.
    let rec subst subfn fm =
        match fm with
        | False -> False
        | True -> True
        | Atom (R (p, args)) ->
            Atom (R (p, List.map (tsubst subfn) args))
        | Not p ->
            Not (subst subfn p)
        | And (p, q) ->
            And (subst subfn p, subst subfn q)
        | Or (p, q) ->
            Or (subst subfn p, subst subfn q)
        | Imp (p, q) ->
            Imp (subst subfn p, subst subfn q)
        | Iff (p, q) ->
            Iff (subst subfn p, subst subfn q)
        | Forall (x, p) ->
            substq subfn mk_forall x p
        | Exists (x, p) ->
            substq subfn mk_exists x p

    and substq subfn quant x p =
        let x' = 
            if List.exists (fun y -> mem x (fvt (tryapplyd subfn y (Var y)))) (subtract (fv p) [x])
                then variant x (fv (subst (undefine x subfn) p)) 
                else x
        quant x' (subst ((x |-> Var x') subfn) p)

