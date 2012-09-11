module TestSets002

// pg. 119
// ------------------------------------------------------------------------- //
// Terms.                                                                    //
// ------------------------------------------------------------------------- //

    type term = 
        | Var of string
        | Fn of string * term list

// ------------------------------------------------------------------------- //
// Polymorphic finite partial functions via Patricia trees.                  //
//                                                                           //
// The point of this strange representation is that it is canonical (equal   //
// functions have the same encoding) yet reasonably efficient on average.    //
//                                                                           //
// Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        //
// ------------------------------------------------------------------------- //
//

    // pg. 621
    type func<'a,'b> =
    | Empty
    | Leaf of int * ('a * 'b) list
    | Branch of int * int * func<'a,'b> * func<'a,'b>

// ------------------------------------------------------------------------- //
// Undefined function.                                                       //
// ------------------------------------------------------------------------- //

    // pg. 621
    let undefined = Empty

// ------------------------------------------------------------------------- //
// Application.                                                              //
// ------------------------------------------------------------------------- //

    // pg. 621
    let applyd =
        let rec apply_listd l d x =
            match l with
            | (a,b)::t -> 
                let c = compare x a
                if c = 0   then b 
                elif c > 0 then apply_listd t d x 
                else            d x
            | []             -> d x
        fun f d x ->
//            let k = Pervasives.hash x           // TODO: Change this so that it does not use Pervasives
            let k = hash x           // TODO: Change this so that it does not use Pervasives
            let rec look t =
                match t with
                | Leaf(h,l) when h = k                           -> apply_listd l d x
                | Branch(p,b,l,r) when (k ^^^ p) &&& (b - 1) = 0 -> look (if k &&& b = 0 then l else r)
                | _                                              -> d x
            look f

    // pg. 621
    let apply f = applyd f (fun x -> failwith "apply")

    // pg. 621
    let tryapplyd f a d = applyd f (fun x -> d) a

//    // pg. 621
//    let tryapplyl f x = tryapplyd f x []
    
    // pg. 621
    let defined f x =
        try 
            apply f x |> ignore
            true 
        with 
        | Failure _ -> false

// ------------------------------------------------------------------------- //
// Redefinition and combination.                                             //
// ------------------------------------------------------------------------- //

    // Finite Partial Functions (FPF)
    // To update the FPF with a new mapping from x to y.
    // pg. 621
    let (|->),combine =
      let newbranch p1 t1 p2 t2 =
        let zp = p1 ^^^ p2
        let b = zp &&& (-zp)
        let p = p1 &&& (b - 1)
        if p1 &&& b = 0 then Branch(p,b,t1,t2)
        else Branch(p,b,t2,t1)

      let rec define_list (x,y as xy) l =
        match l with
        | (a,b as ab)::t ->
              let c = compare x a
              if c = 0 then xy::t
              elif c < 0 then xy::l
              else ab::(define_list xy t)
        | [] -> [xy]
      and combine_list op z l1 l2 =
        match (l1,l2) with
        | [],_ -> l2
        | _,[] -> l1
        | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
              let c = compare x1 x2
              if c < 0 then xy1::(combine_list op z t1 l2)
              elif c > 0 then xy2::(combine_list op z l1 t2) 
              else
                  let y = op y1 y2 
                  let l = combine_list op z t1 t2
                  if z(y) then l 
                  else (x1,y)::l

      let (|->) x y =
        let k = hash x
        let rec upd t =
          match t with
          | Empty -> Leaf (k,[x,y])
          | Leaf(h,l) ->
               if h = k then Leaf(h,define_list (x,y) l)
               else newbranch h t k (Leaf(k,[x,y]))
          | Branch(p,b,l,r) ->
              if k &&& (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
              elif k &&& b = 0 then Branch(p,b,upd l,r)
              else Branch(p,b,l,upd r)
        upd

      let rec combine op z t1 t2 =
        match (t1,t2) with
        | Empty,_ -> t2
        | _,Empty -> t1
        | Leaf(h1,l1),Leaf(h2,l2) ->
            if h1 = h2 then
                let l = combine_list op z l1 l2
                if l = [] then Empty 
                else Leaf(h1,l)
            else newbranch h1 t1 h2 t2
        | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
              if k &&& (b - 1) = p then
                if k &&& b = 0 then (
                   match combine op z lf l with
                   | Empty -> r 
                   | l' -> Branch(p,b,l',r))
                else (
                   match combine op z lf r with
                    | Empty -> l 
                    | r' -> Branch(p,b,l,r'))
              else
                newbranch k lf p br
        | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
              if k &&& (b - 1) = p then
                if k &&& b = 0 then (
                   match combine op z l lf with
                   | Empty -> r 
                   | l' -> Branch(p,b,l',r))
                else (
                   match combine op z r lf with
                   | Empty -> l 
                   | r' -> Branch(p,b,l,r'))
              else
                newbranch p br k lf
        | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
              if b1 < b2 then
                if p2 &&& (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
                elif p2 &&& b1 = 0 then (
                   match combine op z l1 t2 with
                   | Empty -> r1 
                   | l -> Branch(p1,b1,l,r1))
                else (
                   match combine op z r1 t2 with
                   | Empty -> l1 
                   | r -> Branch(p1,b1,l1,r))
              elif b2 < b1 then
                if p1 &&& (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
                elif p1 &&& b2 = 0 then (
                   match combine op z t1 l2 with
                   | Empty -> r2 
                   | l -> Branch(p2,b2,l,r2))
                else (
                   match combine op z t1 r2 with
                   | Empty -> l2 
                   | r -> Branch(p2,b2,l2,r))
              elif p1 = p2 then (
                match (combine op z l1 l2,combine op z r1 r2) with
                | (Empty,r) -> r 
                | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
              else
                newbranch p1 t1 p2 t2
      (|->),combine

// ------------------------------------------------------------------------- //
// List membership. This does *not* assume the list is a set.                //
// ------------------------------------------------------------------------- //

    // pg. 619
    // use List.head
    let hd l =
        match l with
        | h::t -> h
        | _ -> failwith "hd"
        
    // pg. 619
    // use List.tail
    let tl l =
        match l with
        | h::t -> t
        | _ -> failwith "tl"

    // pg. 619 - list iterator
    // f - accumulator function
    // l - list
    // b - initial value
    let rec itlist f l b =
        match l with
        | []     -> b
        | (h::t) -> f h (itlist f t b)
        
    // pg. 619
    // use List.zip
    let rec zip l1 l2 =
        match (l1,l2) with
        | ([],[])         -> []
        | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
        | _               -> failwith "zip"

    // pg. 619
    // Use List.forall
    let rec forall p l =
        match l with
        | []   -> true
        | h::t -> p(h) && forall p t
        
    // pg. 619
    // Use List.exists
    let rec exists p l =
        match l with
        | [] -> false
        | h::t -> p(h) || exists p t
    
    // pg. 619
    // Use List.length
    let length =
        let rec len k l =
            if l = [] then k else len (k + 1) (List.tail l)
        fun l -> len 0 l

    // pg. 619
    // Use List.map
    let map f =
        let rec mapf l =
            match l with
            | []     -> []
            | (x::t) -> let y = f x in y::(mapf t)
        mapf

// ------------------------------------------------------------------------- //
// Application of (presumably imperative) function over a list.              //
// ------------------------------------------------------------------------- //

    // pg. 619
    let rec do_list f l =
        match l with
        | []   -> ()
        | h::t -> f(h); do_list f t

// ------------------------------------------------------------------------- //
// List membership. This does *not* assume the list is a set.                //
// ------------------------------------------------------------------------- //

    // pg. 620
    let rec mem x lis =
        match lis with
        | []     -> false
        | (h::t) -> (compare x h = 0) || (mem x t)

// pg. 629
// ------------------------------------------------------------------------- //
// Printing of terms.                                                        //
// ------------------------------------------------------------------------- //

    let rec print_term prec fm =
        match fm with
        | Var x -> printf "%s" x
        | Fn("^",[tm1;tm2]) -> print_infix_term true prec 24 "^" tm1 tm2
        | Fn("/",[tm1;tm2]) -> print_infix_term true prec 22 " /" tm1 tm2
        | Fn("*",[tm1;tm2]) -> print_infix_term false prec 20 " *" tm1 tm2
        | Fn("-",[tm1;tm2]) -> print_infix_term true prec 18 " -" tm1 tm2
        | Fn("+",[tm1;tm2]) -> print_infix_term false prec 16 " +" tm1 tm2
        | Fn("::",[tm1;tm2]) -> print_infix_term false prec 14 "::" tm1 tm2
        | Fn(f,args) -> print_fargs f args

    and print_fargs f args =
        printf "%s" f
        if args = [] then () else
        (printf "(";
//        open_box 0;
        print_term 0 (List.head args); 
//        print_break 0 0;
        do_list (
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

// ------------------------------------------------------------------------- //
// Install a (trivial) printer for finite partial functions.                 //
// ------------------------------------------------------------------------- //

    // pg. ???
//    let print_fpf (f:func<'a,'b>) = printf "<func>"
//    let print_fpf (f: ('a,'b)func ) = printf "<func>"

    let rec print_fpf_list l =
        match l with
        | (a,b)::t -> 
            printf "fpf key: %A " a;
            printf "fpf value: ";
//            print_term 0 b;
            printf "value: %A " b;
            print_fpf_list t
        | [] -> ()

    let rec print_fpf (f:func<'a,'b>) = 
      match f with
      | Empty -> printf "Empty"
      | Leaf(h,l) -> 
          Printf.printf "Leaf: %i " h;
          print_fpf_list l
      | Branch(p,b,l,r) ->
          Printf.printf "Branch: p: %i, b: %i " p b;
          Printf.printf "\n";
          print_fpf l;
          Printf.printf "\n";
          print_fpf r;
          Printf.printf "\n"
      
    let rec print_terms ts =
       match ts with
       | (a,b)::t -> 
           printf "%s" "        a: "; print_term 0 a; printf "%s" "\n        b: "; print_term 0 b; printf "%s" "\n";
           print_terms t
       | [] -> ()

// pg. 187
// ------------------------------------------------------------------------- //
// Matching of terms and literals.                                           //
// ------------------------------------------------------------------------- //

//    let rec term_match env eqs =
//        match eqs with
//        | (Fn(f,fa),Fn(g,ga))::oth when f = g && List.length fa = List.length ga ->
//            term_match env (List.zip fa ga @ oth)
//        | (Var x,t)::oth ->
//            if not (defined env x) then term_match ((x |-> t) env) oth
//            elif apply env x = t then term_match env oth
//            else failwith "term_match"
//        | _ -> failwith "term_match"

    let term_level_ref = ref 0

    let rec term_match env eqs =
        term_level_ref := term_level_ref.contents + 1;
        printf "%s" "Enter: term_match - level: "; printf "%d" (term_level_ref.contents); printf "%s" "\n";
        printf "%s" "  env: "; print_fpf env; printf "%s" "\n";
        printf "%s" "  eqs: \n"; print_terms eqs;
        let result = 
            match eqs with
            | [] -> 
                printf "%s" "  term_match: option 1 - Empty \n";
                env
            | (Fn(f,fa),Fn(g,ga))::oth when f = g && length fa = length ga ->
                printf "%s" "  term_match: option 2 - Function\n";
                term_match env (zip fa ga @ oth)
            | (Var x,t)::oth ->
                printf "%s" "  term_match: option 3 - Var\n";
                if not (defined env x) then term_match ((x |-> t) env) oth
                else if apply env x = t then term_match env oth
                else failwith "fail: term_match"
            | _ -> 
                printf "%s" "  term_match: option 4 - fail\n";
                printf "%s" "Exit: term_match - level: "; printf "%d" (term_level_ref.contents); printf "%s" "\n";
                term_level_ref := term_level_ref.contents - 1;
                failwith "term_match"
        printf "%s" "  result: "; print_fpf result; printf "%s" "\n";
        printf "%s" "Exit: term_match - level: "; printf "%d" (term_level_ref.contents); printf "%s" "\n";
        term_level_ref := term_level_ref.contents - 1;
        result;;

// pg. 119
// ------------------------------------------------------------------------- //
// Abbreviation for FOL formula.                                             //
// ------------------------------------------------------------------------- //

    type fol = R of string * term list

// pg. 26
// ========================================================================= //
// Polymorphic type of formulas with parser and printer.                     //
//                                                                           //
// Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  //
// ========================================================================= //

    type ('a)formula = 
        | False
        | True
        | Atom   of 'a
        | Not    of ('a)formula
        | And    of ('a)formula * ('a)formula
        | Or     of ('a)formula * ('a)formula
        | Imp    of ('a)formula * ('a)formula
        | Iff    of ('a)formula * ('a)formula
        | Forall of string * ('a)formula
        | Exists of string * ('a)formula

// pg. 131
// ------------------------------------------------------------------------- //
// Substitution within terms.                                                //
// ------------------------------------------------------------------------- //

    let rec tsubst sfn tm =
        match tm with
        | Var x      -> tryapplyd sfn x tm
        | Fn(f,args) -> Fn(f,List.map (tsubst sfn) args)

// pg. 619
// ------------------------------------------------------------------------- //
// Explosion and implosion of strings.                                       //
// ------------------------------------------------------------------------- //

    // pg. 619
    let explode (s : string) =
        let rec exap n l =
            if n < 0 then l
            else exap (n - 1) ((s.Substring(n,1))::l)
        exap ((String.length s) - 1) []
        
    // pg. 619
    let implode l = itlist (+) l ""

// pg. 17
// ------------------------------------------------------------------------- //
// Lexical analysis.                                                         //
// ------------------------------------------------------------------------- //

// Note: explode and mem are defined in the lib module

    let matches s = 
        let chars = explode s
        fun c -> mem c chars

    let space = matches " \t\n\r"
    let punctuation = matches "()[]{},"
    let symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"
    let numeric = matches "0123456789"
    let alphanumeric = matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

    let rec lexwhile prop inp =
        match inp with
        | c::cs when prop c -> 
            let tok,rest = lexwhile prop cs
            c+tok,rest
        | _ -> "",inp

    let rec lex inp =
        match snd(lexwhile space inp) with
        | []    -> []
        | c::cs -> 
            let prop = 
                if alphanumeric(c) then alphanumeric
                else if symbolic(c) then symbolic
                else fun c -> false
            let toktl,rest = lexwhile prop cs
            (c+toktl)::lex rest

// pg. 623
// ------------------------------------------------------------------------- //
// General parsing of iterated infixes.                                      //
// ------------------------------------------------------------------------- //

    let rec parse_ginfix opsym opupdate sof subparser inp =
        let e1,inp1 = subparser inp
        if (inp1 <> []) && (List.head inp1 = opsym) then parse_ginfix opsym opupdate (opupdate sof e1) subparser (List.tail inp1)
        else sof e1,inp1

    let parse_left_infix opsym opcon =
        parse_ginfix opsym (fun f e1 e2 -> opcon(f e1,e2)) (fun x -> x)

    let parse_right_infix opsym opcon =
        parse_ginfix opsym (fun f e1 e2 -> f(opcon(e1,e2))) (fun x -> x)

    let parse_list opsym =
        parse_ginfix opsym (fun f e1 e2 -> (f e1)@[e2]) (fun x -> [x])

// pg. 624
// ------------------------------------------------------------------------- //
// Other general parsing combinators.                                        //
// ------------------------------------------------------------------------- //

    let papply f (ast,rest) = 
        (f ast,rest)

    let nextin inp tok = 
        (inp <> []) && (List.head inp = tok)

    let parse_bracketed subparser cbra inp =
        let ast,rest = subparser inp
        if nextin rest cbra then ast,List.tail rest
        else failwith "Closing bracket expected"

// pg. 625
// ------------------------------------------------------------------------- //
// Parsing of formulas, parametrized by atom parser "pfn".                   //
// ------------------------------------------------------------------------- //

    let rec parse_atomic_formula (ifn,afn) vs inp =
        match inp with
        | []                                    -> failwith "formula expected"
        | "false"::rest                         -> False,rest
        | "true"::rest                          -> True,rest
        | "("::rest -> 
            (try ifn vs inp with Failure _      -> parse_bracketed (parse_formula (ifn,afn) vs) ")" rest)
        | "~"::rest                             -> papply (fun p -> Not p) (parse_atomic_formula (ifn,afn) vs rest)
        | "forall"::x::rest                     -> parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Forall(x,p)) x rest
        | "exists"::x::rest                     -> parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Exists(x,p)) x rest
        | _                                     -> afn vs inp

    and parse_quant (ifn,afn) vs qcon x inp =
        match inp with
        | []      -> failwith "Body of quantified term expected"
        | y::rest -> papply (fun fm -> qcon(x,fm)) (if y = "." then parse_formula (ifn,afn) vs rest else parse_quant (ifn,afn) (y::vs) qcon y rest)

    and parse_formula (ifn,afn) vs inp =
        parse_right_infix "<=>" (fun (p,q) -> Iff(p,q))
            (parse_right_infix "==>" (fun (p,q) -> Imp(p,q))
                (parse_right_infix "\\/" (fun (p,q) -> Or(p,q))
                    (parse_right_infix "/\\" (fun (p,q) -> And(p,q))
                        (parse_atomic_formula (ifn,afn) vs)))) inp

// pg. 20
// ------------------------------------------------------------------------- //
// Generic function to impose lexing and exhaustion checking on a parser.    //
// ------------------------------------------------------------------------- //

    let make_parser pfn s =
        let expr,rest = 
            pfn (lex(explode s)) in
        match rest with
        | [] -> expr
        | _  -> failwith "Unparsed input"

// pg. 628
// ------------------------------------------------------------------------- //
// Parsing of terms.                                                         //
// ------------------------------------------------------------------------- //

    let is_const_name s = List.forall numeric (explode s) || s = "nil"

    let rec parse_atomic_term vs inp =
        match inp with
        | [] -> failwith "term expected"
        | "("::rest -> parse_bracketed (parse_term vs) ")" rest
        | "-"::rest -> papply (fun t -> Fn("-",[t])) (parse_atomic_term vs rest)
        | f::"("::")"::rest -> Fn(f,[]),rest
        | f::"("::rest ->
            papply (fun args -> Fn(f,args))
                    (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
        | a::rest ->
            (if is_const_name a && not(mem a vs) then Fn(a,[]) else Var a),rest

    and parse_term vs inp =
        parse_right_infix "::" (fun (e1,e2) -> Fn("::",[e1;e2]))
            (parse_right_infix "+" (fun (e1,e2) -> Fn("+",[e1;e2]))
                (parse_left_infix "-" (fun (e1,e2) -> Fn("-",[e1;e2]))
                    (parse_right_infix "*" (fun (e1,e2) -> Fn("*",[e1;e2]))
                        (parse_left_infix "/" (fun (e1,e2) -> Fn("/",[e1;e2]))
                        (parse_left_infix "^" (fun (e1,e2) -> Fn("^",[e1;e2]))
                            (parse_atomic_term vs)))))) inp

    let parset = make_parser (parse_term [])

// pg. 628
// ------------------------------------------------------------------------- //
// Parsing of formulas.                                                      //
// ------------------------------------------------------------------------- //

    let parse_infix_atom vs inp =       
        let tm,rest = parse_term vs inp in
        if List.exists (nextin rest) ["="; "<"; "<="; ">"; ">="] then                     
            papply (fun tm' -> Atom(R(List.head rest,[tm;tm'])))                          
                    (parse_term vs (List.tail rest))                                       
        else failwith ""
                                                               
    let parse_atom vs inp =
        try parse_infix_atom vs inp with Failure _ ->                                
        match inp with                                                               
        | p::"("::")"::rest -> Atom(R(p,[])),rest                                    
        | p::"("::rest ->
            papply (fun args -> Atom(R(p,args)))
                    (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
        | p::rest when p <> "(" -> Atom(R(p,[])),rest
        | _ -> failwith "parse_atom"
                                                                               
    let parse = make_parser (parse_formula (parse_infix_atom,parse_atom) [])  

// pg. 262
// ------------------------------------------------------------------------- //
// Rewriting at the top level with first of list of equations.               //
// ------------------------------------------------------------------------- //

    let rec rewrite1 eqs t =
        match eqs with
        | Atom(R("=",[l;r]))::oeqs ->
            try tsubst (term_match undefined [l,t]) r with 
            | Failure _ -> rewrite1 oeqs t
        | _ -> failwith "rewrite1"

// pg. 263
// ------------------------------------------------------------------------- //
// Rewriting repeatedly and at depth (top-down).                             //
// ------------------------------------------------------------------------- //

    let rec rewrite eqs tm =
        try rewrite eqs (rewrite1 eqs tm) with 
        | Failure _ ->
            match tm with
            | Var x -> tm
            | Fn(f,args) -> 
                let tm' = Fn(f,List.map (rewrite eqs) args)
                if tm' = tm then tm 
                else rewrite eqs tm'

//
// pg. 263
// ------------------------------------------------------------------------- //
// Example: 3 * 2 + 4 in successor notation.                                 //
// ------------------------------------------------------------------------- //

    let test001 () = 
        let result = rewrite [(parse "0 + x = x"); (parse "S(x) + y = S(x + y)"); (parse "0 * x = 0"); (parse "S(x) * y = y + x * y")] (parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))");
        printfn "%A" result

    let test002 () =
        printfn "%s" "test002"
        let eq1 = parse "0 + x = x"
        let eq2 = parse "S(x) + y = S(x + y)"
        let eq3 = parse "0 * x = 0"
        let eq4 = parse "S(x) * y = y + x * y"
        let tm1 = parset "S(S(S(0))) * S(S(0)) + S(S(S(S(0))))"
        let result = rewrite [eq1; eq2; eq3; eq4] tm1
        printfn "%A" result

    let tests () =
        test001 ()
        test002 ()