// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

module FSharpx.Books.AutomatedReasoning.limitations

open LanguagePrimitives
open FSharpx.Compatibility.OCaml.Num

open lib
open intro
open formulas
open prop
open defcnf
open dp
open stal
open bdd
open fol
open skolem
open herbrand
open unif
open tableaux
open resolution
open prolog
open meson
open skolems
open equal
open cong
open rewrite
open order
open completion
open eqelim
open paramodulation
open decidable
open qelim
open cooper
open complex
open real
open grobner
open geom
open interpolation
open combining
open lcf
open lcfprop
open folderived
open lcffol
open tactics

// ========================================================================= //
// Goedel's theorem and relatives.                                           //
// ========================================================================= //

// pg. 530
// ------------------------------------------------------------------------- //
// Produce numeral in zero-successor form.                                   //
// ------------------------------------------------------------------------- //

let rec numeral n =
    if n = GenericZero then Fn ("0", [])
    else Fn ("S", [numeral (n - Int 1)])
        
// pg. 532
// ------------------------------------------------------------------------- //
// Map strings to numbers. This is bijective, to avoid certain quibbles.     //
// ------------------------------------------------------------------------- //

let number (s : string) =
    List.foldBack (fun i g ->
        Int (1 + int (char s.[i])) + (Int 256) * g) (0 -- (String.length s - 1)) (Int 0)
            
// pg. 532
// ------------------------------------------------------------------------- //
// Injective pairing function with "pair x y" always nonzero.                //
// ------------------------------------------------------------------------- //

let pair x y =
    (x + y) * (x + y) + x + Int 1
        
// pg. 533
// ------------------------------------------------------------------------- //
// Goedel numbering of terms and formulas.                                   //
// ------------------------------------------------------------------------- //

let rec gterm tm =
    match tm with
    | Var x ->
        pair (Int 0) (number x)
    | Fn ("0", []) ->
        pair (Int 1) (Int 0)
    | Fn ("S", [t]) ->
        pair (Int 2) (gterm t)
    | Fn ("+", [s;t]) ->
        pair (Int 3) (pair (gterm s) (gterm t))
    | Fn ("*", [s;t]) ->
        pair (Int 4) (pair (gterm s) (gterm t))
    | _ ->
        failwith "gterm: not in the language"

let rec gform fm =
    match fm with
    | False ->
        pair (Int 0) (Int 0)
    | True ->
        pair (Int 0) (Int 1)
    | Atom (R ("=", [s;t])) ->
        pair (Int 1) (pair (gterm s) (gterm t))
    | Atom (R ("<", [s;t])) ->
        pair (Int 2) (pair (gterm s) (gterm t))
    | Atom (R ("<=", [s;t])) ->
        pair (Int 3) (pair (gterm s) (gterm t))
    | Not p ->
        pair (Int 4) (gform p)
    | And (p, q) ->
        pair (Int 5) (pair (gform p) (gform q))
    | Or (p, q) ->
        pair (Int 6) (pair (gform p) (gform q))
    | Imp (p, q) ->
        pair (Int 7) (pair (gform p) (gform q))
    | Iff (p, q) ->
        pair (Int 8) (pair (gform p) (gform q))
    | Forall (x, p) ->
        pair (Int 9) (pair (number x) (gform p))
    | Exists (x, p) ->
        pair (Int 10) (pair (number x) (gform p))
    | _ ->
        failwith "gform: not in the language"
    
// pg. 537
// ------------------------------------------------------------------------- //
// The "gnumeral" function.                                                  //
// ------------------------------------------------------------------------- //

let gnumeral n = gterm (numeral n)
    
// pg. 538
// ------------------------------------------------------------------------- //
// Intuition for the self-referential sentence.                              //
// ------------------------------------------------------------------------- //

let diag001 s =
    let rec replacex n l =
        match l with
        | [] ->
            if n = 0 then ""
            else failwith "unmatched quotes"
        | "x" :: t when n = 0 ->
            "`" + s + "'" + replacex n t
        | "`" :: t ->
            "`" + replacex (n + 1) t
        | "'" :: t ->
            "'" + replacex (n - 1) t
        | h :: t ->
            h + replacex n t
    replacex 0 (explode s)

let phi001 = diag001 "P(diag(x))"
    
// pg. 538
// ------------------------------------------------------------------------- //
// Pseudo-substitution variant.                                              //
// ------------------------------------------------------------------------- //

let qdiag001 s = sprintf "let `x' be `%s' in %s"
let phi002 = qdiag001 "P(qdiag(x))"
    
// pg. ???
// ------------------------------------------------------------------------- //
// Quine from Martin Jambon.                                                 //
// ------------------------------------------------------------------------- //

(fun s -> Printf.printf "%s\n%s\n" s s) "(fun s -> Printf.printf \"%s\\n%S\\n\" s s)"
    
// pg. 538
// ------------------------------------------------------------------------- //
// Diagonalization and quasi-diagonalization of formulas.                    //
// ------------------------------------------------------------------------- //

let diag002 x p =
    subst (x |=> numeral (gform p)) p

let qdiag002 x p =
    Exists (x, And (mk_eq (Var x) (numeral (gform p)), p))
        
// pg. 548
// ------------------------------------------------------------------------- //
// Decider for delta-sentences.                                              //
// ------------------------------------------------------------------------- //

let rec dtermval v tm =
    match tm with
    | Var x ->
        apply v x
    | Fn ("0", []) ->
        Int 0
    | Fn ("S", [t]) ->
        dtermval v t + Int 1
    | Fn ("+", [s;t]) ->
        dtermval v s + dtermval v t
    | Fn ("*", [s;t]) ->
        dtermval v s * dtermval v t
    | _ ->
        failwith "dtermval: not a ground term of the language"

let rec dholds v fm =
    match fm with
    | False ->
        false
    | True ->
        true
    | Atom (R ("=", [s;t])) ->
        dtermval v s = dtermval v t
    | Atom (R ("<", [s;t])) ->
        dtermval v s < dtermval v t
    | Atom (R ("<=", [s;t])) ->
        dtermval v s <= dtermval v t
    | Not p ->
        not (dholds v p)
    | And (p, q) ->
        dholds v p && dholds v q
    | Or (p, q) ->
        dholds v p || dholds v q
    | Imp (p, q) ->
        not (dholds v p) || dholds v q
    | Iff (p, q) ->
        dholds v p = dholds v q
    | Forall (x, Imp (Atom (R (a, [Var y;t])), p)) ->
        dhquant List.forall v x y a t p
    | Exists (x, And (Atom (R (a, [Var y;t])), p)) ->
        dhquant List.exists v x y a t p
    | _ ->
        failwith "dholds: not an arithmetical delta-formula"

and dhquant pred v x y a t p =
    if x <> y || mem x (fvt t) then
        failwith "dholds: not delta"
    else
        let m =
            if a = "<" then dtermval v t - Int 1
            else dtermval v t
        pred (fun n -> dholds ((x |-> n) v) p) (Int 0 --- m)

// pg. 550
// ------------------------------------------------------------------------- //
// Test sigma/pi status (don't check the language of arithmetic).            //
// ------------------------------------------------------------------------- //

type formulaclass = Sigma | Pi | Delta

let opp = function
    | Sigma -> Pi
    | Pi -> Sigma
    | Delta -> Delta

let rec classify c n fm =
    match fm with
    | False
    | True
    | Atom _ ->
        true
    | Not p ->
        classify (opp c) n p
    | And (p, q)
    | Or (p, q) ->
        classify c n p && classify c n q
    | Imp (p, q) ->
        classify (opp c) n p && classify c n q
    | Iff (p, q) ->
        classify Delta n p && classify Delta n q
    | Exists (x, p) when n <> 0 && c = Sigma ->
        classify c n p
    | Forall (x, p) when n <> 0 && c = Pi ->
        classify c n p
    | Exists (x, And (Atom (R (("<"|"<="), [Var y;t])), p))
    | Forall (x, Imp (Atom (R (("<"|"<="), [Var y;t])), p))
        when x = y && not(mem x (fvt t)) ->
        classify c n p
    | Exists (x, p)
    | Forall (x, p) ->
        n <> 0 && classify (opp c) (n - 1) fm

// pg. 551
// ------------------------------------------------------------------------- //
// Verification of true Sigma_1 formulas, refutation of false Pi_1 formulas. //
// ------------------------------------------------------------------------- //

let rec veref sign m v fm =
    match fm with
    | False ->
        sign false
    | True ->
        sign true
    | Atom (R ("=", [s;t])) ->
        sign (dtermval v s = dtermval v t)
    | Atom (R ("<", [s;t])) ->
        sign (dtermval v s < dtermval v t)
    | Atom (R ("<=", [s;t])) ->
        sign (dtermval v s <= dtermval v t)
    | Not p ->
        veref (not << sign) m v p
    | And (p, q) ->
        sign (sign (veref sign m v p) && sign (veref sign m v q))
    | Or (p, q) ->
        sign (sign (veref sign m v p) || sign (veref sign m v q))
    | Imp (p, q) ->
        veref sign m v (Or (Not p, q))
    | Iff (p, q) ->
        veref sign m v (And (Imp (p, q), Imp (q, p)))
    | Exists (x, p)
        when sign true ->
        List.exists (fun n -> veref sign m ((x |-> n) v) p) (Int 0 --- m)
    | Forall (x, p)
        when sign false ->
        List.exists (fun n -> veref sign m ((x |-> n) v) p) (Int 0 --- m)
    | Forall (x, Imp (Atom (R (a, [Var y;t])), p))
        when sign true ->
        verefboundquant m v x y a t sign p
    | Exists (x, And (Atom (R (a, [Var y;t])), p))
        when sign false ->
        verefboundquant m v x y a t sign p

and verefboundquant m v x y a t sign p =
    if x <> y || mem x (fvt t) then
        failwith "veref"
    else
        let m =
            if a = "<" then dtermval v t - Int 1
            else dtermval v t
        List.forall (fun n -> veref sign m ((x |-> n) v) p) (Int 0 --- m)

let sholds = veref id
    
// pg. 552
// ------------------------------------------------------------------------- //
// Find adequate bound for all existentials to make sentence true.           //
// ------------------------------------------------------------------------- //

let sigma_bound fm =
    first (Int 0) (fun n -> sholds n undefined fm)
    
// pg. 558
// ------------------------------------------------------------------------- //
// Turing machines.                                                          //
// ------------------------------------------------------------------------- //

type symbol = Blank | One

type direction = Left | Right | Stay
    
// pg. 558
// ------------------------------------------------------------------------- //
// Type of the tape.                                                         //
// ------------------------------------------------------------------------- //

type tape = Tape of int * func<int, symbol>
    
// pg. 558
// ------------------------------------------------------------------------- //
// Look at current character.                                                //
// ------------------------------------------------------------------------- //

let look (Tape(r,f)) =
    tryapplyd f r Blank
        
// pg. 559
// ------------------------------------------------------------------------- //
// Write a symbol on the tape.                                               //
// ------------------------------------------------------------------------- //

let write s (Tape(r, f)) =
    Tape (r, (r |-> s) f)
        
// pg. 559
// ------------------------------------------------------------------------- //
// Move machine left or right.                                               //
// ------------------------------------------------------------------------- //

let move dir (Tape (r, f)) =
    let d =
        if dir = Left then -1
        elif dir = Right then 1
        else 0
    Tape (r + d, f)
        
// pg. 559
// ------------------------------------------------------------------------- //
// Configurations, i.e. state and tape together.                             //
// ------------------------------------------------------------------------- //

type config = Config of int * tape
    
// pg. 559
// ------------------------------------------------------------------------- //
// Keep running till we get to an undefined state.                           //
// ------------------------------------------------------------------------- //

let rec run prog (Config (state, tape) as config) =
    let stt = state, look tape
    if defined prog stt then
        let char, dir, state' = apply prog stt
        run prog (Config (state', move dir (write char tape)))
    else config
        
// pg. 560
// ------------------------------------------------------------------------- //
// Tape with set of canonical input arguments.                               //
// ------------------------------------------------------------------------- //

let input_tape =
    let writen n =
        funpow n (move Left << write One) << move Left << write Blank
    fun args ->
        List.foldBack writen args (Tape (0, undefined))
            
// pg. 560
// ------------------------------------------------------------------------- //
// Read the result of the tape.                                              //
// ------------------------------------------------------------------------- //

let rec output_tape tape =
    let tape' = move Right tape
    if look tape' = Blank then 0
    else 1 + output_tape tape'
        
// pg. 560
// ------------------------------------------------------------------------- //
// Overall program execution.                                                //
// ------------------------------------------------------------------------- //

let exec prog args =
    let c = Config (1, input_tape args)
    match run prog c with
    | Config (_, t) ->
        output_tape t

// pg. 565
// ------------------------------------------------------------------------- //
// Robinson axioms.                                                          //
// ------------------------------------------------------------------------- //
//
let robinson = (parse "(forall m n. S(m) = S(n) ==> m = n) /\ (forall n. ~(n = 0) <=> exists m. n = S(m)) /\ (forall n. 0 + n = n) /\ (forall m n. S(m) + n = S(m + n)) /\ (forall n. 0 * n = 0) /\ (forall m n. S(m) * n = n + m * n) /\ (forall m n. m <= n <=> exists d. m + d = n) /\ (forall m n. m < n <=> S(m) <= n)")

let [suc_inj; num_cases; add_0; add_suc;
        mul_0; mul_suc; le_def; lt_def;] =
    conjths robinson

// pg. 565
// ------------------------------------------------------------------------- //
// Particularly useful "right handed" inference rules.                       //
// ------------------------------------------------------------------------- //

let right_spec t th = imp_trans th (ispec t (consequent (concl th)))

let right_mp ith th =
    imp_unduplicate (imp_trans th (imp_swap ith))

let right_imp_trans th1 th2 =
    imp_unduplicate (imp_front 2 (imp_trans2 th1 (imp_swap th2)))

let right_sym th =
    let s, t = dest_eq (consequent (concl th))
    imp_trans th (eq_sym s t)

let right_trans th1 th2 =
    let s, t = dest_eq (consequent (concl th1))
    let t', u = dest_eq (consequent (concl th2))
    imp_trans_chain [th1; th2] (eq_trans s t u)
        
// pg. 566
// ------------------------------------------------------------------------- //
// Evalute constant expressions (allow non-constant on RHS in last clause).  //
// ------------------------------------------------------------------------- //

let rec robop tm =
    match tm with
    | Fn (op, [Fn ("0", []); t]) ->
        if op = "*" then
            right_spec t mul_0
        else
            right_trans (right_spec t add_0) (robeval t)
    | Fn (op, [Fn ("S", [u]); t]) ->
        let th2 =
            let th1 =
                if op = "+" then add_suc
                else mul_suc
            List.foldBack right_spec [t;u] th1
        right_trans th2 (robeval (rhs (consequent (concl th2))))

and robeval tm =
    match tm with
    | Fn ("S", [t]) ->
        let th = robeval t
        let t' = rhs (consequent (concl th))
        imp_trans th (axiom_funcong "S" [t] [t'])
    | Fn (op, [s; t]) ->
        let th1 = robeval s
        let s' = rhs (consequent (concl th1))
        let th2 = robop (Fn (op, [s';t]))
        let th3 = axiom_funcong op [s;t] [s';t]
        let th4 = modusponens (imp_swap th3) (axiom_eqrefl t)
        right_trans (imp_trans th1 th4) th2
    | _ ->
        add_assum robinson (axiom_eqrefl tm)
    
// pg. 567
// ------------------------------------------------------------------------- //
// Consequences of the axioms.                                               //
// ------------------------------------------------------------------------- //

let robinson_consequences = (parse "(forall n. S(n) = 0 ==> false) /\ (forall n. 0 = S(n) ==> false) /\ (forall m n. (m = n ==> false) ==> (S(m) = S(n) ==> false)) /\ (forall m n. (exists d. m + d = n) ==> m <= n) /\ (forall m n. S(m) <= n ==> m < n) /\ (forall m n. (forall d. d <= n ==> d = m ==> false) ==> m <= n ==> false) /\ (forall m n. (forall d. d < n ==> d = m ==> false) ==> m < n ==> false) /\ (forall n. n <= 0 \/ exists m. S(m) = n) /\ (forall n. n <= 0 ==> n = 0) /\ (forall m n. S(m) <= S(n) ==> m <= n) /\ (forall m n. m < S(n) ==> m <= n) /\ (forall n. n < 0 ==> false)")

let robinson_thm =
    prove (Imp (robinson, robinson_consequences)) [
        note ("eq_refl", parse "forall x. x = x") using [axiom_eqrefl (Var "x")];
        note ("eq_trans", parse "forall x y z. x = y ==> y = z ==> x = z")
            using [eq_trans (Var "x") (Var "y") (Var "z")];
        note ("eq_sym", parse "forall x y. x = y ==> y = x")
            using [eq_sym (Var "x") (Var "y")];
        note ("suc_cong", parse "forall a b. a = b ==> S(a) = S(b)")
            using [axiom_funcong "S" [Var "a"] [Var "b"]];
        note ("add_cong",
            parse "forall a b c d. a = b /\ c = d ==> a + c = b + d")
            using [axiom_funcong "+" [Var "a"; Var "c"] [Var "b"; Var "d"]];
        note ("le_cong",
            parse "forall a b c d. a = b /\ c = d ==> a <= c ==> b <= d")
            using [axiom_predcong "<=" [Var "a"; Var "c"] [Var "b"; Var "d"]];
        note ("lt_cong",
            parse "forall a b c d. a = b /\ c = d ==> a < c ==> b < d")
            using [axiom_predcong "<" [Var "a"; Var "c"] [Var "b"; Var "d"]];

        assume ["suc_inj", parse "forall m n. S(m) = S(n) ==> m = n";
                "num_nz", parse "forall n. ~(n = 0) <=> exists m. n = S(m)";
                "add_0", parse "forall n. 0 + n = n";
                "add_suc", parse "forall m n. S(m) + n = S(m + n)";
                "mul_0", parse "forall n. 0 * n = 0";
                "mul_suc", parse "forall m n. S(m) * n = n + m * n";
                "le_def", parse "forall m n. m <= n <=> exists d. m + d = n";
                "lt_def", parse "forall m n. m < n <=> S(m) <= n"];
        note ("not_suc_0", parse "forall n. ~(S(n) = 0)") by ["num_nz"; "eq_refl"];
        so conclude (parse "forall n. S(n) = 0 ==> false") at once;
        so conclude (parse "forall n. 0 = S(n) ==> false") by ["eq_sym"];
        note ("num_cases", parse "forall n. (n = 0) \/ exists m. n = S(m)")
                by ["num_nz"];
        note ("suc_inj_eq", parse "forall m n. S(m) = S(n) <=> m = n")
            by ["suc_inj"; "suc_cong"];
        so conclude
            (parse "forall m n. (m = n ==> false) ==> (S(m) = S(n) ==> false)")
            at once;
        conclude (parse "forall m n. (exists d. m + d = n) ==> m <= n")
            by ["le_def"];
        conclude (parse "forall m n. S(m) <= n ==> m < n") by ["lt_def"];
        conclude (parse "forall m n. (forall d. d <= n ==> d = m ==> false) ==> m <= n ==> false")
            by ["eq_refl"; "le_cong"];
        conclude (parse "forall m n. (forall d. d < n ==> d = m ==> false) ==> m < n ==> false")
            by ["eq_refl"; "lt_cong"];
        have (parse "0 <= 0") by ["le_def"; "add_0"];
        so have (parse "forall x. x = 0 ==> x <= 0")
            by ["le_cong"; "eq_refl"; "eq_sym"];
        so conclude (parse "forall n. n <= 0 \/ (exists m. S(m) = n)")
            by ["num_nz"; "eq_sym"];
        note ("add_eq_0", parse "forall m n. m + n = 0 ==> m = 0 /\ n = 0") proof [
            fix "m"; fix "n";
                assume ["A", parse "m + n = 0"];
                cases (parse "m = 0 \/ exists p. m = S(p)") by ["num_cases"];
                so conclude (parse "m = 0") at once;
                so have (parse "m + n = 0 + n") by ["add_cong"; "eq_refl"];
                so our thesis by ["A"; "add_0"; "eq_sym"; "eq_trans"];
                qed;
                so consider ("p", parse "m = S(p)") at once;
                so have (parse "m + n = S(p) + n") by ["add_cong"; "eq_refl"];
                so have (parse "m + n = S(p + n)") by ["eq_trans"; "add_suc"];
                so have (parse "S(p + n) = 0") by ["A"; "eq_sym"; "eq_trans"];
                so our thesis by ["not_suc_0"];
                qed];
        so conclude (parse "forall n. n <= 0 ==> n = 0") by ["le_def"];
        have (parse "forall m n. S(m) <= S(n) ==> m <= n") proof
            [fix "m"; fix "n";
                assume ["lesuc", parse "S(m) <= S(n)"];
                so consider ("d", parse "S(m) + d = S(n)") by ["le_def"];
                so have (parse "S(m + d) = S(n)") by ["add_suc"; "eq_sym"; "eq_trans"];
                so have (parse "m + d = n") by ["suc_inj"];
                so conclude (parse "m <= n") by ["le_def"];
                qed];
    so conclude (parse "forall m n. S(m) <= S(n) ==> m <= n") at once;
    so conclude (parse "forall m n. m < S(n) ==> m <= n") by ["lt_def"];
    fix "n";
    assume ["hyp", parse "n < 0"];
    so have (parse "S(n) <= 0") by ["lt_def"];
    so consider ("d", parse "S(n) + d = 0") by ["le_def"];
    so have (parse "S(n + d) = 0") by ["add_suc"; "eq_trans"; "eq_sym"];
    so our thesis by ["not_suc_0"];
    qed; ]

let [suc_0_l; suc_0_r; suc_inj_false;
        expand_le; expand_lt; expand_nle; expand_nlt;
        num_lecases; le_0; le_suc; lt_suc; lt_0] =
        List.map (imp_trans robinson_thm) (conjths robinson_consequences)

// pg. 567
// ------------------------------------------------------------------------- //
// Prove or disprove equations between ground terms.                         //
// ------------------------------------------------------------------------- //

let rob_eq s t =
    let rec sth = robeval s
    and tth = robeval t
    right_trans sth (right_sym tth)

let rec rob_nen (s, t) =
    match s, t with
    | Fn ("S", [s']), Fn ("0", []) ->
        right_spec s' suc_0_l
    | Fn ("0", []), Fn ("S", [t']) ->
        right_spec t' suc_0_r
    | Fn("S", [u]), Fn ("S", [v]) ->
            right_mp (List.foldBack right_spec [v; u] suc_inj_false) (rob_nen (u, v))
    | _ ->
        failwith "rob_ne: true equation or unexpected term"

let rob_ne s t =
    let rec sth = robeval s
    and tth = robeval t
    let rec s' = rhs (consequent (concl sth))
    and t' = rhs (consequent (concl tth))
    let th = rob_nen (s',t')
    let xth = axiom_predcong "=" [s; t] [s'; t']
    right_imp_trans (right_mp (imp_trans sth xth) tth) th
    
// pg. 570
// ------------------------------------------------------------------------- //
// Dual version of "eliminate_connective" for unnegated case.                //
// ------------------------------------------------------------------------- //

let introduce_connective fm =
    if not <| negativef fm then
        iff_imp2 (expand_connective fm)
    else
        imp_add_concl False (iff_imp1 (expand_connective (negatef fm)))
            
// pg. 570
// ------------------------------------------------------------------------- //
// This is needed to preserve the canonical form for bounded quantifiers.    //
//                                                                           //
// |- (forall x. p(x) ==> q(x) ==> false)                                    //
//    ==> (exists x. p(x) /\ q(x)) ==> false                                 //
// ------------------------------------------------------------------------- //

let elim_bex fm =
    match fm with
    | Imp (Exists (x, And (p, q)), False) ->
        let rec pq = And (p, q)
        and pqf = Imp (p, Imp (q, False))
        let th1 = imp_swap (imp_refl (Imp (pqf, False)))
        let th2 = imp_trans th1 (introduce_connective (Imp (pq, False)))
        imp_trans (genimp x th2) (exists_left_th x pq False)
    | _ ->
        failwith "elim_bex"
            
// pg. 570
// ------------------------------------------------------------------------- //
// Eliminate some concepts in terms of others.                               //
// ------------------------------------------------------------------------- //
//
let sigma_elim fm =
    match fm with
    | Atom (R ("<=", [s;t])) ->
        List.foldBack right_spec [t;s] expand_le
    | Atom (R ("<" ,[s;t])) ->
        List.foldBack right_spec [t;s] expand_lt
    | Imp (Atom (R ("<=", [s;t])), False) ->
        List.foldBack right_spec [t;s] expand_nle
    | Imp (Atom (R ("<", [s;t])), False) ->
        List.foldBack right_spec [t;s] expand_nlt
    | Imp (Exists (x, And (p, q)), False) ->
        add_assum robinson (elim_bex fm)
    | _ ->
        add_assum robinson (introduce_connective fm)

// pg. 571
// ------------------------------------------------------------------------- //
// |- R ==> forall x. x <= 0 ==> P(x)  |- R ==> forall x. x <= n ==> P(S(x)) //
// ----------------------------------------------------------------------    //
//         |- R ==> forall x. x <= S(n) ==> P(x)                             //
// ------------------------------------------------------------------------- //
//
let boundquant_step th0 th1 =
    match concl th0,concl th1 with
    | Imp (_, Forall (x, Imp (_, p))),
            Imp (_, Forall (_, Imp (Atom (R ("<=", [_;t])) ,_))) ->
        let th2 = List.foldBack right_spec [t; Var x] le_suc
        let th3 = right_imp_trans th2 (right_spec (Var x) th1)
        let y = variant "y" (var (concl th1))
        let q = Imp (Atom (R ("<=", [Var x; Fn ("S", [t])])), p)
        let rec qx = consequent (concl th3)
        and qy = subst (x |=> Var y) q
        let th4 = imp_swap (isubst (Fn ("S", [Var x])) (Var y) qx qy)
        let th5 = exists_left x (imp_swap (imp_trans th3 th4))
        let th6 = spec (Var x) (gen y th5)
        let th7 = imp_insert (antecedent q) (right_spec (Var x) th0)
        let th8 = ante_disj (imp_front 2 th7) th6
        let th9 = right_spec (Var x) num_lecases
        let rec a1 = consequent (concl th9)
        and a2 = antecedent (concl th8)
        let tha = modusponens (isubst zero zero a1 a2) (axiom_eqrefl zero)
        gen_right x (imp_unduplicate (imp_trans (imp_trans th9 tha) th8))
          
// pg. 572
// ------------------------------------------------------------------------- //
// Main sigma-prover.                                                        //
// ------------------------------------------------------------------------- //

let rec sigma_prove fm =
    match fm with
    | False ->
        failwith "sigma_prove"
    | Atom (R ("=", [s;t])) ->
        rob_eq s t
    | Imp (Atom (R ("=", [s;t])), False) ->
        rob_ne s t
    | Imp (p, q) when p = q ->
        add_assum robinson (imp_refl p)
    | Imp (Imp (p, q), False) ->
        let rec pth = sigma_prove p
        and qth = sigma_prove (Imp (q, False))
        right_mp (imp_trans qth (imp_truefalse p q)) pth
    | Imp (p, q) when q <> False ->
        let m = sigma_bound fm
        if sholds m undefined q then
            imp_insert p (sigma_prove q)
        else
            imp_trans2 (sigma_prove (Imp (p, False))) (ex_falso q)
    | Imp (Forall (x, p), False) ->
        let m = sigma_bound (Exists (x, Not p))
        let n = first (Int 0) (fun n ->
            sholds m undefined (subst (x |=> numeral n) (Not p)))
        let ith = ispec (numeral n) (Forall (x, p))
        let th = sigma_prove (Imp (consequent (concl ith), False))
        imp_swap (imp_trans ith (imp_swap th))
    | Forall (x, Imp (Atom (R (("<="|"<" as a), [Var x';t])), q))
        when x' = x && not(occurs_in (Var x) t) ->
        bounded_prove (a, x, t, q)
    | _ ->
        let th = sigma_elim fm
        right_mp th (sigma_prove (antecedent (consequent (concl th))))

// pg. 572
// ------------------------------------------------------------------------- //
// Evaluate the bound for a bounded quantifier                               //
// ------------------------------------------------------------------------- //

and bounded_prove (a, x, t, q) =
    let tth = robeval t
    let u = rhs (consequent (concl tth))
    let rec th1 = boundednum_prove (a, x, u, q)
    and th2 = axiom_predcong a [Var x; t] [Var x; u]
    let th3 = imp_trans tth (modusponens th2 (axiom_eqrefl (Var x)))
    let a,b = dest_imp (consequent (concl th3))
    let th4 = imp_swap (imp_trans_th a b q)
    gen_right x (right_mp (imp_trans th3 th4) (right_spec (Var x) th1))
        
// pg. 573
// ------------------------------------------------------------------------- //
// Actual expansion of a bounded quantifier.                                 //
// ------------------------------------------------------------------------- //

and boundednum_prove (a, x, t, q) =
    match a, t with
    | "<", Fn ("0", []) ->
        gen_right x (imp_trans2 (right_spec (Var x) lt_0) (ex_falso q))
    | "<", Fn ("S", [u]) ->
        let th1 = List.foldBack right_spec [u; Var x] lt_suc
        let th2 = boundednum_prove ("<=", x, u, q)
        let th3 = imp_trans2 th1 (imp_swap (right_spec (Var x) th2))
        gen_right x (imp_unduplicate (imp_front 2 th3))
    | "<=", Fn ("0", []) ->
        let q' = subst (x |=> zero) q
        let th1 = imp_trans (eq_sym (Var x) zero) (isubst zero (Var x) q' q)
        let th2 = imp_trans2 (right_spec (Var x) le_0) th1
        let th3 = imp_swap (imp_front 2 th2)
        gen_right x (right_mp th3 (sigma_prove q'))
    | "<=", Fn ("S", [u]) ->
        let rec fm' = Forall (x, Imp (Atom (R ("<=", [Var x; zero])), q))
        and fm'' = Forall (x, Imp (Atom (R ("<=", [Var x; u])),
                            subst (x |=> Fn ("S", [Var x])) q))
        boundquant_step (sigma_prove fm') (sigma_prove fm'')