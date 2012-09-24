// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
//open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
//open Reasoning.Automated.Harrison.Handbook.skolem
//open Reasoning.Automated.Harrison.Handbook.herbrand
//open Reasoning.Automated.Harrison.Handbook.unif
//open Reasoning.Automated.Harrison.Handbook.tableaux
//open Reasoning.Automated.Harrison.Handbook.resolution
//open Reasoning.Automated.Harrison.Handbook.prolog
//open Reasoning.Automated.Harrison.Handbook.meson
//open Reasoning.Automated.Harrison.Handbook.skolems
//open Reasoning.Automated.Harrison.Handbook.equal
//open Reasoning.Automated.Harrison.Handbook.cong
//open Reasoning.Automated.Harrison.Handbook.rewrite
//open Reasoning.Automated.Harrison.Handbook.order
//open Reasoning.Automated.Harrison.Handbook.completion
//open Reasoning.Automated.Harrison.Handbook.eqelim
//open Reasoning.Automated.Harrison.Handbook.paramodulation
//open Reasoning.Automated.Harrison.Handbook.decidable
//open Reasoning.Automated.Harrison.Handbook.qelim
//open Reasoning.Automated.Harrison.Handbook.cooper
//open Reasoning.Automated.Harrison.Handbook.complex
//open Reasoning.Automated.Harrison.Handbook.real
//open Reasoning.Automated.Harrison.Handbook.grobner
//open Reasoning.Automated.Harrison.Handbook.geom
//open Reasoning.Automated.Harrison.Handbook.interpolation
//open Reasoning.Automated.Harrison.Handbook.combining
open Reasoning.Automated.Harrison.Handbook.lcf
open Reasoning.Automated.Harrison.Handbook.lcfprop
open Reasoning.Automated.Harrison.Handbook.folderived
//open Reasoning.Automated.Harrison.Handbook.lcffol
open Reasoning.Automated.Harrison.Handbook.tactics

//fsi.AddPrinter print_goal;;

// pg. 514
// ------------------------------------------------------------------------- //
// A simple example.                                                         //
// ------------------------------------------------------------------------- //

// 1 subgoal:
// ---> (forall x. x <=x) /\
//      (forall x y z. x <=y /\ y <=z ==> x <=z) /\
//      (forall x y. f(x) <=y <=> x <=g(y)) ==>
//      (forall x y. x <=y ==> f(x) <=f(y)) /\
//      (forall x y. x <=y ==> g(x) <=g(y))
// val it : unit = ()
let g0 = set_goal (parse "(forall x. x <= x) /\ (forall x y z. x <= y /\ y <= z ==> x <= z) /\ (forall x y. f(x) <= y <=> x <= g(y)) ==> (forall x y. x <= y ==> f(x) <= f(y)) /\ (forall x y. x <= y ==> g(x) <= g(y))");;
print_goal g0;;

// 1 subgoal:
// ant: (forall x. x <=x) /\
//      (forall x y z. x <=y /\ y <=z ==> x <=z) /\
//      (forall x y. f(x) <=y <=> x <=g(y))
// ---> (forall x y. x <=y ==> f(x) <=f(y)) /\
//      (forall x y. x <=y ==> g(x) <=g(y))
// val it : unit = ()
let g1 = imp_intro_tac "ant" g0;;
print_goal g1;;

// 2 subgoals starting with
// ant: (forall x. x <=x) /\
//      (forall x y z. x <=y /\ y <=z ==> x <=z) /\
//      (forall x y. f(x) <=y <=> x <=g(y))
// ---> forall x y. x <=y ==> f(x) <=f(y)
// val it : unit = ()
let g2 = conj_intro_tac g1;;
print_goal g2;;

// TODO: Finish running examples and recording output.
let g3 = funpow 2 (auto_tac by ["ant"]) g2;;
print_goal g3;;

extract_thm g3;;
    
// pg. 514
// ------------------------------------------------------------------------- //
// All packaged up together.                                                 //
// ------------------------------------------------------------------------- //

prove (parse "(forall x. x <= x) /\(forall x y z. x <= y /\ y <= z ==> x <= z) /\(forall x y. f(x) <= y <=> x <= g(y))==> (forall x y. x <= y ==> f(x) <= f(y)) /\ (forall x y. x <= y ==> g(x) <= g(y))")
        [imp_intro_tac "ant";
        conj_intro_tac;
        auto_tac by ["ant"];
        auto_tac by ["ant"]];;
      
// pg. 518
// ------------------------------------------------------------------------- //
// A simple example.                                                         //
// ------------------------------------------------------------------------- //

let ewd954 = 
    prove (parse "(forall x y. x <= y <=> x * y = x) /\ (forall x y. f(x * y) = f(x) * f(y)) ==> forall x y. x <= y ==> f(x) <= f(y)") [note("eq_sym",(parse "forall x y. x = y ==> y = x"))
    using [eq_sym (parset "x") (parset "y")];
    note("eq_trans",(parse "forall x y z. x = y /\ y = z ==> x = z"))
    using [eq_trans (parset "x") (parset "y") (parset "z")];
    note("eq_cong",(parse "forall x y. x = y ==> f(x) = f(y)"))
    using [axiom_funcong "f" [(parset "x")] [(parset "y")]];
    assume ["le",(parse "forall x y. x <= y <=> x * y = x");
            "hom",(parse "forall x y. f(x * y) = f(x) * f(y)")];
    fix "x"; fix "y";
    assume ["xy",(parse "x <= y")];
    so have (parse "x * y = x") by ["le"];
    so have (parse "f(x * y) = f(x)") by ["eq_cong"];
    so have (parse "f(x) = f(x * y)") by ["eq_sym"];
    so have (parse "f(x) = f(x) * f(y)") by ["eq_trans"; "hom"];
    so have (parse "f(x) * f(y) = f(x)") by ["eq_sym"];
    so conclude (parse "f(x) <= f(y)") by ["le"];
    qed];;

// ------------------------------------------------------------------------- //
// More examples not in the main text.                                       //
// ------------------------------------------------------------------------- //

prove
    (parse "(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")
    [assume ["A",(parse "exists x. p(x)")];
    assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
    note ("C",(parse "forall x. p(x) ==> p(f(f(f(f(x)))))"))
    proof
    [have (parse "forall x. p(x) ==> p(f(f(x)))") by ["B"];
        so conclude (parse "forall x. p(x) ==> p(f(f(f(f(x)))))") at once;
        qed];
    consider ("a",(parse "p(a)")) by ["A"];
    take (parset "a");
    so conclude (parse "p(f(f(f(f(a)))))") by ["C"];
    qed];;

// ------------------------------------------------------------------------- //
// Alternative formulation with lemma construct.                             //
// ------------------------------------------------------------------------- //

let lemma (s,p) (Goals((asl,w)::gls,jfn) as gl) =
    Goals((asl,p)::((s,p)::asl,w)::gls,
        fun (thp::thw::oths) ->
            jfn(imp_unduplicate(imp_trans thp (shunt thw)) :: oths)) in
prove
    (parse "(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")
    [assume ["A",(parse "exists x. p(x)")];
    assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
    lemma ("C",(parse "forall x. p(x) ==> p(f(f(f(f(x)))))"));
        have (parse "forall x. p(x) ==> p(f(f(x)))") by ["B"];
        so conclude (parse "forall x. p(x) ==> p(f(f(f(f(x)))))") at once;
        qed;
    consider ("a",(parse "p(a)")) by ["A"];
    take (parset "a");
    so conclude (parse "p(f(f(f(f(a)))))") by ["C"];
    qed];;

// ------------------------------------------------------------------------- //
// Running a series of proof steps one by one on goals.                      //
// ------------------------------------------------------------------------- //

let run prf g = List.foldBack id (List.rev prf) g

// ------------------------------------------------------------------------- //
// LCF-style interactivity.                                                  //
// ------------------------------------------------------------------------- //

let current_goal = ref[set_goal False]

let g x =
    current_goal := [set_goal x]
    List.head(!current_goal)

let e t =
    current_goal := (t(List.head(!current_goal))::(!current_goal))
    List.head(!current_goal)

let es t =
    current_goal := (run t (List.head(!current_goal))::(!current_goal))
    List.head(!current_goal)

let b () =
    current_goal := List.tail(!current_goal)
    List.head(!current_goal)

// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

prove (parse "p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
        [our thesis at once;
        qed];;

prove
    (parse "(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")
    [assume ["A",(parse "exists x. p(x)")];
    assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
    note ("C",(parse "forall x. p(x) ==> p(f(f(f(f(x)))))")) proof
    [have (parse "forall x. p(x) ==> p(f(f(x)))") by ["B"];
        so our thesis at once;
        qed];
    consider ("a",(parse "p(a)")) by ["A"];
    take (parset "a");
    so our thesis by ["C"];
    qed];;

prove (parse "forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
        [fix "c";
        assume ["A",(parse "p(c)")];
        assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
        take (parset "c");
        conclude (parse "p(c)") by ["A"];
        note ("C",(parse "p(c) ==> p(f(c))")) by ["B"];
        so our thesis by ["C"; "A"];
        qed];;

prove (parse "p(c) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
        [assume ["A",(parse "p(c)")];
        assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
        take (parset "c");
        conclude (parse "p(c)") by ["A"];
        our thesis by ["A"; "B"];
        qed];;

prove (parse "forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
        [fix "c";
        assume ["A",(parse "p(c)")];
        assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
        take (parset "c");
        conclude (parse "p(c)") by ["A"];
        note ("C",(parse "p(c) ==> p(f(c))")) by ["B"];
        our thesis by ["C"; "A"];
        qed];;

prove (parse "forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\ p(f(y))")
        [fix "c";
        assume ["A",(parse "p(c)")];
        assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
        take (parset "c");
        note ("D",(parse "p(c)")) by ["A"];
        note ("C",(parse "p(c) ==> p(f(c))")) by ["B"];
        our thesis by ["C"; "A"; "D"];
        qed];;


prove (parse "(p(a) \/ p(b)) ==> q ==> exists y. p(y)")
    [assume ["A",(parse "p(a) \/ p(b)")];
    assume ["",(parse "q")];
    cases (parse "p(a) \/ p(b)") by ["A"];
        take (parset "a");
        so our thesis at once;
        qed;

        take (parset "b");
        so our thesis at once;
        qed];;
        
// TODO: Fix this so it works
//let v1 = "A"
//let v2 = (parse "p(a)")
//let v3 = note(v1,v2)
//prove
//    (parse "(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))")
//    [assume ["base",(parse "p(a) \/ p(b)");
//            "Step",(parse "forall x. p(x) ==> p(f(x))")];
//    cases (parse "p(a) \/ p(b)") by ["base"]; 
//        so v3 at once;
//        note ("X",(parse "p(a) ==> p(f(a))")) by ["Step"];
//        take (parset "a");
//        our thesis by ["A"; "X"];
//        qed;
//
//        take (parset "b");
//        so our thesis by ["Step"];
//        qed];;

prove
    (parse "(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))")
    [assume ["A",(parse "exists x. p(x)")];
    assume ["B",(parse "forall x. p(x) ==> p(f(x))")];
    consider ("a",(parse "p(a)")) by ["A"];
    so note ("concl",(parse "p(f(a))")) by ["B"];
    take (parset "a");
    our thesis by ["concl"];
    qed];;

prove (parse "(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x))
        ==> (p(a) <=> q(a))")
    [assume ["A",(parse "forall x. p(x) ==> q(x)")];
    assume ["B",(parse "forall x. q(x) ==> p(x)")];
    note ("von",(parse "p(a) ==> q(a)")) by ["A"];
    note ("bis",(parse "q(a) ==> p(a)")) by ["B"];
    our thesis by ["von"; "bis"];
    qed];;

//** Mizar-like
// This is an example of Mizar proof, it will not work with this.

//prove
//    (parse "(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))")
//    [assume ["A",(parse "antecedent")];
//    note ("Step",(parse "forall x. p(x) ==> p(f(x))")) by ["A"];
//    per_cases by ["A"];
//        suppose ("base",(parse "p(a)"));
//        note ("X",(parse "p(a) ==> p(f(a))")) by ["Step"];
//        take (parset "a");
//        our thesis by ["base"; "X"];
//        qed;
//
//        suppose ("base",(parse "p(b)"));
//        our thesis by ["Step"; "base"];
//        qed;
//    endcase];;
       
// ------------------------------------------------------------------------- //
// Some amusing efficiency tests versus a "direct" spec.                     //
// ------------------------------------------------------------------------- //

test002 10;;
test002 11;;
test002 12;;
test002 13;;
test002 14;;
test002 15;;