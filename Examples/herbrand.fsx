// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas                              //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open Reasoning.Automated.Harrison.Handbook.lib
//open Reasoning.Automated.Harrison.Handbook.intro
open Reasoning.Automated.Harrison.Handbook.formulas
open Reasoning.Automated.Harrison.Handbook.prop
//open Reasoning.Automated.Harrison.Handbook.propexamples
//open Reasoning.Automated.Harrison.Handbook.defcnf
//open Reasoning.Automated.Harrison.Handbook.dp
//open Reasoning.Automated.Harrison.Handbook.stal
//open Reasoning.Automated.Harrison.Handbook.bdd
open Reasoning.Automated.Harrison.Handbook.folMod
open Reasoning.Automated.Harrison.Handbook.skolem
open Reasoning.Automated.Harrison.Handbook.herbrand

// pg. 161
// ------------------------------------------------------------------------- //
// First example and a little tracing.                                       //
// ------------------------------------------------------------------------- //

// 0 ground instances tried; 1 items in list
// 0 ground instances tried; 1 items in list
// 1 ground instances tried; 1 items in list
// 1 ground instances tried; 1 items in list
// val it : int = 2
gilmore (parse "exists x. forall y. P(x) ==> P(y)");;

// val sfm : fol formula =
//   And (Atom (R ("P",[Var "x"])),Not (Atom (R ("P",[Fn ("f_y",[Var "x"])]))))
let sfm = skolemize(Not (parse "exists x. forall y. P(x) ==> P(y)"));;

// <<P(x) /\ ~P(f_y(x))>>
// val it : unit = ()
print_fol_formula sfm;;

// pg. 161
// ------------------------------------------------------------------------- //
// Quick example.                                                            //
// ------------------------------------------------------------------------- //

// 0 ground instances tried; 1 items in list
// 0 ground instances tried; 1 items in list
//
// val p24 : int = 1
let p24 = gilmore (parse "~(exists x. U(x) /\ Q(x)) 
/\ (forall x. P(x) ==> Q(x) \/ R(x)) 
/\ ~(exists x. P(x) ==> (exists x. Q(x))) 
/\ (forall x. Q(x) 
/\ R(x) ==> U(x)) ==> (exists x. P(x) /\ R(x))");;

// pg. 162
// ------------------------------------------------------------------------- //
// Slightly less easy example.                                               //
// ------------------------------------------------------------------------- //

// TODO: This completes in OCaml but not F#.
// 0 ground instances tried; 1 items in list
// 0 ground instances tried; 1 items in list
// 1 ground instances tried; 13 items in list
// 1 ground instances tried; 13 items in list
// 2 ground instances tried; 57 items in list
// 3 ground instances tried; 84 items in list
// 4 ground instances tried; 405 items in list
//
// Process is terminated due to StackOverflowException.
let p45 = gilmore (parse "(forall x. P(x) 
/\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==> (forall y. G(y) /\ H(x,y) ==> R(y))) 
/\ ~(exists y. L(y) /\ R(y)) 
/\ (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) 
/\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))");;

// pg. 162
// ------------------------------------------------------------------------- //
// Apparently intractable example.                                           //
// ------------------------------------------------------------------------- //

// 0 ground instances tried; 1 items in list
// 0 ground instances tried; 1 items in list
// 1 ground instances tried; 2 items in list
// 2 ground instances tried; 2 items in list
// 3 ground instances tried; 6 items in list
// 4 ground instances tried; 11 items in list
// 5 ground instances tried; 19 items in list
// 6 ground instances tried; 14 items in list
// 7 ground instances tried; 17 items in list
// 8 ground instances tried; 17 items in list
// 8 ground instances tried; 17 items in list
// 9 ground instances tried; 34 items in list
// 10 ground instances tried; 68 items in list
// 11 ground instances tried; 136 items in list
// 12 ground instances tried; 272 items in list
// 13 ground instances tried; 640 items in list
// 14 ground instances tried; 1520 items in list
// 15 ground instances tried; 3640 items in list
//
// Process is terminated due to StackOverflowException.
let p20 = gilmore (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// pg. 163
// ------------------------------------------------------------------------- //
// Show how much better than the Gilmore procedure this can be.              //
// ------------------------------------------------------------------------- //

// Note: Changed name from p20 to p20 dp
// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 5 items in list
// 2 ground instances tried; 7 items in list
// 3 ground instances tried; 10 items in list
// 4 ground instances tried; 12 items in list
// 5 ground instances tried; 13 items in list
// 6 ground instances tried; 14 items in list
// 7 ground instances tried; 15 items in list
// 8 ground instances tried; 16 items in list
// 8 ground instances tried; 16 items in list
// 9 ground instances tried; 18 items in list
// 10 ground instances tried; 20 items in list
// 11 ground instances tried; 22 items in list
// 12 ground instances tried; 24 items in list
// 13 ground instances tried; 26 items in list
// 14 ground instances tried; 28 items in list
// 15 ground instances tried; 30 items in list
// 16 ground instances tried; 32 items in list
// 17 ground instances tried; 35 items in list
// 18 ground instances tried; 37 items in list
//
// val p20dp : int = 19
let p20dp = davisputnam (parse "(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 6 items in list
// 1 ground instances tried; 6 items in list
// 2 ground instances tried; 10 items in list
// 3 ground instances tried; 14 items in list
// 4 ground instances tried; 18 items in list
// 5 ground instances tried; 22 items in list
// 6 ground instances tried; 29 items in list
// 7 ground instances tried; 36 items in list
// 7 ground instances tried; 36 items in list
// 8 ground instances tried; 40 items in list
// 9 ground instances tried; 44 items in list
// 10 ground instances tried; 48 items in list
// 11 ground instances tried; 52 items in list
// 12 ground instances tried; 56 items in list
// 13 ground instances tried; 60 items in list
// 14 ground instances tried; 64 items in list
// 15 ground instances tried; 68 items in list
// 16 ground instances tried; 72 items in list
// 17 ground instances tried; 76 items in list
// 18 ground instances tried; 80 items in list
// 19 ground instances tried; 84 items in list
// 20 ground instances tried; 88 items in list
// 21 ground instances tried; 92 items in list
// 22 ground instances tried; 96 items in list
// 23 ground instances tried; 100 items in list
// 24 ground instances tried; 104 items in list
// 25 ground instances tried; 108 items in list
// 26 ground instances tried; 112 items in list
// 27 ground instances tried; 116 items in list
// 28 ground instances tried; 123 items in list
// 29 ground instances tried; 130 items in list
// 30 ground instances tried; 137 items in list
// 31 ground instances tried; 144 items in list
// 31 ground instances tried; 144 items in list
// 32 ground instances tried; 148 items in list
// 33 ground instances tried; 152 items in list
// 34 ground instances tried; 156 items in list
// 35 ground instances tried; 160 items in list
// 36 ground instances tried; 164 items in list
// 37 ground instances tried; 168 items in list
// 38 ground instances tried; 172 items in list
// 39 ground instances tried; 176 items in list
//
// val p36 : int = 3
let p36 = davisputnam' (parse "(forall x. exists y. P(x,y)) 
/\ (forall x. exists y. G(x,y)) 
/\ (forall x y. P(x,y) \/ G(x,y) ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
==> (forall x. exists y. H(x,y))");;

// 0 ground instances tried; 0 items in list
// 0 ground instances tried; 0 items in list
// 1 ground instances tried; 31 items in list
// 2 ground instances tried; 41 items in list
// 3 ground instances tried; 51 items in list
// 4 ground instances tried; 61 items in list
// 5 ground instances tried; 71 items in list
// 6 ground instances tried; 81 items in list
// 7 ground instances tried; 91 items in list
// 8 ground instances tried; 101 items in list
// 9 ground instances tried; 111 items in list
// 10 ground instances tried; 121 items in list
// 11 ground instances tried; 131 items in list
// 12 ground instances tried; 141 items in list
// 13 ground instances tried; 151 items in list
// 14 ground instances tried; 161 items in list
// 15 ground instances tried; 171 items in list
// 16 ground instances tried; 181 items in list
// 17 ground instances tried; 191 items in list
// 18 ground instances tried; 201 items in list
// 19 ground instances tried; 211 items in list
// 20 ground instances tried; 221 items in list
// 21 ground instances tried; 231 items in list
// 22 ground instances tried; 241 items in list
// 23 ground instances tried; 251 items in list
// 24 ground instances tried; 261 items in list
// 25 ground instances tried; 271 items in list
// 26 ground instances tried; 281 items in list
// 27 ground instances tried; 291 items in list
// 28 ground instances tried; 301 items in list
// 29 ground instances tried; 311 items in list
// 30 ground instances tried; 321 items in list
// 31 ground instances tried; 331 items in list
// 32 ground instances tried; 341 items in list
// 33 ground instances tried; 351 items in list
// 34 ground instances tried; 361 items in list
// 35 ground instances tried; 371 items in list
// 36 ground instances tried; 381 items in list
// 37 ground instances tried; 391 items in list
// 38 ground instances tried; 393 items in list
// 39 ground instances tried; 396 items in list
// 40 ground instances tried; 399 items in list
// 41 ground instances tried; 402 items in list
// 42 ground instances tried; 405 items in list
// 43 ground instances tried; 407 items in list
// 44 ground instances tried; 410 items in list
// 45 ground instances tried; 414 items in list
// 46 ground instances tried; 418 items in list
// 47 ground instances tried; 422 items in list
// 48 ground instances tried; 426 items in list
// 49 ground instances tried; 429 items in list
// 50 ground instances tried; 433 items in list
// 51 ground instances tried; 437 items in list
// 52 ground instances tried; 441 items in list
// 53 ground instances tried; 445 items in list
// 54 ground instances tried; 449 items in list
// 55 ground instances tried; 452 items in list
// 56 ground instances tried; 456 items in list
// 57 ground instances tried; 460 items in list
// 58 ground instances tried; 464 items in list
// 59 ground instances tried; 468 items in list
// 60 ground instances tried; 472 items in list
// 61 ground instances tried; 475 items in list
// 62 ground instances tried; 479 items in list
// 63 ground instances tried; 483 items in list
// 64 ground instances tried; 487 items in list
// 65 ground instances tried; 491 items in list
// 66 ground instances tried; 495 items in list
// 67 ground instances tried; 498 items in list
// 68 ground instances tried; 502 items in list
// 69 ground instances tried; 506 items in list
// 70 ground instances tried; 510 items in list
// 71 ground instances tried; 514 items in list
// 72 ground instances tried; 518 items in list
// 73 ground instances tried; 528 items in list
// 74 ground instances tried; 530 items in list
// 75 ground instances tried; 532 items in list
// 76 ground instances tried; 535 items in list
// 77 ground instances tried; 538 items in list
// 78 ground instances tried; 541 items in list
// 79 ground instances tried; 543 items in list
// 80 ground instances tried; 545 items in list
// 81 ground instances tried; 547 items in list
// 82 ground instances tried; 550 items in list
// 83 ground instances tried; 553 items in list
// 84 ground instances tried; 556 items in list
// 85 ground instances tried; 558 items in list
// 86 ground instances tried; 560 items in list
// 87 ground instances tried; 563 items in list
// 88 ground instances tried; 567 items in list
// 89 ground instances tried; 571 items in list
// 90 ground instances tried; 575 items in list
// 91 ground instances tried; 578 items in list
// 92 ground instances tried; 581 items in list
// 93 ground instances tried; 585 items in list
// 94 ground instances tried; 589 items in list
// 95 ground instances tried; 593 items in list
// 96 ground instances tried; 597 items in list
// 97 ground instances tried; 600 items in list
// 98 ground instances tried; 603 items in list
// 99 ground instances tried; 607 items in list
// 100 ground instances tried; 611 items in list
// 101 ground instances tried; 615 items in list
// 102 ground instances tried; 619 items in list
// 103 ground instances tried; 622 items in list
// 104 ground instances tried; 625 items in list
// 105 ground instances tried; 629 items in list
// 106 ground instances tried; 633 items in list
// 107 ground instances tried; 637 items in list
// 108 ground instances tried; 641 items in list
// 109 ground instances tried; 651 items in list
// 110 ground instances tried; 653 items in list
// 111 ground instances tried; 655 items in list
// 112 ground instances tried; 657 items in list
// 113 ground instances tried; 660 items in list
// 114 ground instances tried; 663 items in list
// 115 ground instances tried; 665 items in list
// 116 ground instances tried; 667 items in list
// 117 ground instances tried; 669 items in list
// 118 ground instances tried; 671 items in list
// 119 ground instances tried; 674 items in list
// 120 ground instances tried; 677 items in list
// 121 ground instances tried; 679 items in list
// 122 ground instances tried; 681 items in list
// 123 ground instances tried; 683 items in list
// 124 ground instances tried; 685 items in list
// 125 ground instances tried; 688 items in list
// 126 ground instances tried; 691 items in list
// 127 ground instances tried; 693 items in list
// 128 ground instances tried; 695 items in list
// 129 ground instances tried; 697 items in list
// 130 ground instances tried; 700 items in list
// 131 ground instances tried; 704 items in list
// 132 ground instances tried; 708 items in list
// 133 ground instances tried; 711 items in list
// 134 ground instances tried; 714 items in list
// 135 ground instances tried; 717 items in list
// 136 ground instances tried; 721 items in list
// 137 ground instances tried; 725 items in list
// 138 ground instances tried; 729 items in list
// 139 ground instances tried; 732 items in list
// 140 ground instances tried; 735 items in list
// 141 ground instances tried; 738 items in list
// 142 ground instances tried; 742 items in list
// 143 ground instances tried; 746 items in list
// 144 ground instances tried; 750 items in list
// 145 ground instances tried; 760 items in list
// 146 ground instances tried; 762 items in list
// 147 ground instances tried; 764 items in list
// 148 ground instances tried; 766 items in list
// 149 ground instances tried; 768 items in list
// 150 ground instances tried; 771 items in list
// 151 ground instances tried; 773 items in list
// 152 ground instances tried; 775 items in list
// 153 ground instances tried; 777 items in list
// 154 ground instances tried; 779 items in list
// 155 ground instances tried; 781 items in list
// 156 ground instances tried; 784 items in list
// 157 ground instances tried; 786 items in list
// 158 ground instances tried; 788 items in list
// 159 ground instances tried; 790 items in list
// 160 ground instances tried; 792 items in list
// 161 ground instances tried; 794 items in list
// 162 ground instances tried; 797 items in list
// 163 ground instances tried; 799 items in list
// 164 ground instances tried; 801 items in list
// 165 ground instances tried; 803 items in list
// 166 ground instances tried; 805 items in list
// 167 ground instances tried; 807 items in list
// 168 ground instances tried; 810 items in list
// 169 ground instances tried; 812 items in list
// 170 ground instances tried; 814 items in list
// 171 ground instances tried; 816 items in list
// 172 ground instances tried; 818 items in list
// 173 ground instances tried; 821 items in list
// 174 ground instances tried; 825 items in list
// 175 ground instances tried; 828 items in list
// 176 ground instances tried; 831 items in list
// 177 ground instances tried; 834 items in list
// 178 ground instances tried; 837 items in list
// 179 ground instances tried; 841 items in list
// 180 ground instances tried; 845 items in list
// 
// val p29 : int = 5
let p29 = davisputnam' (parse "(exists x. P(x)) /\ (exists x. G(x)) ==>
((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
(forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))");;
