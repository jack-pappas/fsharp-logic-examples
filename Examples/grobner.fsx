// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.lib
open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.complex
open FSharpx.Books.AutomatedReasoning.grobner

// pg. 413
// ------------------------------------------------------------------------- //
// Examples.                                                                 //
// ------------------------------------------------------------------------- //

// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// val it : bool = true
grobner_decide (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0");;

// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 4 pairs
// 4 basis elements and 3 pairs
// 4 basis elements and 2 pairs
// 4 basis elements and 1 pairs
// 4 basis elements and 0 pairs
// val it : bool = false
grobner_decide (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0");;

// 4 basis elements and 6 pairs
// 5 basis elements and 9 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 9 basis elements and 29 pairs
// 9 basis elements and 28 pairs
// 10 basis elements and 36 pairs
// 11 basis elements and 45 pairs
// 12 basis elements and 55 pairs
// 13 basis elements and 66 pairs
// 13 basis elements and 65 pairs
// 14 basis elements and 77 pairs
// 15 basis elements and 90 pairs
// 16 basis elements and 104 pairs
// 16 basis elements and 103 pairs
// 17 basis elements and 118 pairs
// 18 basis elements and 134 pairs
// 19 basis elements and 151 pairs
// 4 basis elements and 6 pairs
// 5 basis elements and 9 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 10 basis elements and 38 pairs
// 11 basis elements and 47 pairs
// 12 basis elements and 57 pairs
// 13 basis elements and 68 pairs
// 14 basis elements and 80 pairs
// 15 basis elements and 93 pairs
// 15 basis elements and 92 pairs
// 16 basis elements and 106 pairs
// 17 basis elements and 121 pairs
// 18 basis elements and 137 pairs
// 18 basis elements and 136 pairs
// 19 basis elements and 153 pairs
// 20 basis elements and 171 pairs
// 21 basis elements and 190 pairs
// val it : bool = true
grobner_decide (parse @"(a * x^2 + b * x + c = 0) /\ (a * y^2 + b * y + c = 0) /\ ~(x = y)  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;

// ------------------------------------------------------------------------- //
// Compare with earlier procedure.                                           //
// ------------------------------------------------------------------------- //

let fm = (parse @"(a * x^2 + b * x + c = 0) /\ (a * y^2 + b * y + c = 0) /\  ~(x = y) ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
time complex_qelim (generalize fm),time grobner_decide fm;;
        
    // ------------------------------------------------------------------------- //
    // More tests.                                                               //
    // ------------------------------------------------------------------------- //

// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// CPU time (user): 0.000724
// val it : bool = true
time grobner_decide  (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0");;

// 3 basis elements and 3 pairs
// 3 basis elements and 2 pairs
// 4 basis elements and 3 pairs
// 4 basis elements and 4 pairs
// 4 basis elements and 2 pairs
// 4 basis elements and 1 pairs
// 4 basis elements and 0 pairs
// CPU time (user): 0.014134
// val it : bool = false
time grobner_decide  (parse @"a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0");;

// 4 basis elements and 6 pairs
// 5 basis elements and 9 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 9 basis elements and 29 pairs
// 9 basis elements and 28 pairs
// 10 basis elements and 36 pairs
// 11 basis elements and 45 pairs
// 12 basis elements and 55 pairs
// 13 basis elements and 66 pairs
// 13 basis elements and 65 pairs
// 14 basis elements and 77 pairs
// 15 basis elements and 90 pairs
// 16 basis elements and 104 pairs
// 16 basis elements and 103 pairs
// 17 basis elements and 118 pairs
// 18 basis elements and 134 pairs
// 19 basis elements and 151 pairs
// 4 basis elements and 6 pairs
// 5 basis elements and 9 pairs
// 5 basis elements and 8 pairs
// 6 basis elements and 12 pairs
// 7 basis elements and 17 pairs
// 8 basis elements and 23 pairs
// 9 basis elements and 30 pairs
// 10 basis elements and 38 pairs
// 11 basis elements and 47 pairs
// 12 basis elements and 57 pairs
// 13 basis elements and 68 pairs
// 14 basis elements and 80 pairs
// 15 basis elements and 93 pairs
// 15 basis elements and 92 pairs
// 16 basis elements and 106 pairs
// 17 basis elements and 121 pairs
// 18 basis elements and 137 pairs
// 18 basis elements and 136 pairs
// 19 basis elements and 153 pairs
// 20 basis elements and 171 pairs
// 21 basis elements and 190 pairs
// CPU time (user): 0.045882
// val it : bool = true
time grobner_decide (parse @"(a * x^2 + b * x + c = 0) /\ (a * y^2 + b * y + c = 0) /\ ~(x = y) ==> (a * x * y = c) /\ (a * (x + y) + b = 0)");;
time grobner_decide (parse @"(y_1 = 2 * y_3) /\ (y_2 = 2 *
                 y_4) /\ (y_1 * y_3 = y_2 * y_4) ==> (y_1^2 = y_2^2)");;


time grobner_decide (parse @"(x1 = u3) /\ (x1 * (u2 - u1) = x2 * u3) /\ (x4 * (x2 - u1) = x1 * (x3 - u1)) /\ (x3 * u3 = x4 * u2) /\ ~(u1 = 0) /\ ~(u3 = 0) ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)");;

time grobner_decide (parse @"(u1 * x1 - u1 * u3 = 0) /\ (u3 * x2 - (u2 - u1) * x1 = 0) /\ (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\ (u3 * x4 - u2 * x3 = 0) /\  ~(u1 = 0) /\ ~(u3 = 0) ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)");;

//** Checking resultants (in one direction) **//

time grobner_decide (parse @"a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0 ==> 4*a^2*c-b^2*a = 0");;

//3 basis elements and 3 pairs
//4 basis elements and 5 pairs
//5 basis elements and 8 pairs
//6 basis elements and 12 pairs
//6 basis elements and 11 pairs
//7 basis elements and 16 pairs
//7 basis elements and 15 pairs
//8 basis elements and 21 pairs
//9 basis elements and 28 pairs
//10 basis elements and 36 pairs
//11 basis elements and 45 pairs
//12 basis elements and 55 pairs
//13 basis elements and 66 pairs
//13 basis elements and 65 pairs
//14 basis elements and 77 pairs
//15 basis elements and 90 pairs
//16 basis elements and 104 pairs
//16 basis elements and 103 pairs
//16 basis elements and 102 pairs
//16 basis elements and 101 pairs
//16 basis elements and 100 pairs
//CPU time (user): 0.011039
//val it : bool = true
time grobner_decide (parse @"a * x^2 + b * x + c = 0 /\ d * x + e = 0 ==> d^2*c-e*d*b+a*e^2 = 0");;

//3 basis elements and 3 pairs
//4 basis elements and 5 pairs
//5 basis elements and 8 pairs
//6 basis elements and 12 pairs
//7 basis elements and 17 pairs
//8 basis elements and 23 pairs
//9 basis elements and 30 pairs
//10 basis elements and 38 pairs
//11 basis elements and 47 pairs
//12 basis elements and 57 pairs
//13 basis elements and 68 pairs
//14 basis elements and 80 pairs
//15 basis elements and 93 pairs
//16 basis elements and 107 pairs
//17 basis elements and 122 pairs
//18 basis elements and 138 pairs
//19 basis elements and 155 pairs
//20 basis elements and 173 pairs
//20 basis elements and 172 pairs
//21 basis elements and 191 pairs
//21 basis elements and 190 pairs
//22 basis elements and 210 pairs
//23 basis elements and 231 pairs
//24 basis elements and 253 pairs
//24 basis elements and 252 pairs
//25 basis elements and 275 pairs
//25 basis elements and 274 pairs
//25 basis elements and 273 pairs
//26 basis elements and 297 pairs
//27 basis elements and 322 pairs
//27 basis elements and 321 pairs
//27 basis elements and 320 pairs
//27 basis elements and 319 pairs
//27 basis elements and 318 pairs
//27 basis elements and 317 pairs
//28 basis elements and 343 pairs
//29 basis elements and 370 pairs
//29 basis elements and 369 pairs
//29 basis elements and 368 pairs
//29 basis elements and 367 pairs
//29 basis elements and 366 pairs
//29 basis elements and 365 pairs
//30 basis elements and 393 pairs
//31 basis elements and 422 pairs
//32 basis elements and 452 pairs
//32 basis elements and 451 pairs
//32 basis elements and 450 pairs
//32 basis elements and 449 pairs
//33 basis elements and 480 pairs
//33 basis elements and 479 pairs
//33 basis elements and 478 pairs
//34 basis elements and 510 pairs
//34 basis elements and 509 pairs
//35 basis elements and 542 pairs
//35 basis elements and 541 pairs
//35 basis elements and 540 pairs
//35 basis elements and 539 pairs
//36 basis elements and 573 pairs
//36 basis elements and 572 pairs
//36 basis elements and 571 pairs
//36 basis elements and 570 pairs
//36 basis elements and 569 pairs
//36 basis elements and 568 pairs
//36 basis elements and 567 pairs
//37 basis elements and 602 pairs
//37 basis elements and 601 pairs
//37 basis elements and 600 pairs
//37 basis elements and 599 pairs
//37 basis elements and 598 pairs
//37 basis elements and 597 pairs
//37 basis elements and 596 pairs
//37 basis elements and 595 pairs
//37 basis elements and 594 pairs
//37 basis elements and 593 pairs
//37 basis elements and 592 pairs
//37 basis elements and 591 pairs
//37 basis elements and 590 pairs
//37 basis elements and 589 pairs
//38 basis elements and 625 pairs
//38 basis elements and 624 pairs
//38 basis elements and 623 pairs
//38 basis elements and 622 pairs
//38 basis elements and 621 pairs
//38 basis elements and 620 pairs
//38 basis elements and 619 pairs
//38 basis elements and 618 pairs
//38 basis elements and 617 pairs
//38 basis elements and 616 pairs
//38 basis elements and 615 pairs
//38 basis elements and 614 pairs
//38 basis elements and 613 pairs
//38 basis elements and 612 pairs
//38 basis elements and 611 pairs
//38 basis elements and 610 pairs
//38 basis elements and 609 pairs
//38 basis elements and 608 pairs
//38 basis elements and 607 pairs
//38 basis elements and 606 pairs
//38 basis elements and 605 pairs
//38 basis elements and 604 pairs
//38 basis elements and 603 pairs
//38 basis elements and 602 pairs
//38 basis elements and 601 pairs
//38 basis elements and 600 pairs
//38 basis elements and 599 pairs
//38 basis elements and 598 pairs
//38 basis elements and 597 pairs
//38 basis elements and 596 pairs
//38 basis elements and 595 pairs
//38 basis elements and 594 pairs
//38 basis elements and 593 pairs
//38 basis elements and 592 pairs
//38 basis elements and 591 pairs
//38 basis elements and 590 pairs
//38 basis elements and 589 pairs
//38 basis elements and 588 pairs
//38 basis elements and 587 pairs
//38 basis elements and 586 pairs
//38 basis elements and 585 pairs
//38 basis elements and 584 pairs
//38 basis elements and 583 pairs
//38 basis elements and 582 pairs
//38 basis elements and 581 pairs
//38 basis elements and 580 pairs
//38 basis elements and 579 pairs
//38 basis elements and 578 pairs
//38 basis elements and 577 pairs
//38 basis elements and 576 pairs
//38 basis elements and 575 pairs
//38 basis elements and 574 pairs
//38 basis elements and 573 pairs
//38 basis elements and 572 pairs
//38 basis elements and 571 pairs
//38 basis elements and 570 pairs
//38 basis elements and 569 pairs
//38 basis elements and 568 pairs
//38 basis elements and 567 pairs
//38 basis elements and 566 pairs
//38 basis elements and 565 pairs
//38 basis elements and 564 pairs
//38 basis elements and 563 pairs
//38 basis elements and 562 pairs
//38 basis elements and 561 pairs
//38 basis elements and 560 pairs
//38 basis elements and 559 pairs
//39 basis elements and 596 pairs
//40 basis elements and 634 pairs
//40 basis elements and 633 pairs
//40 basis elements and 632 pairs
//40 basis elements and 631 pairs
//40 basis elements and 630 pairs
//40 basis elements and 629 pairs
//40 basis elements and 628 pairs
//41 basis elements and 667 pairs
//41 basis elements and 666 pairs
//41 basis elements and 665 pairs
//41 basis elements and 664 pairs
//41 basis elements and 663 pairs
//41 basis elements and 662 pairs
//41 basis elements and 661 pairs
//41 basis elements and 660 pairs
//41 basis elements and 659 pairs
//41 basis elements and 658 pairs
//41 basis elements and 657 pairs
//42 basis elements and 697 pairs
//42 basis elements and 696 pairs
//42 basis elements and 695 pairs
//43 basis elements and 736 pairs
//43 basis elements and 735 pairs
//43 basis elements and 734 pairs
//44 basis elements and 776 pairs
//44 basis elements and 775 pairs
//44 basis elements and 774 pairs
//44 basis elements and 773 pairs
//44 basis elements and 772 pairs
//44 basis elements and 771 pairs
//44 basis elements and 770 pairs
//44 basis elements and 769 pairs
//44 basis elements and 768 pairs
//44 basis elements and 767 pairs
//44 basis elements and 766 pairs
//44 basis elements and 765 pairs
//44 basis elements and 764 pairs
//44 basis elements and 763 pairs
//44 basis elements and 762 pairs
//44 basis elements and 761 pairs
//44 basis elements and 760 pairs
//44 basis elements and 759 pairs
//44 basis elements and 758 pairs
//44 basis elements and 757 pairs
//45 basis elements and 800 pairs
//45 basis elements and 799 pairs
//45 basis elements and 798 pairs
//45 basis elements and 797 pairs
//45 basis elements and 796 pairs
//45 basis elements and 795 pairs
//45 basis elements and 794 pairs
//45 basis elements and 793 pairs
//45 basis elements and 792 pairs
//45 basis elements and 791 pairs
//45 basis elements and 790 pairs
//45 basis elements and 789 pairs
//45 basis elements and 788 pairs
//45 basis elements and 787 pairs
//45 basis elements and 786 pairs
//45 basis elements and 785 pairs
//45 basis elements and 784 pairs
//45 basis elements and 783 pairs
//45 basis elements and 782 pairs
//45 basis elements and 781 pairs
//CPU time (user): 0.139069
//val it : bool = true
time grobner_decide (parse @"a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0 ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0");;

//***** Seems a bit too lengthy?

time grobner_decide (parse @"a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0 ==> e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0");;

 //*******//

//********* Works correctly, but it's lengthy

time grobner_decide (parse @" (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\ (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2 /\ (x1 - x0')^2 + (y1 - y0')^2 = (x2 - x0')^2 + (y2 - y0')^2 /\ (x2 - x0')^2 + (y2 - y0')^2 = (x3 - x0')^2 + (y3 - y0')^2 ==> x0 = x0' /\ y0 = y0'");;

//**** Corrected with non-isotropy conditions; even lengthier
       
time grobner_decide (parse @"(x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\ (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2 /\ (x1 - x0')^2 + (y1 - y0')^2 = (x2 - x0')^2 + (y2 - y0')^2 /\ (x2 - x0')^2 + (y2 - y0')^2 = (x3 - x0')^2 + (y3 - y0')^2 /\ ~((x1 - x0)^2 + (y1 - y0)^2 = 0) /\ ~((x1 - x0')^2 + (y1 - y0')^2 = 0) ==> x0 = x0' /\ y0 = y0'");;

//*** Maybe this is more efficient? (No?)
        
time grobner_decide (parse @"(x1 - x0)^2 + (y1 - y0)^2 = d /\ (x2 - x0)^2 + (y2 - y0)^2 = d /\ (x3 - x0)^2 + (y3 - y0)^2 = d /\ (x1 - x0')^2 + (y1 - y0')^2 = e /\ (x2 - x0')^2 + (y2 - y0')^2 = e /\ (x3 - x0')^2 + (y3 - y0')^2 = e /\ ~(d = 0) /\ ~(e = 0) ==> x0 = x0' /\ y0 = y0'");;

//**********//

// ------------------------------------------------------------------------- //
// Inversion of homographic function (from Gosper's CF notes).               //
// ------------------------------------------------------------------------- //

//2 basis elements and 1 pairs
//CPU time (user): 0.000426
//val it : bool = true
time grobner_decide (parse @"y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y");;

// ------------------------------------------------------------------------- //
// Manual "sums of squares" for 0 <= a /\ a <= b ==> a^3 <= b^3.             //
// ------------------------------------------------------------------------- //

time complex_qelim (parse @"forall a b c d e. a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0 ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 = 0");;

//4 basis elements and 6 pairs
//4 basis elements and 5 pairs
//4 basis elements and 4 pairs
//CPU time (user): 0.012950
//val it : bool = true
time grobner_decide (parse @"a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0 ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 = 0");;

// ------------------------------------------------------------------------- //
// Special case of a = 1, i.e. 1 <= b ==> 1 <= b^3                           //
// ------------------------------------------------------------------------- //

time complex_qelim (parse @"forall b d e.  b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0 ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0");;

//3 basis elements and 3 pairs
//3 basis elements and 2 pairs
//CPU time (user): 0.001556
//val it : bool = true
time grobner_decide (parse @"b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0 ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0");;

// ------------------------------------------------------------------------- //
// Converse, 0 <= a /\ a^3 <= b^3 ==> a <= b                                 //
//                                                                           //
// This derives b <= 0, but not a full solution.                             //
// ------------------------------------------------------------------------- //

//4 basis elements and 6 pairs
//4 basis elements and 5 pairs
//4 basis elements and 4 pairs
//4 basis elements and 3 pairs
//5 basis elements and 6 pairs
//6 basis elements and 10 pairs
//7 basis elements and 15 pairs
//7 basis elements and 14 pairs
//8 basis elements and 20 pairs
//8 basis elements and 19 pairs
//CPU time (user): 0.003743
//val it : bool = true
time grobner_decide (parse @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0");;

// ------------------------------------------------------------------------- //
// Here are further steps towards a solution, step-by-step.                  //
// ------------------------------------------------------------------------- //

//4 basis elements and 6 pairs
//4 basis elements and 5 pairs
//4 basis elements and 4 pairs
//4 basis elements and 3 pairs
//5 basis elements and 6 pairs
//6 basis elements and 10 pairs
//7 basis elements and 15 pairs
//7 basis elements and 14 pairs
//8 basis elements and 20 pairs
//8 basis elements and 19 pairs
//CPU time (user): 0.023012
//val it : bool = true
time grobner_decide (parse @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)");;

//4 basis elements and 6 pairs
//4 basis elements and 5 pairs
//4 basis elements and 4 pairs
//4 basis elements and 3 pairs
//5 basis elements and 6 pairs
//6 basis elements and 10 pairs
//7 basis elements and 15 pairs
//7 basis elements and 14 pairs
//8 basis elements and 20 pairs
//8 basis elements and 19 pairs
//CPU time (user): 0.006227
//val it : bool = true
time grobner_decide (parse @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3");;

//4 basis elements and 6 pairs
//4 basis elements and 5 pairs
//4 basis elements and 4 pairs
//4 basis elements and 3 pairs
//5 basis elements and 6 pairs
//6 basis elements and 10 pairs
//7 basis elements and 15 pairs
//7 basis elements and 14 pairs
//8 basis elements and 20 pairs
//8 basis elements and 19 pairs
//CPU time (user): 0.005773
//val it : bool = true
time grobner_decide (parse @"a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0 ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0");;

// ------------------------------------------------------------------------- //
// A simpler one is ~(x < y /\ y < x), i.e. x < y ==> x <= y.                //
//                                                                           //
// Yet even this isn't completed!                                            //
// ------------------------------------------------------------------------- //

//3 basis elements and 3 pairs
//4 basis elements and 5 pairs
//5 basis elements and 8 pairs
//6 basis elements and 12 pairs
//7 basis elements and 17 pairs
//7 basis elements and 16 pairs
//CPU time (user): 0.021446
//val it : bool = true
time grobner_decide (parse @"(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0");;

// ------------------------------------------------------------------------- //
// Inspired by Cardano's formula for a cubic. This actually works worse than //
// with naive quantifier elimination (of course it's false...)               //
// ------------------------------------------------------------------------- //

//*****

time grobner_decide (parse @"t - u = n /\ 27 * t * u = m^3 /\ ct^3 = t /\ cu^3 = u /\ x = ct - cu ==> x^3 + m * x = n");;

//**********//

