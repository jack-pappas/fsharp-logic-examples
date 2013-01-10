// ========================================================================= //
// Copyright (c) 2003-2007, John Harrison.                                   //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

#load "initialization.fsx"

open FSharpx.Books.AutomatedReasoning.fol
open FSharpx.Books.AutomatedReasoning.lcf
open FSharpx.Books.AutomatedReasoning.folderived

fsi.AddPrinter sprint_thm

// pg. 490
// ------------------------------------------------------------------------- //
// Example.                                                                  //
// ------------------------------------------------------------------------- //

// folderived.p001
icongruence (parset @"s") (parset @"t") (parset @"f(s,g(s,t,s),u,h(h(s)))")
                            (parset @"f(s,g(t,t,s),u,h(h(t)))");;
    
// pg. 494
// ------------------------------------------------------------------------- //
// An example.                                                               //
// ------------------------------------------------------------------------- //

// folderived.p002
ispec (parset @"y") (parse @"forall x y z. x + y + z = z + y + x");;

// ------------------------------------------------------------------------- //
// Additional tests not in main text.                                        //
// ------------------------------------------------------------------------- //

// folderived.p003
isubst (parset @"x + x") (parset @"2 * x")
        (parse @"x + x = x ==> x = 0") (parse @"2 * x = x ==> x = 0");;

// folderived.p004
isubst (parset @"x + x")  (parset @"2 * x")
        (parse @"(x + x = y + y) ==> (y + y + y = x + x + x)")
        (parse @"2 * x = y + y ==> y + y + y = x + 2 * x");;

// folderived.p005
ispec (parset @"x") (parse @"forall x y z. x + y + z = y + z + z");;

// folderived.p006
ispec (parset @"x") (parse @"forall x. x = x");;

// folderived.p007
ispec (parset @"w + y + z") (parse @"forall x y z. x + y + z = y + z + z");;

// folderived.p008
ispec (parset @"x + y + z") (parse @"forall x y z. x + y + z = y + z + z");;

// folderived.p009
ispec (parset @"x + y + z") (parse @"forall x y z. nothing_much");;

// folderived.p010
isubst (parset @"x + x") (parset @"2 * x")
        (parse @"(x + x = y + y) <=> (something \/ y + y + y = x + x + x)")
        (parse @"(2 * x = y + y) <=> (something \/ y + y + y = x + x + x)");;

// folderived.p011
isubst (parset @"x + x")  (parset @"2 * x")
        (parse @"(exists x. x = 2) <=> exists y. y + x + x = y + y + y")
        (parse @"(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)");;

// folderived.p012
isubst (parset @"x")  (parset @"y")
        (parse @"(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)")
        (parse @"(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)");;

// ------------------------------------------------------------------------- //
// The bug is now fixed.                                                     //
// ------------------------------------------------------------------------- //

// folderived.p013
ispec (parset @"x'") (parse @"forall x x' x''. x + x' + x'' = 0");;

// folderived.p014
ispec (parset @"x''") (parse @"forall x x' x''. x + x' + x'' = 0");;

// folderived.p015
ispec (parset @"x' + x''") (parse @"forall x x' x''. x + x' + x'' = 0");;

// folderived.p016
ispec (parset @"x + x' + x''") (parse @"forall x x' x''. x + x' + x'' = 0");;

// folderived.p017
ispec (parset @"2 * x") (parse @"forall x x'. x + x' = x' + x");;