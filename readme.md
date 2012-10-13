Logic Programming in F#
===
### Code and Examples from John Harrison's "[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html)"

---

### Purpose

The purpose this site is to allow someone to learn automated theorem provers and proof assistants using John's book but instead of using OCaml, they can use F#. While OCaml is a perfectly valid language, F# is a first class language of Visual Studio thus allowing one the use of a powerful Iteractive Development Environment.

When converting the code from OCaml to F# the main goal was to keep the F# code as close as possible to the OCaml code presented in the book so that one did not have to spend time trying to understand what code changes were made.


---

### Needed for Installation ###

There are two solutions: `*.VS10.sln` and `*.VS11.sln` for Visual Studio 2010 and Visual Studio 2012 respectively.
Both solutions are targeting .NET framework 4.0; while the VS10 version uses F# 2.0, the VS11 version targets F# 3.0.

We use NuGet to manage external packages, for example, NUnit/FsUnit for unit testing.
You will need to install [NuGet] (http://nuget.codeplex.com/) to get additional required libraries. 
After installing NuGet, make sure to enable "Allow NuGet to download missing packages during build". 
[This setting](http://docs.nuget.org/docs/workflows/using-nuget-without-committing-packages) is under Options -> Package Manager -> General.
You will have to build the application once you have NuGet installed and the solution opened in Visual Studio.

The test cases have been executed with *NUnit 2.6 x86* and *TestDriven.NET-3.4.2803* x86 test runners. 
**We recommend you to use x86 versions of the test runners.** 
Although 1MB stack limit is enough for 32-bit test processes, the test cases will soon result in `StackOverflowException` on a 64-bit process. 
The reason is that many library functions are *non-tail-recursive* and many types double their sizes on x64 platform.

### Instructions on running tests with NUnit ###

To run the unit test you will need to

1. Download and install NUnit
2. Download repository, unpack if necessary, open with Visual Studio 2010, and build the solution
4. Start NUnit x86 (Note: on 64-bit systems the system menu will use 64-bit version of NUnit. 
   The x86 version of NUnit is nunit-x86 which can be found in the NUnit bin directory)
5. Within NUnit *File -> Open Project*, navigate to directory with FSharpx.Books.AutomatedReasoning.Tests.dll
6. Double click FSharpx.Books.AutomatedReasoning.Tests.dll
9. Click *Categories* tab on left side of NUnit
10. Double click LongRunning, and select *Exclude these categories*
13. Click *Tests* tab on left side of NUnit and hit *Run*



### Interesting changes from OCaml to F# ###

- OCaml exceptions changed to F# `'T option`.
  
    This only works sometimes -- when the exception doesn't return any (useful) information. When the exception does return information, it's necessary to use `Choice<_,_>`. Also, changing functions to use `'T option` or `Choice<_,_>` instead of exceptions can also alter their type signatures, which can cause the code to suddenly fail to compile.
- Preprocessor doesn't exist. i.e. camlp4 / camlp5
- OCaml top-level commands such as #trace and #install-printer don't exist.

	The OCaml REPL directive:

		#install_printer my_printer;;

	has the equivalent F# (in F# interactive):

		fsi.AddPrinter my_printer;;		// my_printer : 'T -> string

### F# porting notes ###
 - Turned off the F# compiler warning `FS0025` (about incomplete pattern matches). These matches are found throughout the original OCaml code and eliminating them *correctly* would require extensive changes to the code; so, for compatibility purposes, the code has been left as-is and the warning disabled to promote readability.
 - Run a few examples with 16MB stack (the default limit set by OCaml version) using `runWithEnlargedStack` in `initialization.fsx`. 
These examples emit `StackOverflowException`s in F# on Windows due to small 1MB stack (see extensive discussion [here](http://stackoverflow.com/questions/7947446/why-does-f-impose-a-low-limit-on-stack-size)).
 - Redefined `Failure` active patterns to accommodate `KeyNotFoundException`, `ArgumentException`, etc. The OCaml version makes use of `Failure` as a control flow; the F# version throws different kinds of exceptions which weren't caught by default `Failure`. The active pattern might be updated to handle other exceptions later (see the detailed function in the beginning of `lib.fs`).

### OCaml Quotations

[OCaml Quotations](http://caml.inria.fr/pub/docs/tutorial-camlp4/tutorial004.html)

Since F# does not support the OCaml French-style \<\< quotation \>\>,
the parser will be explicitly invoked and the printer will be invoked via fsi.AddPrinter.  
As such the use of default_parser and default_printer does not appear in the F# code.

> OCaml: \<\<x + 3 * y\>\>;;

> F#: parse_exp "x + 3 * y";;

> OCaml: \<\<p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)\>\>;;

> F#: parse_prop_formula "p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)";;

### Duplicate names

Since OCaml shadows names and F# does not allow duplicate names, any function name causing a duplicate name error will have the name appended with an increasing sequential number.

> OCaml:  let a = ...;; let a = ...;; let a = ...;;

> F#: let a001 = ...;; let a002 = ...;; let a003 = ...;;

For some of the test strings such as in tableaux.fsx, the same name is used multiple times. To avoid duplicate name errors some of the names have a character appended.

> OCaml: let p20 = prawitx ...;; let p20 = compare ...;;  let p20 = splittab ...;;

> F#:   let p20p = prawitx ...;; let p20c = compare ...;; let p20s = splittab ...;;

 
### Writing unit tests ###
A large set of unit tests is created based on available examples. 
These test cases serve as an **evidence** of correctness when the code base is updated or optimized over time. 
There are a few problems on implementing test cases though:
 - NUnit only accepts parameterized tests on primitive types. To compare sophisticated values, we have to put them into arrays and use indices as test parameters.
 - FsUnit uses type test to implement its DSL. Type inference doesn't work on this DSL, so make sure that two compared values belong to the same type.
 - FsUnit and the library have some clashed constraints, namely `True` and `False`. To create tests correctly, one might need to use detailed type annotation, such as `formula<fol>.True` and `formula<fol>.False` for literals in first-order logic.
 - A few slow tests are put into `LongRunning` category. They aren't recommended to run on the development basis. Their purposes are to validate the project upon release.
