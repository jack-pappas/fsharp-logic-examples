Logic Programming in F#
===
### Code and Examples from John Harrison's "[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html)"

---

### Purpose

[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html) is a book designed to teach the fundamental aspects of propositional logic, automated theorem proving, and proof assistants. It includes a large number of examples written in OCaml, which we have translated and adapted to F# in order to take advantage of Visual Studio and the .NET Framework.

Our ported F# code aims to stay as close as possible to the original OCaml to make it easy to follow along with the book.

---

### Setup / Installation ###

There are two solutions: `*.VS10.sln` and `*.VS11.sln` for Visual Studio 2010 and Visual Studio 2012, respectively.
Both solutions target .NET 4.0.

[NuGet](http://nuget.org) is used to manage external packages; the easiest way to [install NuGet](http://visualstudiogallery.msdn.microsoft.com/27077b70-9dad-4c64-adcf-c7cf6bc9970c) is by downloading it (for free) from the [Visual Studio Extension Gallery](http://visualstudiogallery.msdn.microsoft.com/27077b70-9dad-4c64-adcf-c7cf6bc9970c). If you do not have NuGet, or are running a version prior to `2.0`, you *must* install it (or upgrade) before you will be able to build the projects.

The solution uses the *Package Restore* feature of NuGet to automatically download any missing packages when the project is built. This requires that you have the "[Allow NuGet to download missing packages during build](http://docs.nuget.org/docs/workflows/using-nuget-without-committing-packages)" setting enabled; in Visual Studio, you can find the setting under `Options -> Package Manager -> General`.

Once NuGet is installed and configured, you should be able to build the solution.

### When reading along with the book ###

The OCaml code from [resource page](http://www.cl.cam.ac.uk/~jrh13/atp/) combines the code and examples in one script. We have separated them in our ported F# code to simplify development and testing; all library code has been placed into the `FSharpx.Books.AutomatedReasoning` project, and the examples put into F# scripts (`.fsx`) in the `Examples` folder.

In the book, OCaml code and example scripts are identified by bounding boxes. Example code typically starts with an `#`, indicating it is being run in the OCaml REPL; the ported code for these are typically found in the Examples directory and code without the # is typically found in the library project.

### Running Examples ###

To run the examples you must have built the solution first.

The Examples are broken down into script files based on the name of the original OCaml file. The examples appear sequentially as they appear in the book and we include page numbers from the book as comments in the examples to make cross-referencing easier.

When first opening an example script file, run the #load, open and fsi.AddPriter statements at the top of the script file to setup the interactive environment for the following examples.

It is suggested that when running the examples that you run each one separately so as not to lose track of which example produced which result. Some of the examples rely on statements earlier in the script so if you skip ahead you may get errors.

Since the examples are for demonstrating certain aspects of automated reasoning and automated reasoning is an ongoing science, some of the examples will demonstrate failures with a failure, exception, or never returning.  

Additionally automated reasoning is based on AI techniques and the search for the solution can be fast, slow, not be found with a computer due to limited resources such as stack space, not finish in a reasonable amount of time such as a day, or not even know if a solution can be found with this code. So when running the examples we have tried to provide as much feedback as possible on what to expect, but sometimes we just have to give up during the running of the example.  

The feedback takes the following form for each example run:

  1. Under 10 seconds - no comment.
  2. more than 10 seconds and completes - result of FSI #time;; directive. i.e. Real: 02:37:35.586, CPU: 02:37:31.718, GC gen0: 50200, gen1: 1376, gen2: 98.
  3. More than several minutes and we gave up on letting it finish - comment with long running.
  4. Exception - comment noting expected exception.
  5. Failure - comment noting expected failure reason.


### Unit Testing ###

The `FSharpx.Books.AutomatedReasoning.Tests` project contains all of the examples from the book (plus some additional examples from John Harrison's website), converted into unit test cases with **NUnit 2.6.1** and **FsUnit**.

You can execute the tests by building the `FSharpx.Books.AutomatedReasoning.Tests` project, then loading the compiled assembly into a test runner like **NUnit GUI** or **TestDriven.NET 3.4.2803 (Beta 3)**.

*We strongly recommend using the x86 versions of the test runners.* The CLR's default maximum stack size of 1MB is enough for 32-bit processes, but the test cases reliably crash with a `StackOverflowException` on a 64-bit process. This is because many of the library functions are recursive, but not *tail-recursive* -- and since many types double in size on an x64 platform, these functions quickly consume the stack and crash the process.

NOTE: On a 64-bit machine, the NUnit installer only creates a Start Menu shortcut for the 64-bit version so you must create your own shortcut (e.g., on the Desktop) to the x86 version; the x86 version is normally found at `C:\Program Files (x86)\NUnit 2.6.1\bin\nunit-x86.exe`.

Once you have installed NUnit, built the `FSharpx.Books.AutomatedReasoning.Tests` project, and opened the NUnit (x86) GUI, follow these steps to run the tests:

  1. In the NUnit GUI, go to `File -> Open Project`. Find the `FSharpx.Books.AutomatedReasoning.Tests.dll` in the `FSharpx.Books.AutomatedReasoning.Tests\bin\Debug` folder in your repository folder (i.e., the folder you cloned the repository into). Double-click the file, or select it and press the 'Open' button.
  2. Click the *Categories* tab on left side of the NUnit GUI window.
  3. Double-click 'LongRunning', then check the box labeled *Exclude these categories*.
  4. Click the *Tests* tab on left side of the NUnit GUI window and press the 'Run' button.

### Interesting changes from OCaml to F# ###

- OCaml exceptions changed to F# `'T option`.
  
    This only works sometimes -- when the exception doesn't return any (useful) information. When the exception does return information, it's necessary to use `Choice<_,_>`. Also, changing functions to use `'T option` or `Choice<_,_>` instead of exceptions can also alter their type signatures, which can cause the code to suddenly fail to compile.
- Preprocessors i.e. [camlp4 / camlp5](http://caml.inria.fr/pub/docs/tutorial-camlp4/tutorial004.html) don't exist in F#.
Since F# does not support the OCaml French-style \<\< quotation \>\>,
the parser will be explicitly invoked.
As such the use of default_parser and default_printer does not appear in the F# code.

        // OCaml:
        <<x + 3 * y>>;;
        // F#: 
        parse_exp "x + 3 * y";;
        // OCaml: 
        <<p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)>>;;
        // F#: 
        parse_prop_formula "p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)";;

- Duplicated names are avoided.
Since OCaml shadows names and F# does not allow duplicate names, any function name causing a duplicate name error will have the name appended with an increasing sequential number.

         // OCaml:  
         let a = ...;; let a = ...;; let a = ...;;
         // F#: 
         let a001 = ...;; let a002 = ...;; let a003 = ...;;
For some of the test strings such as in tableaux.fsx, the same name is used multiple times. To avoid duplicate name errors some of the names have a character appended.

         // OCaml: 
         let p20 = prawitx ...;; let p20 = compare ...;;  let p20 = splittab ...;;
         // F#:   
         let p20p = prawitx ...;; let p20c = compare ...;; let p20s = splittab ...;;

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

### Writing unit tests ###
A large set of unit tests is created based on available examples. 
These test cases serve as an **evidence** of correctness when the code base is updated or optimized over time. 
There are a few problems on implementing test cases though:
 - NUnit only accepts parameterized tests on primitive types. To compare sophisticated values, we have to put them into arrays and use indices as test parameters.
 - FsUnit uses type test to implement its DSL. Type inference doesn't work on this DSL, so make sure that two compared values belong to the same type.
 - FsUnit and the library have some clashed constraints, namely `True` and `False`. To create tests correctly, one might need to use detailed type annotation, such as `formula<fol>.True` and `formula<fol>.False` for literals in first-order logic.
 - A few slow tests are put into `LongRunning` category. They aren't recommended to run on the development basis. Their purposes are to validate the project upon release.
