Logic Programming in F#
===
### Code and Examples from John Harrison's "[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html)" ###

---

### Purpose ###

[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html) is a book designed to teach the fundamental aspects of propositional logic, automated theorem proving, and proof assistants. It includes a large number of examples written in OCaml, which we have translated and adapted to F# in order to take advantage of Visual Studio and the .NET Framework.

Our ported F# code aims to stay as close as possible to the original OCaml to make it easy to follow along with the book.

---

### Setup / Installation ###

There are two solutions: `*.VS10.sln` and `*.VS11.sln` for Visual Studio 2010 and Visual Studio 2012, respectively.
Both solutions target .NET 4.0.

[NuGet](http://nuget.org) is used to manage external packages; the easiest way to [install NuGet](http://visualstudiogallery.msdn.microsoft.com/27077b70-9dad-4c64-adcf-c7cf6bc9970c) is by downloading it (for free) from the [Visual Studio Extension Gallery](http://visualstudiogallery.msdn.microsoft.com/27077b70-9dad-4c64-adcf-c7cf6bc9970c). If you do not have NuGet, or are running a version prior to `2.0`, you *must* install it (or upgrade) before you will be able to build the projects.

The solution uses the *Package Restore* feature of NuGet to automatically download any missing packages when the project is built. This requires that you have the "[Allow NuGet to download missing packages during build](http://docs.nuget.org/docs/workflows/using-nuget-without-committing-packages)" setting enabled; in Visual Studio, you can find the setting under `Options -> Package Manager -> General`.

Once NuGet is installed and configured, you should be able to build the solution.

---

### When reading along with the book ###

The OCaml code from [resource page](http://www.cl.cam.ac.uk/~jrh13/atp/) combines the code and examples in one script. We have separated them in our ported F# code to simplify development and testing; all library code has been placed into the `FSharpx.Books.AutomatedReasoning` project, and the examples put into F# scripts (`.fsx`) in the `Examples` folder.

In the book, OCaml code and example scripts are identified by bounding boxes. Example code typically starts with an `#`, indicating it is being run in the OCaml REPL; the ported code for these are typically found in the Examples directory and code without the # is typically found in the library project.

---

### Running Examples ###

To run the example scripts, you must first build the solution (see the previous section).

The `Examples` folder contains `*.fsx` scripts corresponding to the original OCaml files. Within each `*.fsx` file, examples appear in the same order as in the book; we have added a comment to each example with its page number in the book to make cross-referencing easier.

When first opening an example script file, run the `#load`, `open` and `fsi.AddPrinter` statements at the top of the script file to setup the interactive environment for the following examples.

We suggest that when running the examples, you run each one separately so as not to lose track of which example produced which result. Some of the examples rely on statements earlier in the script, so if you skip ahead you may get errors.

In order to demonstrate certain aspects and limitations of automated reasoning, some of the examples purposely fail by raising an exception; others may take several minutes, hours, or days to run -- if they terminate at all. In both cases, these examples are identified by comments in the scripts so you will know this is the expected behavior.

Each of the examples fall into one of the following categories (with the associated special comment, if applicable):

  1.*Completes successfully in <10 seconds.*

  No special comment. **Most examples fall into this category.**

  2.*Completes successfully in >10 seconds, but <5 minutes.*

  Includes a comment with the result of the `fsi` `#time` directive when the example is run on an average machine. For example:

  ```fsharp
  // Real: 00:04:35.586, CPU: 00:04:31.718, GC gen0: 5020, gen1: 137, gen2: 9
  ```

  3.*Runs for an unknown or infinite length of time*

  Some examples take a very long time to run. These are marked with the comment `LongRunning`.

  4.*Failure*

  Marked with a comment noting the expected reason for failure.

  5.*Exception*

  Examples that raise a non-Failure exception; marked with a comment noting the expected type of the exception.

---

### Notable differences between the OCaml and F# code ###

  - In a few places, errors are handled using the `Option` type instead of exceptions. This is because:
    - Exceptions in F#/.NET are much slower than in OCaml
    - Recursive functions which throw and/or catch exceptions don't play nicely with type inference (in both F# and OCaml); the output type of such functions cannot be unified, so it will always be shown as a generic parameter (e.g., `'b`) instead of the true output type of the function (e.g., `int` or `bool`). These functions also make it *extremely* difficult to locate the source of an error.

  - Preprocessors such as [camlp4 / camlp5](http://caml.inria.fr/pub/docs/tutorial-camlp4/tutorial004.html) don't exist for F#. The original OCaml code for the book uses `camlp5` quotations (`<<` and `>>`) to transparently call the parsing functions for formula and term strings. Our F# code adds explicit calls to the parsing functions; as such, no uses of `default_parser` and `default_printer` appear in the F# code.

    Examples:

    ```ocaml
    (* OCaml *)
    <<x + 3 * y>>;;
    ```
    ```fsharp
    // F#
    parse_exp "x + 3 * y";;
    ```

    ```ocaml
    (* OCaml *)
    <<p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)>>;;
    ```
    ```fsharp
    // F#
    parse_prop_formula "p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)";;
    ```

  - Duplicated names are avoided. Since OCaml shadows names and F# does not allow duplicate names, any function name causing a duplicate name error will have the name appended with an increasing sequential number.

    ```ocaml
    (* OCaml *)
    let a = ...;;
    let a = ...;;
    let a = ...;;
    ```
    ```fsharp
    // F#
    let a001 = ...;;
    let a002 = ...;;
    let a003 = ...;;
    ```
     
    For some of the test strings such as in tableaux.fsx, the same name is used multiple times. To avoid duplicate name errors some of the names have a character appended.

    ```ocaml
    (* OCaml *)
    let p20 = prawitx ...;;
    let p20 = compare ...;;
    let p20 = splittab ...;;
    ```
    ```fsharp
    // F#
    let p20p = prawitx ...;;
    let p20c = compare ...;;
    let p20s = splittab ...;;
    ```

  - Some OCaml toplevel commands such as `#trace` and `#install-printer` don't exist in F# Interactive (`fsi`). In some cases, the functionality can be replicated:

    ```ocaml
    (* OCaml toplevel *)
    #install_printer my_printer;;
    ```
    ```fsharp
    // F# (fsi)
    fsi.AddPrinter my_printer;;   // my_printer : 'T -> string
    ```

---

### Unit Testing ###

The `FSharpx.Books.AutomatedReasoning.Tests` project contains all of the examples from the book (plus some additional examples from John Harrison's website), converted into unit test cases with NUnit 2.6.1 and FsUnit. These test cases serve as **evidence** (but not proof!) of correctness as the code base is updated or optimized over time.

You can execute the tests by building the `FSharpx.Books.AutomatedReasoning.Tests` project, then loading the compiled assembly into a test runner like **[NUnit GUI](http://www.nunit.org/)** or **[TestDriven.NET 3.4.2803 (Beta 3)](http://www.testdriven.net/)**.

*We strongly recommend using the x86 versions of the test runners.* The CLR's default maximum stack size of 1MB is enough for 32-bit processes, but the test cases reliably crash with a `StackOverflowException` on a 64-bit process. This is because many of the library functions are recursive, but not *tail-recursive* -- and since many types double in size on an x64 platform, these functions quickly consume the stack and crash the process.

NOTE: On a 64-bit machine, the NUnit installer only creates a Start Menu shortcut for the 64-bit version so you must create your own shortcut (e.g., on the Desktop) to the x86 version; the x86 version is normally found at `C:\Program Files (x86)\NUnit 2.6.1\bin\nunit-x86.exe`.

Once you have installed NUnit, built the `FSharpx.Books.AutomatedReasoning.Tests` project, and opened the NUnit (x86) GUI, follow these steps to run the tests:

  1. In the NUnit GUI, go to `File -> Open Project`. Find the `FSharpx.Books.AutomatedReasoning.Tests.dll` in the `FSharpx.Books.AutomatedReasoning.Tests\bin\Debug` folder in your repository folder (i.e., the folder you cloned the repository into). Double-click the file, or select it and press the 'Open' button.
  2. Click the *Categories* tab on left side of the NUnit GUI window.
  3. Double-click 'LongRunning', then check the box labeled *Exclude these categories*.
  4. Click the *Tests* tab on left side of the NUnit GUI window and press the 'Run' button.

There are a few important points to note when implementing new test cases:
  - NUnit only accepts parameterized tests on primitive types. To compare sophisticated values, we have to put them into arrays and use indices as test parameters.
  - FsUnit uses type test to implement its DSL. Type inference doesn't work on this DSL, so make sure that two compared values belong to the same type.
  - FsUnit and the library have some clashed constraints, namely `True` and `False`. To create tests correctly, one might need to use detailed type annotation such as `formula<fol>.True` and `formula<fol>.False` for literals in first-order logic.
  - A few slow tests are put into `LongRunning` category. These tests aren't recommended for normal development -- they're only used to validate the ported code on release.

---

### F#-specific porting notes ###

  - The F# compiler warning `FS0025` (about incomplete pattern matches) has been disabled for the `Debug` configurations of the projects. These incomplete matches are found throughout the original OCaml code and eliminating them *correctly* would require extensive changes to the code. So, to keep our code faithful to the book, it has been left as-is and the warning disabled to promote readability.
  - A few examples must be run with a 16MB stack (the default limit set by OCaml version); this is done using the `runWithEnlargedStack` function in `Examples\initialization.fsx`.
Without using our `runWithEnlargedStack` function, these examples crash with a `StackOverflowException` because the CLR uses a 1MB stack by default. (Discussion: [Why does F# impose a low limit on stack size?](http://stackoverflow.com/questions/7947446/why-does-f-impose-a-low-limit-on-stack-size)).
  - The built-in `Failure` active pattern has been redefined to accommodate `KeyNotFoundException`, `ArgumentException`, etc. The OCaml version makes use of `Failure` as a control flow; the F# version throws different kinds of exceptions which aren't caught by the default `Failure` pattern. The active pattern may need to be updated to handle other exceptions later (see the detailed function in the beginning of `lib.fs`).
