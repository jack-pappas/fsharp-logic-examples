Logic Programming in F#
===
### Code and Examples from John Harrison's "[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html)"

---

### Needed for Installation ###

The solution uses F# 2.0 and .NET framework 4.0 inside [Visual Studio 2010] (http://www.microsoft.com/visualstudio/eng/products/visual-studio-overview).

You will need to install [NuGet] (http://nuget.codeplex.com/) to get additional required libraries. 
After installing NuGet, make sure to enable "Allow NuGet to download missing packages during build". 
[This setting](http://docs.nuget.org/docs/workflows/using-nuget-without-committing-packages) is under Options -> Package Manager -> General.
You will have to build the application once you have NuGet installed and the solution open in Visual Studio.

The test cases have been tested with *NUnit 2.6 x86* and *TestDriven.NET-3.4.2803* x86 test runners. 
**We recommend you to use x86 versions of the test runners.** 
Although 1MB stack limit is enough for 32-bit test processes, the test cases will soon result in `StackOverflowException` on a 64-bit process. 
The reason is that many functions are *non-tail-recursive* and types often double their sizes on x64.

### Instructions on running tests with NUnit ###

To run the unit test you will need to

1. Download and install NUnit
2. Download repository, unpack if necessary, open with Visual Studio 2010, and build the solution
4. Start NUnit x86 (Note: on 64-bit systems the system menu will use 64-bit version of NUnit. 
   The x86 version of NUnit is nunit-x86 which can be found in the NUnit bin directory)
5. Within NUnit *File -> Open Project*, navigate to directory with Reasoning.Automated.Harrison.Handbook.Tests.dll
6. Double click Reasoning.Automated.Harrison.Handbook.Tests.dll
9. Click *Categories* tab on left side of NUnit
10. Double click LongRunning, click *Add* and select *Exclude these categories*
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
 - Run a few examples with 16MB stack (the default limit set by OCaml version) using `runWith16MBStack` in `initialization.fsx`. These examples result in `StackOverflowException` in F# on Windows due to small 1MB stack (see extensive discussion [here](http://stackoverflow.com/questions/7947446/why-does-f-impose-a-low-limit-on-stack-size)).

### Unit tests ###
A large set of unit tests is created based on available examples. These test cases serve as proofs of correctness when the code base is updated or optimized over time. There are a few problems on implementing test cases though:
 - NUnit only accepts parameterized tests on primitive types. To compare sophisticated values, we have to put them into arrays and use indices as test parameters.
 - FsUnit uses type test to implement its DSL. Type inference doesn't work on this DSL, so make sure that `expected` and `result` belong to the same type.
 - FsUnit and the library have some clashed constraints, namely `True` and `False`. To create tests correctly, one might need to use detailed type annotation, such as `formula<fol>.True` and `formula<fol>.False` for literals in first-order logic.
 - A few slow tests are put into `LongRunning` category. They aren't recommended to run on the development basis. Their purposes are to validate the project upon release.
 
### Optimization Notes (`optimized` branch only) ###
 - Replaced the `(--)` and `(---)` operators with F# list comprehensions using the range syntax, e.g., `[m..n]`.
 
 - A number of functions defined in `lib.fs` have exact equivalents in `FSharp.Core`; these functions have been removed from `lib.fs` and all uses of them replaced by their equivalent function from `FSharp.Core`. NOTE : Some of these functions have also been replaced in the `master` branch code.
  - Replaced `(**)` (or `(>>|>)` in the `master` branch) with `(<<)`.
  - Replaced `map2` with `List.map2`.
  - Replaced `rev` with `List.rev`.
  - Replaced `hd` with `List.head`.
  - Replaced `tl` with `List.tail`.
  - Replaced `itlist` with `List.foldBack`.
  - Replaced `end_itlist` with `List.reduceBack`.
  - Replaced `itlist2` with `List.foldBack2`.
  - Replaced `zip` with `List.zip`.
  - Replaced `forall` with `List.forall`.
  - Replaced `exists` with `List.exists`.
  - Replaced `partition` with `List.partition`.
  - Replaced `filter` with `List.filter`.
  - Replaced `length` with `List.length`.
  - Replaced `find` with `List.find`.
  - Replaced `el` with `List.nth`.
  - Replaced `map` with `List.map`.
  - Replaced `replicate` with `List.replicate`.
  - Replaced `forall2` with `List.forall2`.
  - Re-implemented `index` using `List.findIndex`.
  - Replaced `unzip` with `List.unzip`.
  - Re-implemented `mapfilter` using `List.choose`.
  - Replaced `maximize` and `optimize` with `List.maxBy`.
  - Replaced `minimize` and `optimize` with `List.minBy`.

 - Re-implemented some of the remaining functions in `lib.fs` so they're faster.

  - Replaced the Patricia trie datatype used to implement Finite Partial Functions (the `func<_,_>` type in the code) with the F# `Map<_,_>` type.
    - `func<_,_>` is now just an alias for `Map<_,_>`.
    - Removed some of the functions for manipulating the Patricia trie type, since they were no longer needed.
    - Modified the remaining functions for working with `func<_,_>` so they work with `Map<_,_>` instead; some of these functions are now just aliases for functions in the F# `Map` module.

 - **`(Incomplete)`** Recursive functions have been modified/re-implemented so thta all recursive calls can be compiled to tail-calls. For many functions, this means modifying the function to use continuation-passing (CPS).

 - **`(Incomplete)`** Reformatted code (where possible) for better readability. This doesn't affect the performance *per se*, but it does often make it easier to spot potential optimizations in the code.
  - Reformat heavily-nested function calls using the F# pipeline operator `(|>)`.
  - Use `match` instead of 'if-elif-else' when it seems appropriate.
  
 - **`(Incomplete)`** Replace sorted lists with F# `Set<_>` type and functions from the `Set` module.
  - So far, most (all?) of the functions in `lib.fs` which perform set-based operations on lists have been rewritten to use `Set<_>` internally. However, they still accept and output lists for compatibility with existing code; the overhead of converting between sets and lists currently causes some tests to run significantly slower.

### Optimization TODO ###
 - Modify code to use arrays instead of lists, where possible.
 - Modify code to use F# `Set<_>` instead of representing sets with lists.
 - Rewrite functions, as needed, to avoid unnecessary data-manipulation and list traversals. The code makes extensive use of the `(@)` operator and the `List.foldBack` function, which should be replaced (if possible) with `(::)` and `List.fold`.
   - In addition, there are a number of places where the range operator `[m..n]` is used to create a list of values which is immediately consumed using `List.foldBack`, `List.map`, etc.; instead, these should be replaced with the `List.init` function.
   - Some of the uses of `List.foldBack` and `List.reduceBack` will be replaced by `Set.foldBack` and `Array.foldBack` as we make other optimizations.
 - Modify code to use `Option` and `Choice<_,_>` instead of handling backtracking with exceptions.
 - Parsing code should be modified to operate on `char list` rather than `string list`, because the string comparisons are much more expensive.
 - (To be performed LAST) Finish CPS-transforming recursive functions.
  - Instead of doing this manually, we could implement a `cont` workflow builder type for F# and use that for the CPS transformations. It would also make the code much easier to read.
