Logic Programming in F#
===
### Code and Examples from John Harrison's "[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html)"

---

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
 - Run a few examples with 10MB stack using `runWithStackFrame` in `initialization.fsx`. These examples result in stackoverflow exception in F# on Windows due to small 1MB stack (see extensive discussion [here](http://stackoverflow.com/questions/7947446/why-does-f-impose-a-low-limit-on-stack-size)).

### Unit tests ###
A large set of unit tests is created based on available examples. These test cases serve as proofs of correctness when the code base is updated or optimized over time. They currently work fine with *NUnit x86 2.6* and *TestDriven.NET-3.4.2803* test runners. There are a few problems on implementing test cases though:
 - NUnit only accepts parameterized tests on primitive types. To compare sophisticated values, we have to put them into arrays and use indices as test parameters.
 - FsUnit uses type test to implement its DSL. Type inference doesn't work on this DSL, so make sure that `expected` and `result` belong to the same type.
 - FsUnit and the library have some clashed constraints, namely `True` and `False`. To create tests correctly, one might need to use detailed type annotation, such as `formula<fol>.True` and `formula<fol>.False` for literals in first-order logic.
 - A few slow tests are put into `LongRunning` category. They aren't recommended to run on the development basis. Their purposes are to validate the project upon release.
 
### Optimization Notes (`optimized` branch only) ###
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

 - Replaced the `(--)` and `(---)` operators with F# list comprehensions using the range syntax, e.g., `[m..n]`.

  - Replaced the Patricia trie datatype used to implement Finite Partial Functions (the `func<_,_>` type in the code) with the F# `Map<_,_>` type.
  - `func<_,_>` is now just an alias for `Map<_,_>`.
  - Removed some of the functions for manipulating the Patricia trie type, since they were no longer needed.
  - Modified the remaining functions for working with `func<_,_>` so they work with `Map<_,_>` instead; some of these functions are now just aliases for functions in the F# `Map` module.

 - **`(Incomplete)`** Recursive functions have been modified/re-implemented so thta all recursive calls can be compiled to tail-calls. For many functions, this means modifying the function to use continuation-passing (CPS).

 - **`(Incomplete)`** Reformatted code (where possible) for better readability. This doesn't affect the performance *per se*, but it does often make it easier to spot potential optimizations in the code.
  - Reformat heavily-nested function calls using the F# pipeline operator `(|>)`.
  - Use `match` instead of 'if-elif-else' when it seems appropriate.

### Optimization TODO ###
 - Rewrite functions, as needed, to avoid unnecessary data-manipulation and list traversals. The code makes extensive use of the `(@)` operator and the `List.foldBack` function, which should be replaced (if possible) with `(::)` and `List.fold`. In addition, there are a number of places where the range operator `[m..n]` is used to create a list of values which is immediately consumed using `List.foldBack`, `List.map`, etc.; instead, these should be replaced with the `List.init` function.
 - Modify code to use arrays instead of lists, where possible.
 - Modify code to use `Option` and `Choice<_,_>` instead of handling backtracking with exceptions.
 - Modify code to use F# `Set<_>` instead of representing sets with lists.
 - (To be performed LAST) Finish CPS-transforming recursive functions.
  - Instead of doing this manually, we could implement a `cont` workflow builder type for F# and use that for the CPS transformations. It would also make the code much easier to read.