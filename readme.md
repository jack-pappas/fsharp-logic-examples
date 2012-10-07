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
 - Redefined `Failure` active patterns to accommodate `KeyNotFoundException`, `ArgumentException`, etc. The OCaml version makes use of `Failure` as a control flow; the F# version throws different kinds of exceptions which weren't caught by default `Failure`. The active pattern might be updated to handle other exceptions later (see the detailed function in the beginning of `lib.fs`).
 
### Unit tests ###
A large set of unit tests is created based on available examples. These test cases serve as proofs of correctness when the code base is updated or optimized over time. There are a few problems on implementing test cases though:
 - NUnit only accepts parameterized tests on primitive types. To compare sophisticated values, we have to put them arrays and use indices as test parameters.
 - FsUnit uses type test to implement its DSL. Type inference doesn't work on this DSL, so make sure that `expected` and `result` belong to the same type.
 - FsUnit and the library has some clashed constraints, namely `True` and `False`. To create tests correctly, one might need to specifically use `formula<fol>.True` and `formula<fol>.False` for literals in first-order logic.
 - A few slow tests are marked `LongRunning`. They are not recommended to run on the development basis. Their purposes are to validate the project upon release.
