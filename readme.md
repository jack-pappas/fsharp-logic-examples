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

[NUnit] (http://www.nunit.org/) is recommended to run the unit tests.

### Notes on running Unit test ###

To run the unit test you will need to 
1. Download and install NUnit
2. Download project and open with Visual Studio 2010
3. Build solution
4. Start NUnit (x86 version)
   Note: On 64-bit systems the system menu will use 64-bit version of NUnit.
   The test do not run correctly with the 64-bit version.
   To run the test you must use the x86 version.
   The x86 version of NUnit is nunit-x86 and is found in the NUnit bin directory.
5. Within NUnit File -> Open Project
6. File type: Assemblies (*.dll, *.exe)
7. Navigate to directory with Reasoning.Automated.Harrison.Handbook.Tests.dll
8. Double click Reasoning.Automated.Harrison.Handbook.Tests.dll
9. Click Categories tab on left side of NUnit
10. Double click LongRunning
11. Click Add
12. Select Exclude these categories
13. Click Tests tab on left side of NUnit
13. Click Run



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
 - Redefined `Failure` active patterns to accommodate `KeyNotFoundException`, `ArgumentException`, etc. The OCaml version makes use of `Failure` as a control flow; the F# version throws different kinds of exceptions which weren't caught by default `Failure`. The active pattern might be updated to handle other exceptions later (see the detailed function in the beginning of `lib.fs`).
 
### Unit tests ###
A large set of unit tests is created based on available examples. These test cases serve as proofs of correctness when the code base is updated or optimized over time. They currently work fine with *NUnit x86 2.6* and *TestDriven.NET-3.4.2803* test runners. There are a few problems on implementing test cases though:
 - NUnit only accepts parameterized tests on primitive types. To compare sophisticated values, we have to put them into arrays and use indices as test parameters.
 - FsUnit uses type test to implement its DSL. Type inference doesn't work on this DSL, so make sure that `expected` and `result` belong to the same type.
 - FsUnit and the library have some clashed constraints, namely `True` and `False`. To create tests correctly, one might need to use detailed type annotation, such as `formula<fol>.True` and `formula<fol>.False` for literals in first-order logic.
 - A few slow tests are put into `LongRunning` category. They aren't recommended to run on the development basis. Their purposes are to validate the project upon release.
