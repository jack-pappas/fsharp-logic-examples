// ========================================================================= //
// Copyright (c) 2012 Jack Pappas, Anh-Dung Phan                             //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

// ========================================================================= //
// Tweak F# default state for theorem proving code.                          //
// ========================================================================= //

#I @".\..\FSharpx.Books.AutomatedReasoning\bin\Debug"
#r @"FSharpx.Books.AutomatedReasoning.dll"
#r @"FSharpx.Compatibility.OCaml.dll"
#r @"FSharp.PowerPack.dll"

// Reduce margins
fsi.PrintWidth <- 72;;

// Open formatting
//open Format;;

// Open bignums
open FSharpx.Compatibility.OCaml;;
open FSharpx.Compatibility.OCaml.Num;;

// Print the full value of a Num instead of truncating it.
fsi.AddPrinter (fun (n : Num) -> n.ToString ());;

/// The greatest maximum-stack-size that should be used
/// with the 'runWithStackFrame' function.
let [<Literal>] STACK_LIMIT = 16777216;;

/// Run a function with a custom maximum stack size.
/// This is necessary for some functions to execute
/// without raising a StackOverflowException.
let runWithCustomStackSize maxStackSize fn =
    // Preconditions
    if maxStackSize < 1048576 then
        invalidArg "stackSize" "Functions should not be executed with a \
            maximum stack size of less than 1048576 bytes (1MB)."
    elif maxStackSize > STACK_LIMIT then
        invalidArg "stackSize" "The maximum size of the stack frame should \
            not exceed 16777216 bytes (16MB)."

    /// Holds the return value of the function.
    let result = ref Unchecked.defaultof<'T>

    // Create a thread with the specified maximum stack size,
    // then immediately execute the function on it.
    let thread = System.Threading.Thread ((fun () -> result := fn()), maxStackSize)
    thread.Start ()

    // Wait for the function/thread to finish and return the result.
    thread.Join ()
    !result;;

/// Runs a function within a thread which has an enlarged maximum-stack-size.
let inline runWithEnlargedStack fn =
    runWithCustomStackSize STACK_LIMIT fn;;
(* TEMP :   These operators were removed from the 'lib' module.
            Eventually, they should be replaced in the example code
            by their standard F# equivalents. *)
// pg. 618
// OCaml: val ( -- ) : int -> int -> int list = <fun>
// F#:    val ( -- ) : int -> int -> int list
let inline (--) m n = [m .. n];;    // Usages of this should be changed to [x .. y]

// pg.618
// OCaml: val ( --- ) : num -> num -> num list = <fun>
// F#:    val ( --- ) : num -> num -> num list
let inline (---) (m : num) (n : num) = [m .. n];;   // Usages of this should be changed to [x .. y]

// pg. 618
// OCaml: val ( ** ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b = <fun>
// F#:    val ( >>|> ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
/// Composes two functions, then applies a value to the resulting function.
let inline ( >>|> ) f g x = f <| g x;;      // Usages of this should be changed to <<

// ------------------------------------------------------------------------- //
// Find list member that maximizes or minimizes a function.                  //
// ------------------------------------------------------------------------- //

// pg. 620
// OCaml: val maximize : ('a -> 'b) -> 'a list -> 'a = <fun>
// F#:    val maximize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
let inline maximize f l =
    List.maxBy f l
    
// pg. 620
// OCaml: val minimize : ('a -> 'b) -> 'a list -> 'a = <fun>
// F#:    val minimize : ('a -> 'b) -> 'a list -> 'a when 'b : comparison
let inline minimize f l =
    List.minBy f l
