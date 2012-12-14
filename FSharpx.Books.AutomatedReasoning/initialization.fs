// ========================================================================= //
// Copyright (c) 2012 Eric Taucher, Jack Pappas, Anh-Dung Phan               //
// (See "LICENSE.txt" for details.)                                          //
// ========================================================================= //

/// Misc functions to set up a nice environment.
[<AutoOpen>]
module FSharpx.Books.AutomatedReasoning.initialization

type StackSize =
    | Standard
    | Large

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