// TODO : Add copyright/licensing header

namespace Reasoning.Automated.Harrison.Handbook

[<AutoOpen>]
module misc =
    open FSharpx.Compatibility.OCaml    
    open FSharpx.Compatibility.OCaml.Num

    /// <summary>Determines if one number is evenly divisible by another number,
    /// based on the semantics of the OCaml mod (%) operator.</summary>
    /// <remarks>The standard mod (%) operator in .NET (and in F#) throws a DivideByZeroException
    /// when 'y' is zero (0); however, the operation x % 0 simply returns zero (0) in OCaml, so
    /// that is the behavior preserved by this method.</remarks>
    let (*inline*) divides x y =
        //y = 0 || y % x = 0
        match y with
        | 0 -> true       // F# will throw DivideByZeroException so need special case for zero
        | _ -> y % x = 0  // This is correct, it was verified by testing aginst OCaml output.

    // 'divides', for the 'num' type.
    let divides' (x : num) (y : num) : bool =
        raise <| System.NotImplementedException ()

