// TODO : Add copyright/licensing header

namespace Reasoning.Automated.Harrison.Handbook

[<AutoOpen>]
module misc =
    open FSharpx.Compatibility.OCaml

    //
    let mapTuple4 f (a, b, c, d) =
        f a, f b, f c, f d
    
    // Note: The CNF is represented interanally as a list of list.
    // The the first leve; of list have implied and beteween them
    // and the second level of list have implied or between them.
    let print_cnf cnf =
        cnf
        |> List.iteri (fun item h ->
            printf "%d " item
            printfn "%A" h)
//        // TODO : Change to use List.iteri instead of explicitly implementing
//        // a recursive function to process the list.
//        let rec print_cnf_util item cnf =
//            match cnf with
//            | [] -> ()
//            | h :: t ->
//                printf "%d " item
//                printfn "%A" h
//                print_cnf_util (item + 1) t
//        print_cnf_util 0 cnf

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

