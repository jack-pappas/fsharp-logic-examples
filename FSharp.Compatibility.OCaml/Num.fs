// TODO : Add copyright header

namespace FSharpx.Compatibility.OCaml

//
[<CustomEquality; CustomComparison>]
type Num =
    /// 32-bit signed integer.
    | Int of int
    /// Arbitrary-precision integer.
    | Big_int of bigint
    // Arbitrary-precision rational.
    | Ratio of Microsoft.FSharp.Math.BigRational

    static member Zero = Int 0

    static member One = Int 1

    static member op_Addition (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member op_Subtraction (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member op_Multiply (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member op_Division (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member op_Modulus (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member op_UnaryNegation (x : num) : num =
        raise <| System.NotImplementedException ()

    static member op_Explicit (r : int) : num =
        raise <| System.NotImplementedException ()

    static member Abs (x : num) =
        raise <| System.NotImplementedException ()

    static member Ceiling (x : num) : num =
        raise <| System.NotImplementedException ()

    static member Floor (x : num) : num =
        raise <| System.NotImplementedException ()

    static member Max (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member Min (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member Pow (x : num, y : num) =
        raise <| System.NotImplementedException ()

    static member Round (x : num) : num =
        raise <| System.NotImplementedException ()

    static member Sign (x : num) : int =
        raise <| System.NotImplementedException ()

    static member Truncate (x : num) : num =
        raise <| System.NotImplementedException ()

    static member Parse (str : string) : num =
        // TODO : Parse the string into a 'num'
        // If the string cannot be parsed, then for compatibility with OCaml,
        // failwith "num_of_string"
        raise <| System.NotImplementedException ()

    interface System.IEquatable<num> with
        //
        member this.Equals (other : num) =
            raise <| System.NotImplementedException ()

    interface System.IComparable with
        //
        member this.CompareTo (other : obj) =
            raise <| System.NotImplementedException ()

    interface System.IComparable<num> with
        //
        member this.CompareTo (other : num) =
            raise <| System.NotImplementedException ()

/// Type alias for Num, for compatibility with OCaml.
and num = Num


/// <summary>Operation on arbitrary-precision numbers.</summary>
/// <remarks>Numbers (type num) are arbitrary-precision rational numbers, plus the
/// special elements 1/0 (infinity) and 0/0 (undefined).</remarks>
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Num =
    (* TODO :   Add [<CompilerMessage>] to the functions below so when they're used
                the F# compiler will emit a warning to let the user know they can
                use the equivalent, built-in F# generic function.
                E.g., use the generic 'abs' instead of 'abs_num'. *)

    /// Addition.
    let inline add_num (x : num) (y : num) : num =
        x + y

    /// Unary negation.
    let inline minus_num (x : num) : num =
        -x

    let inline (-/) (x : num) (y : num) : num =
        x - y

    //
    let inline sub_num (x : num) (y : num) : num =
        x - y

    let inline ( */ ) (x : num) (y : num) : num =
        x * y

    //
    let inline mult_num (x : num) (y : num) : num =
        x * y

    //
    let inline square_num (x : num) : num =
        x * x

    //
    let inline div_num (x : num) (y : num) : num =
        x / y

    //
    let quo_num (x : num) (y : num) : num =
        raise <| System.NotImplementedException ()

    //
    let mod_num (x : num) (y : num) : num =
        raise <| System.NotImplementedException ()

    //
    let inline ( **/ ) (x : num) (y : num) : num =
        num.Pow (x, y)

    //
    let inline power_num (x : num) (y : num) : num =
        num.Pow (x, y)

    //
    let inline abs_num (x : num) : num =
        num.Abs x

    //
    let inline succ_num (n : num) : num =
        n + (Int 1)

    //
    let inline pred_num (n : num) : num =
        n - (Int 1)

    //
    let incr_num (r : num ref) : unit =
        r := succ_num !r

    //
    let decr_num (r : num ref) : unit =
        r := pred_num !r

    /// Test if a number is an integer
    let is_integer_num (n : num) : bool =
        raise <| System.NotImplementedException ()


    (* The four following functions approximate a number by an integer *)

    //
    let integer_num (n : num) : num =
        // Round or Truncate?
        raise <| System.NotImplementedException ()

    //
    let inline floor_num (n : num) : num =
        num.Floor n

    //
    let round_num (n : num) : num =
        // Round or Truncate?
        raise <| System.NotImplementedException ()

    //
    let inline ceiling_num (n : num) : num =
        num.Ceiling n

    //
    let inline sign_num (n : num) : int =
        num.Sign n


    (* Comparisons between numbers *)

    let inline ( =/ ) (x : num) (y : num) =
        x = y
    let inline ( </ ) (x : num) (y : num) =
        x < y
    let inline ( >/ ) (x : num) (y : num) =
        x > y
    let inline ( <=/ ) (x : num) (y : num) =
        x <= y
    let inline ( >=/ ) (x : num) (y : num) =
        x >= y
    let inline ( <>/ ) (x : num) (y : num) =
        x <> y
    let inline eq_num (x : num) (y : num) =
        x = y
    let inline lt_num (x : num) (y : num) =
        x < y
    let inline le_num (x : num) (y : num) =
        x <= y
    let inline gt_num (x : num) (y : num) =
        x > y
    let inline ge_num (x : num) (y : num) =
        x >= y

    /// Return -1, 0 or 1 if the first argument is less than, equal to, or greater than the second argument.
    let inline compare_num (x : num) (y : num) =
        compare x y
    /// Return the greater of the two arguments.
    let inline max_num (x : num) (y : num) =
        num.Max (x, y)
    /// Return the smaller of the two arguments.
    let inline min_num (x : num) (y : num) =
        num.Min (x, y)


    (* Coercions with strings *)

    //
    let inline string_of_num (n : num) : string =
        n.ToString ()

    //
    let approx_num_fix (precision : int) (n : num) : string =
        raise <| System.NotImplementedException ()

    //
    let approx_num_exp (precision : int) (n : num) : string =
        raise <| System.NotImplementedException ()

    /// Convert a string to a number.
    /// Raise Failure "num_of_string" if the given string is not a valid representation of an integer
    let inline num_of_string (str : string) : num =
        num.Parse str


    (* Coercions between numerical types *)

    // TEMP : Alias for 'nat' so it can be used by the function definitions below.
    // What is the underlying type of OCaml's 'nat'? Is it a 32-bit integer or a native-size integer?
    type nat = uint32

    let int_of_num (n : num) : int =
        raise <| System.NotImplementedException ()

    let num_of_int (r : int) : num =
        raise <| System.NotImplementedException ()

    let nat_of_num (n : num) : nat =
        raise <| System.NotImplementedException ()

    let num_of_nat (r : nat) : num =
        raise <| System.NotImplementedException ()

    let num_of_bug_int (i : bigint) : num =
        raise <| System.NotImplementedException ()

    let big_int_of_num (n : num) : bigint =
        raise <| System.NotImplementedException ()

//    let ratio_of_num (n : num) : Microsoft.FSharp.Math.BigRational =
//        raise <| System.NotImplementedException ()
//
//    let num_of_ratio (q : Microsoft.FSharp.Math.BigRational) : num =
//        raise <| System.NotImplementedException ()

    let float_of_num (n : num) : float =
        raise <| System.NotImplementedException ()

