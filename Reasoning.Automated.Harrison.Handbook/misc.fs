namespace Reasoning.Automated.Harrison.Handbook.Eric

//open Reasoning.Automated.Harrison.Handbook.prop

module misc =

    let mapTuple4 f (a, b, c, d ) = (f a, f b, f c, f d)
    
    // Note: The CNF is represented interanally as a list of list.
    // The the first leve; of list have implied and beteween them
    // and the second level of list have implied or between them.
    let print_cnf cnf =
        let rec print_cnf_util cnf item =
            match cnf with
            | []   -> ()
            | h::t -> 
                printf "%d " item
                printfn "%A"  h
                print_cnf_util t (item + 1)
        print_cnf_util cnf 0




