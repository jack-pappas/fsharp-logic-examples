namespace Reasoning.Automated.Harrison.Handbook.Eric

module misc =

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




