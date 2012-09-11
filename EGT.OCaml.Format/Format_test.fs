namespace EGT.OCaml

module Format_test =

    open Format

    let test001 = 
        printfn "test001 <<<<<<<";
        print_string "Hello, World!"
        printfn "test001 >>>>>>>";

    let test010 =
      open_box 0; print_string "<<";
      open_box 0; print_string "p \/ q ==> r"; close_box();
      print_string ">>"; close_box()

