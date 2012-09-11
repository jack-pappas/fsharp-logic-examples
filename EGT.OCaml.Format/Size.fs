namespace EGT.OCaml

module Size =
    
    type size =
      interface
        abstract size_of_int : int -> size
        abstract int_of_size : size -> int
      end




