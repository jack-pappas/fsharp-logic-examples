namespace Reasoning.Automated.Harrison.Handbook

module prop_test =

    open lib
    open intro
    open formulas
    open prop

    let test001 = print_prop_formula (parse_prop_formula "p \/ q ==> r")


