module NHolZ.Tests.Utils1

open NHolZ
open NUnit.Framework
open FsUnit

open FSharp.Compatibility.OCaml.Big_int

(* dest_type tests *)

[<Test>]
let ``dest_type_var_test``() =

    dest_type (Tyvar "num")
    |> should equal (Type_var "num")

[<Test>]
let ``dest_type_comp_test``() =

    dest_type (Tycomp ("->", [Tyvar "num";Tyvar "num"]))
    |> should equal (Type_comp ("->", [Tyvar "num";Tyvar "num"]))

(* is_bool_type tests *)

[<Test>]
let ``is_bool_type_false_test``() =

    is_bool_type (Tyvar "num")
    |> should equal false

[<Test>]
let ``is_bool_type_false2_test``() =

    is_bool_type (Tyvar "bool") //bool deve essere una costante e non una variabile
    |> should equal false

[<Test>]
let ``is_bool_type_true_test``() =

    is_bool_type (Tycomp ("bool",[])) //Tycomp è il tipo di qualsiasi costante di tip: bool è una costante zero aria come si vede dalla list
    |> should equal true

(* type_tyvars tests *)

[<Test>]
let ``type_tyvars_test``() =

    type_tyvars (Tycomp ("->", [(Tycomp ("+", [Tyvar "num";Tyvar "num"]));Tyvar "string"]))
    |> should equal [Tyvar "num";Tyvar "string"]

(* type_match tests *)

[<Test>]
let ``type_match_test``() =

    type_match (Tycomp ("->", [Tyvar "a";Tyvar "a"])) (Tycomp ("->", [Tyvar "b";Tyvar "b"]))
    |> should equal [(Tyvar "a", Tyvar "b")]

(* dest_term tests *)

[<Test>]
let ``dest_term_Tmconst_test``() =

    dest_term (Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"])))
    |> should equal (Term_const ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"])))

//TODO: add tests for other types of term

(* mk_const tests *)

[<Test>]
let ``mk_const_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("toString",Tycomp ("->",[Tyvar "x";Tyvar "y"])),Leaf,Leaf)

    let expected = Tmconst ("toString", Tycomp ("->",[Tyvar "w";Tyvar "z"]))
    let actual = mk_const ("toString", Tycomp ("->",[Tyvar "w";Tyvar "z"]))

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* const_name tests *)

[<Test>]
let ``const_name_test``() =

    const_name (Tmconst ("toString", Tycomp ("->",[Tyvar "w";Tyvar "z"])))
    |> should equal "toString"

(* const_type tests *)

[<Test>]
let ``const_type_test``() =

    const_type (Tmconst ("toString", Tycomp ("->",[Tyvar "w";Tyvar "z"])))
    |> should equal (Tycomp ("->",[Tyvar "w";Tyvar "z"]))

(* var_name tests *)

[<Test>]
let ``var_name_test``() =

    var_name (Tmvar ("a", Tyvar "bool"))
    |> should equal "a"

(* var_type tests *)

[<Test>]
let ``var_type_test``() =

    var_type (Tmvar ("a", Tyvar "bool"))
    |> should equal (Tyvar "bool")

(* list_mk_comb tests *)

[<Test>]
let ``list_mk_comb_test``() =

    list_mk_comb (Tmconst ("toString", Tycomp ("->",[Tyvar "w";Tyvar "z"])),[(Tmconst ("a", Tyvar "w"))])
    |> should equal (Tmcomb ((Tmconst ("toString", Tycomp ("->",[Tyvar "w";Tyvar "z"]))),(Tmconst ("a", Tyvar "w"))))

(* mk_bin tests *)

[<Test>]
let ``mk_bin_test``() =
    
    let expected = Tmcomb (Tmcomb ((Tmconst ("+", Tycomp ("->",[Tyvar "num";Tycomp ("->",[Tyvar "num";Tyvar "num"])]))),(Tmconst ("1", Tyvar "num"))), Tmconst ("2", Tyvar "num"))
    let actual = mk_bin (Tmconst ("+", Tycomp ("->",[Tyvar "num";Tycomp ("->",[Tyvar "num";Tyvar "num"])])),(Tmconst ("1", Tyvar "num")),(Tmconst ("2", Tyvar "num")))
    

    actual
    |> should equal expected

(* dest_bin tests *)

[<Test>]
let ``dest_bin_test``() =

    //is the inverse of the above function
    
    let expected = (Tmconst ("+", Tycomp ("->",[Tyvar "num";Tycomp ("->",[Tyvar "num";Tyvar "num"])])),(Tmconst ("1", Tyvar "num")),(Tmconst ("2", Tyvar "num")))
    let actual = dest_bin (Tmcomb (Tmcomb ((Tmconst ("+", Tycomp ("->",[Tyvar "num";Tycomp ("->",[Tyvar "num";Tyvar "num"])]))),(Tmconst ("1", Tyvar "num"))), Tmconst ("2", Tyvar "num")))
    

    actual
    |> should equal expected

(* is_bin tests *)

[<Test>]
let ``is_bin_test``() =
    
    let expected = true
    let actual = is_bin (Tmcomb (Tmcomb ((Tmconst ("+", Tycomp ("->",[Tyvar "num";Tycomp ("->",[Tyvar "num";Tyvar "num"])]))),(Tmconst ("1", Tyvar "num"))), Tmconst ("2", Tyvar "num")))

    actual
    |> should equal expected

(* dest_cbin tests *)

[<Test>]
let ``dest_cbin_test``() =
    
    let expected = (Tmconst ("1", Tyvar "num"),Tmconst ("2", Tyvar "num"))
    let actual = dest_cbin "+" (Tmcomb (Tmcomb ((Tmconst ("+", Tycomp ("->",[Tyvar "num";Tycomp ("->",[Tyvar "num";Tyvar "num"])]))),(Tmconst ("1", Tyvar "num"))), Tmconst ("2", Tyvar "num")))

    actual
    |> should equal expected

(* mk_binder tests *)

[<Test>]
let ``mk_binder_test``() =

    let f = Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])) //f (g:int -> int) = g 2
    let var = Tmvar ("x", Tyvar "num")
    let trm = Tmconst ("1", Tyvar "num")
    let lambdaAbstr = Tmabs (var, trm) // \x. 1
    
    let expected = Tmcomb (Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])), lambdaAbstr) // f \x. 1
    let actual = mk_binder (f,var,trm)

    actual
    |> should equal expected

(* dest_binder tests *)

[<Test>]
let ``dest_binder_test``() =

    //L'inversa della precedente

    let f = Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))
    let var = Tmvar ("x", Tyvar "num")
    let trm = Tmconst ("1", Tyvar "num")
    let lambdaAbstr = Tmabs (var, trm) // \x. 1
    
    let expected = (f,var,trm) 
    let actual = dest_binder (Tmcomb (Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])), lambdaAbstr))

    actual
    |> should equal expected

(* dest_cbinder tests *)

[<Test>]
let ``dest_cbinder_test``() =

    let f = Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))
    let var = Tmvar ("x", Tyvar "num")
    let trm = Tmconst ("1", Tyvar "num")
    let lambdaAbstr = Tmabs (var, trm) // \x. 1
    
    let expected = (var,trm) 
    let actual = dest_cbinder "f" (Tmcomb (Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])), lambdaAbstr))

    actual
    |> should equal expected

(* is_binder tests *)

[<Test>]
let ``is_binder_test``() =

    let f = Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))
    let var = Tmvar ("x", Tyvar "num")
    let trm = Tmconst ("1", Tyvar "num")
    let lambdaAbstr = Tmabs (var, trm) // \x. 1
    
    let expected = true
    let actual = is_binder (Tmcomb (Tmconst ("f" , Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])), lambdaAbstr))

    actual
    |> should equal expected

(* is_bool_term tests *)

[<Test>]
let ``is_bool_term_true_test``() =

    is_bool_term (Tmconst ("True", (Tycomp ("bool",[]))))
    |> should equal true

(* mk_eq tests *)

[<Test>]
let ``mk_eq_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("=",Tycomp ("->",[Tyvar "a";Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])])])),Leaf,Leaf) //defines equlity on generic types

    let actual = mk_eq (Tmconst ("1", Tyvar "num"), Tmconst ("1", Tyvar "num"))
    let expected = Tmcomb (
                        Tmcomb (
                            Tmconst ("=", Tycomp ("->", [Tyvar "num"; Tycomp ("->", [Tyvar "num"; Tycomp ("bool", [])])])),
                            Tmconst ("1", Tyvar "num")), 
                        Tmconst ("1", Tyvar "num"))

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* dest_eq tests *)

[<Test>]
let ``dest_eq_test``() =

    //è l'inversa della precedente
    
    let expected = (Tmconst ("1", Tyvar "num"), Tmconst ("1", Tyvar "num"))
    let actual = dest_eq (Tmcomb (
                            Tmcomb (
                                Tmconst ("=", Tycomp ("->", [Tyvar "num"; Tycomp ("->", [Tyvar "num"; Tycomp ("bool", [])])])),
                                Tmconst ("1", Tyvar "num")), 
                            Tmconst ("1", Tyvar "num"))
                            )

    actual
    |> should equal expected

(* is_eq tests *)

[<Test>]
let ``is_eq_true_test``() =

    is_eq ((Tmcomb (
                    Tmcomb (
                        Tmconst ("=", Tycomp ("->", [Tyvar "num"; Tycomp ("->", [Tyvar "num"; Tycomp ("bool", [])])])),
                        Tmconst ("1", Tyvar "num")), 
                    Tmconst ("1", Tyvar "num"))
                    )
            )
    |> should equal true

(* mk_imp tests *)

[<Test>]
let ``mk_imp_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("==>",Tycomp ("->",[Tycomp ("bool",[]);Tycomp ("->",[Tycomp ("bool",[]);Tycomp ("bool",[])])])),Leaf,Leaf)

    let actual = mk_imp (Tmconst ("A", Tycomp ("bool",[])), Tmconst ("B", Tycomp ("bool",[])))
    let expected = Tmcomb (
                        Tmcomb (
                            Tmconst ("==>", Tycomp ("->", [Tycomp ("bool",[]); Tycomp ("->", [Tycomp ("bool",[]); Tycomp ("bool", [])])])),
                            Tmconst ("A", Tycomp ("bool",[]))), 
                        Tmconst ("B", Tycomp ("bool",[])))

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* dest_imp tests *)

[<Test>]
let ``dest_imp_test``() =

    //è l'inversa della precedente
    
    let expected = (Tmconst ("A", Tycomp ("bool",[])), Tmconst ("B", Tycomp ("bool",[])))
    let actual = dest_imp (Tmcomb (
                            Tmcomb (
                                Tmconst ("==>", Tycomp ("->", [Tycomp ("bool",[]); Tycomp ("->", [Tycomp ("bool",[]); Tycomp ("bool", [])])])),
                                Tmconst ("A", Tycomp ("bool",[]))), 
                            Tmconst ("B", Tycomp ("bool",[])))
                            )

    actual
    |> should equal expected

(* is_imp tests *)

[<Test>]
let ``is_imp_true_test``() =

    is_imp ((Tmcomb (
                    Tmcomb (
                        Tmconst ("==>", Tycomp ("->", [Tycomp ("bool",[]); Tycomp ("->", [Tycomp ("bool",[]); Tycomp ("bool", [])])])),
                        Tmconst ("A", Tycomp ("bool",[]))), 
                    Tmconst ("B", Tycomp ("bool",[])))
                    )
            )
    |> should equal true

(* mk_exists tests *)

[<Test>]
let ``mk_exists_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("?",Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),Leaf,Leaf)

    let expected = Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("x", Tyvar "a"), 
                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                  )
                            )

    let actual = mk_exists (Tmvar ("x", Tyvar "a"), Tmconst ("True", Tycomp ("bool",[])))
    

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* list_mk_exists tests *)

[<Test>]
let ``list_mk_exists_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("?",Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),Leaf,Leaf)

    let expected = Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("x", Tyvar "a"), 
                                    Tmcomb (
                                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                                            Tmabs (
                                                    Tmvar ("y", Tyvar "a"), 
                                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                                  )
                                          )
                                  )
                            )

    let actual = list_mk_exists ([Tmvar ("x", Tyvar "a");Tmvar ("y", Tyvar "a")], Tmconst ("True", Tycomp ("bool",[])))
    

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* dest_exists tests *)

[<Test>]
let ``dest_exists_test``() =

    //The inverse of mk_exists

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("?",Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),Leaf,Leaf)

    let expected = (Tmvar ("x", Tyvar "a"), Tmconst ("True", Tycomp ("bool",[])))

    let actual = dest_exists
                    (
                        Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("x", Tyvar "a"), 
                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                  )
                            )
                    )
    

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* strip_exists tests *)

[<Test>]
let ``strip_exists_test``() =

    //The inverse of list_mk_exists

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("?",Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),Leaf,Leaf)

    let expected = ([Tmvar ("x", Tyvar "a");Tmvar ("y", Tyvar "a")], Tmconst ("True", Tycomp ("bool",[])))

    let actual = strip_exists
                    (
                     Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("x", Tyvar "a"), 
                                    Tmcomb (
                                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                                            Tmabs (
                                                    Tmvar ("y", Tyvar "a"), 
                                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                                  )
                                          )
                                  )
                            )
                        )
    

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* is_exists tests *)

[<Test>]
let ``is_exists_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("?",Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),Leaf,Leaf)

    let expected = true

    let actual = is_exists
                    (
                     Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("x", Tyvar "a"), 
                                    Tmcomb (
                                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                                            Tmabs (
                                                    Tmvar ("y", Tyvar "a"), 
                                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                                  )
                                          )
                                  )
                            )
                        )
    

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* term_tyvars tests *)

[<Test>]
let ``term_tyvars_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("?",Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),Leaf,Leaf)

    let expected = [Tyvar "a"]

    let actual = term_tyvars
                    (
                     Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("x", Tyvar "a"), 
                                    Tmcomb (
                                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                                            Tmabs (
                                                    Tmvar ("y", Tyvar "a"), 
                                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                                  )
                                          )
                                  )
                            )
                        )
    

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* alpha_eq tests *)

[<Test>]
let ``alpha_eq_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("?",Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),Leaf,Leaf)

    let expected = true

    let term1 =
                    (
                     Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("x", Tyvar "a"), 
                                    Tmcomb (
                                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                                            Tmabs (
                                                    Tmvar ("y", Tyvar "a"), 
                                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                                  )
                                          )
                                  )
                            )
                        )

    let term2 =
                    (
                     Tmcomb (
                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                            Tmabs (
                                    Tmvar ("z", Tyvar "a"), 
                                    Tmcomb (
                                            Tmconst ("?", Tycomp ("->",[Tycomp ("->",[Tyvar "a";Tycomp ("bool",[])]);Tycomp ("bool",[])])),
                                            Tmabs (
                                                    Tmvar ("w", Tyvar "a"), 
                                                    Tmconst ("True", Tycomp ("bool",[])) //Per comodità un termine senza variabili libere
                                                  )
                                          )
                                  )
                            )
                        )

    let actual = alpha_eq term1 term2
    

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* free_vars tests *)

[<Test>]
let ``free_vars_test``() = 

    let actual = free_vars (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmvar("a",Tycomp("bool",[]))))

    free_vars (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmvar("a",Tycomp("bool",[]))))
    |> should equal [Tmvar("a",Tycomp("bool",[]))]

(* var_free_in tests *)

[<Test>]
let ``var_free_in_true_test``() = 

    var_free_in (Tmvar("a",Tycomp("bool",[]))) (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmvar("a",Tycomp("bool",[]))))
    |> should equal true

[<Test>]
let ``var_free_in_false_test``() = 

    var_free_in (Tmvar("x",Tycomp("bool",[]))) (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmvar("a",Tycomp("bool",[]))))
    |> should equal false

(* variant tests *)

[<Test>]
let ``variant_variation_test``() = 

    variant [Tmvar("P",Tycomp("bool",[]))] (Tmvar("P",Tycomp("bool",[])))
    |> should equal (Tmvar("P'",Tycomp("bool",[])))

[<Test>]
let ``variant_no_variation_test``() = 

    let actual = variant [Tmvar("Q",Tycomp("bool",[]))] (Tmvar("P",Tycomp("bool",[])))

    variant [Tmvar("Q",Tycomp("bool",[]))] (Tmvar("P",Tycomp("bool",[])))
    |> should equal (Tmvar("P",Tycomp("bool",[])))

(* cvariant tests *)

[<Test>]
let ``cvariant_already_defined_test``() = 

    the_consts := Node (1,("P",Tycomp("bool",[])),Leaf,Leaf)

    let expected = Tmvar("P'",Tycomp("bool",[]))
    let actual = cvariant [Tmvar("Q",Tycomp("bool",[]))] (Tmvar("P",Tycomp("bool",[])))

    the_consts := (dltree_empty : dltree<string,hol_type>)
    
    actual
    |> should equal expected

(* var_inst tests *)

[<Test>]
let ``var_inst_test``() = 

    let expected = (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmconst ("True", Tycomp ("bool",[]))))
    let actual = var_inst [(Tmvar("a",Tycomp("bool",[])),Tmconst ("True", Tycomp ("bool",[])))] (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmvar("a",Tycomp("bool",[]))))
    
    actual
    |> should equal expected

//TODO: su queste procedure varrebbe la pena inserire altri testi: per esempio sulla possibile cattura di variabili legate

(* tyvar_inst tests *)

[<Test>]
let ``tyvar_inst_test``() = 

    let expected = (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmvar("a",Tycomp ("bool",[]))))
    let actual = tyvar_inst [(Tyvar "a",Tycomp ("bool",[]))] (Tmcomb (Tmconst ("~", Tycomp("->",[Tycomp("bool",[]);Tycomp("bool",[])])), Tmvar("a",Tyvar "a")))
    
    actual
    |> should equal expected

//TODO: su queste procedure varrebbe la pena inserire altri testi: per esempio sulla possibile cattura di variabili legate