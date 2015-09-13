module NHolZ.Tests.Type

open NHolZ
open NUnit.Framework
open FsUnit

open FSharp.Compatibility.OCaml.Big_int

(* prim_get_tyconst_arity tests *)

[<Test>]
let ``prim_get_tyconst_arity_test``() =

    the_tyconsts := Node (1,("A",big_int_of_string "1"),Leaf,Node (1,("B",big_int_of_string "3"),Leaf,Leaf))
    let actual = prim_get_tyconst_arity "B"

    the_tyconsts := (dltree_empty : dltree<string,big_int>)

    actual
    |> should equal (big_int_of_string "3")

(* prim_get_all_tyconsts tests *)

[<Test>]
let ``prim_get_all_tyconsts_test``() =

    the_tyconsts := Node (1,("A",big_int_of_string "1"),Leaf,Node (1,("B",big_int_of_string "3"),Leaf,Leaf))
    let actual = prim_get_all_tyconsts()

    the_tyconsts := (dltree_empty : dltree<string,big_int>)

    actual
    |> should equal [("A",big_int_of_string "1");("B",big_int_of_string "3")]

(* is_tyconst_name tests *)

[<Test>]
let ``is_tyconst_name_test``() =

    the_tyconsts := Node (1,("A",big_int_of_string "1"),Node (1,("B",big_int_of_string "0"),Leaf,Leaf),Node (1,("C",big_int_of_string "3"),Leaf,Leaf))
    let actual = is_tyconst_name "C"

    the_tyconsts := (dltree_empty : dltree<string,big_int>)

    actual
    |> should equal true

(* prim_new_tyconst tests *)

[<Test>]
let ``prim_new_tyconst_test``() =

    let expected = Node (1,("C",big_int_of_string "3"),Leaf,Leaf)
    prim_new_tyconst("C",big_int_of_string "3") |> ignore

    let actual = !the_tyconsts

    the_tyconsts := (dltree_empty : dltree<string,big_int>)

    actual
    |> should equal expected

(* mk_var_type tests *)

[<Test>]
let ``mk_var_type_test``() =

    mk_var_type "A"
    |> should equal (Tyvar "A")

(* dest_var_type tests *)

[<Test>]
let ``dest_var_typee_test``() =

    dest_var_type (Tyvar "A")
    |> should equal "A"

(* is_var_type tests *)

[<Test>]
let ``is_var_type_test``() =

    is_var_type (Tyvar "A")
    |> should equal true

(* mk_comp_type tests *)

[<Test>]
let ``mk_comp_type_test``() =

    the_tyconsts := Node (1,("C",big_int_of_string "2"),Leaf,Leaf)

    let expected = Tycomp ("C",[Tyvar "A"; Tyvar "C"])
    let actual = mk_comp_type("C",[Tyvar "A"; Tyvar "C"])

    the_tyconsts := (dltree_empty : dltree<string,big_int>)

    actual
    |> should equal expected

(* dest_comp_type tests *)

[<Test>]
let ``dest_comp_type_test``() =

    dest_comp_type (Tycomp ("C",[Tyvar "A"; Tyvar "C"]))
    |> should equal ("C",[Tyvar "A"; Tyvar "C"])

(* dest_comp_type tests *)

[<Test>]
let ``is_comp_type_test``() =

    is_comp_type (Tycomp ("C",[Tyvar "A"; Tyvar "C"]))
    |> should equal true

(* type_eq tests *)

[<Test>]
let ``type_eq_test``() =

    type_eq (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "C"]))
    |> should equal true

(* type_lt tests *)

[<Test>]
let ``type_lt_true_test``() =

    type_lt (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "D"]))
    |> should equal true

[<Test>]
let ``type_lt_false1_test``() =

    type_lt (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "C"]))
    |> should equal false

[<Test>]
let ``type_lt_false2_test``() =

    type_lt (Tycomp ("B",[Tyvar "A"; Tyvar "C"])) (Tycomp ("B",[Tyvar "A"; Tyvar "A"]))
    |> should equal false

(* mk_fun_type tests *)

[<Test>]
let ``mk_fun_type_test``() =

    mk_fun_type (Tyvar "A", Tyvar "C")
    |> should equal (Tycomp ("->",[Tyvar "A";Tyvar "C"]))

(* dest_fun_type tests *)

[<Test>]
let ``dest_fun_type_test``() =

    dest_fun_type (Tycomp ("->",[Tyvar "A";Tyvar "C"]))
    |> should equal (Tyvar "A", Tyvar "C")

(* is_fun_type tests *)

[<Test>]
let ``is_fun_type_true_test``() =

    is_fun_type (Tycomp ("->",[Tyvar "A";Tyvar "C"]))
    |> should equal true

[<Test>]
let ``is_fun_type_false_test``() =

    is_fun_type (Tyvar "A")
    |> should equal false

(* type_inst tests *)

[<Test>]
let ``type_inst_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)

    let expected = (Tycomp ("->",[Tyvar "C";Tyvar "B"]))
    let actual = type_inst [(Tyvar "A",Tyvar "C")] (Tycomp ("->",[Tyvar "A";Tyvar "B"]))

    the_tyconsts := (dltree_empty : dltree<string,big_int>)

    actual
    |> should equal expected