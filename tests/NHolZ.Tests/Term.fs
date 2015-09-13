module NHolZ.Tests.Term

open NHolZ
open NUnit.Framework
open FsUnit

open FSharp.Compatibility.OCaml.Big_int

(* type_inst tests *)

[<Test>]
let ``get_const_gtype_test``() =

    the_consts := Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

    let expected = Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])
    let actual = get_const_gtype "+"

    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* get_all_consts tests *)

[<Test>]
let ``get_all_consts_test``() =

    the_consts := Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

    let expected = [("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))]
    let actual = get_all_consts()

    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* is_const_name tests *)

[<Test>]
let ``is_const_name_test``() =

    the_consts := Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

    let expected = true
    let actual = is_const_name "+"

    the_consts := (dltree_empty : dltree<string,hol_type> )

    actual
    |> should equal expected

(* prim_new_const tests *)

[<Test>]
let ``prim_new_const_test``() =

    prim_new_const("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])) |> ignore

    let expected = Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)
    let actual = !the_consts

    the_consts := (dltree_empty : dltree<string,hol_type> )

    actual
    |> should equal expected

(* term_eq tests *)

[<Test>]
let ``term_eq_test``() =

    term_eq (Tmconst ("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))) 
        (Tmconst ("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])))
    |> should equal true

(* term_lt tests *)

[<Test>]
let ``term_lt_true_test``() =

    term_lt (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"]))) 
        (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "D"])))
    |> should equal true

[<Test>]
let ``term_lt_false1_test``() =

    term_lt (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"]))) 
        (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"])))
    |> should equal false

[<Test>]
let ``term_lt_false2_test``() =

    term_lt (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "C"]))) 
        (Tmconst ("B",Tycomp ("B",[Tyvar "A"; Tyvar "A"])))
    |> should equal false

(* type_of tests *)

[<Test>]
let ``type_of variable/constant test``() =

    type_of (Tmconst ("+", Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])))
    |> should equal (Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))

[<Test>]
let ``type_of function application test``() =

    let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
    let func2 = Tmconst ("1", Tyvar "num")
    let funcApp = Tmcomb (func1, func2)

    type_of funcApp
    |> should equal (Tyvar "string")

[<Test>]
let ``type_of lambda abstraction test``() =

    let var = Tmvar ("x", Tyvar "num")
    let trm = Tmconst ("1", Tyvar "num")
    let lambdaAbstr = Tmabs (var, trm)

    type_of lambdaAbstr
    |> should equal (Tycomp ("->",[Tyvar "num";Tyvar "num"]))

(* mk_gconst tests *)

[<Test>]
let ``mk_gconst_test``() =

    the_consts := Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

    let expected = Tmconst ("+", Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"]))
    let actual = mk_gconst "+"

    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* mk_iconst tests *)

[<Test>]
let ``mk_iconst_test``() =

    the_tyconsts := Node (1,("->",big_int_of_string "2"),Leaf,Leaf)
    the_consts := Node (1,("+",Tycomp ("->",[Tycomp ("->",[Tyvar "num";Tyvar "num"]);Tyvar "num"])),Leaf,Leaf)

    let expected = Tmconst ("+", Tycomp ("->",[Tycomp ("->",[Tyvar "bool";Tyvar "bool"]);Tyvar "bool"]))
    let actual = mk_iconst ("+", [(Tyvar "num",Tyvar "bool")])

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_consts := (dltree_empty : dltree<string,hol_type>)

    actual
    |> should equal expected

(* mk_comb tests *)

[<Test>]
let ``mk_comb test``() =

    let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
    let func2 = Tmconst ("1", Tyvar "num")
    let funcApp = Tmcomb (func1, func2)

    mk_comb (func1,func2)
    |> should equal funcApp

(* dest_comb tests *)

[<Test>]
let ``dest_comb test``() =

    let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
    let func2 = Tmconst ("1", Tyvar "num")
    let funcApp = Tmcomb (func1, func2)

    dest_comb funcApp
    |> should equal (func1,func2)

(* is_comb tests *)

[<Test>]
let ``is_comb true test``() =

    let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
    let func2 = Tmconst ("1", Tyvar "num")
    let funcApp = Tmcomb (func1, func2)

    is_comb funcApp
    |> should equal true

[<Test>]
let ``is_comb false test``() =

    let func1 = Tmconst ("toString", Tycomp ("->",[Tyvar "num";Tyvar "string"]))
    let func2 = Tmconst ("1", Tyvar "num")
    let funcApp = Tmcomb (func1, func2)

    is_comb func1
    |> should equal false

(* mk_abs tests *)

[<Test>]
let ``mk_abs test``() =

    let var = Tmvar ("x", Tyvar "num")
    let trm = Tmconst ("1", Tyvar "num")
    let lambdaAbstr = Tmabs (var, trm)

    mk_abs (var,trm)
    |> should equal lambdaAbstr