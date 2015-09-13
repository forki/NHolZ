module NHolZ.Tests.Parser

open NHolZ
open NUnit.Framework
open FsUnit

open FSharp.Compatibility.OCaml.Big_int
open System.Numerics

open NUnit.Framework
open FsUnit

let init () = 

        the_type_fixities := 
              Node
                (1,("#", Infix (10, RightAssoc)),Leaf,
                 Node (1,("->", Infix (5, RightAssoc)),Leaf,Leaf))

        the_fixities := 
          Node
            (4,("==>", Infix (10, RightAssoc)),
             Node
               (3,(@"/\", Infix (20, RightAssoc)),
                Node
                  (2,("+", Infix (50, LeftAssoc)),
                   Node
                     (1,("!", Binder),Leaf,
                      Node (1,("*", Infix (55, LeftAssoc)),Leaf,Leaf)),
                   Node (1,("-", Infix (50, LeftAssoc)),Leaf,Leaf)),
                Node
                  (2,("<=>", Infix (5, NonAssoc)),
                   Node
                     (1,("<", Infix (40, NonAssoc)),Leaf,
                      Node (1,("<=", Infix (40, NonAssoc)),Leaf,Leaf)),
                   Node (1,("=", Infix (30, NonAssoc)),Leaf,Leaf))),
             Node
               (3,("@", Binder),
                Node
                  (2,("?", Binder),
                   Node
                     (1,(">", Infix (40, NonAssoc)),Leaf,
                      Node (1,(">=", Infix (40, NonAssoc)),Leaf,Leaf)),
                   Node (1,("?!", Binder),Leaf,Leaf)),
                Node
                  (2,(@"\/", Infix (15, RightAssoc)),
                   Node (1,("EXP", Infix (60, LeftAssoc)),Leaf,Leaf),
                   Node (1,("~", Prefix),Leaf,Leaf))))

        the_tyconsts := 
          Node
            (2,("->", big_int_of_string "2"),Node (1,("#", big_int_of_string "2"),Leaf,Leaf),
             Node
               (2,("ind", big_int_of_string "0"),Node (1,("bool", big_int_of_string "0"),Leaf,Leaf),
                Node (1,("nat", big_int_of_string "0"),Leaf,Leaf)))

(* parse_type *)
[<Test>]
let ``parse_type_test``() =

    init ()

    let expected = Tycomp ("->", [Tycomp ("bool", []); Tycomp ("bool", [])])

    parse_type("bool->bool")
    |> should equal expected

(* lexer_new tests *)

[<Test>]
let ``lexer_new_test``() =

    let expected = 
        [
            Ident_tok (false, No_mark, "nat"); Ident_tok (false, No_mark, "->");
            Ident_tok (false, No_mark, "nat"); Ident_tok (false, No_mark, "->");
            Ident_tok (false, No_mark, "bool")
        ]

    (lex <* char_explode) "nat->nat->bool"
    |> should equal expected


(* parse_pretype tests *)

[<Test>]
let ``parse_pretype1_test``() =

    prim_new_tyconst("->",big_int_of_string "2") |> ignore
    prim_new_tyconst("nat",big_int_of_string "0") |> ignore
    prim_new_tyconst("bool",big_int_of_string "0") |> ignore
    set_type_fixity("->",Infix (5,RightAssoc)) |> ignore

    let expected = 
        Ptycomp ("->",
            [
                Ptycomp ("nat", []);
                Ptycomp ("bool", [])
            ]
        )

    let actual = parse_pretype ((lex <* char_explode) "nat->bool")

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

[<Test>]
let ``parse_pretype2_test``() =

    prim_new_tyconst("->",big_int_of_string "2") |> ignore
    prim_new_tyconst("nat",big_int_of_string "0") |> ignore
    prim_new_tyconst("bool",big_int_of_string "0") |> ignore
    set_type_fixity("->",Infix (5,RightAssoc)) |> ignore

    let expected = 
        Ptycomp ("->",
            [
                Ptycomp ("nat", []);
                Ptycomp("->", [Ptycomp ("nat", []); Ptycomp ("bool", [])])
            ]
        )

    let actual = parse_pretype ((lex <* char_explode) "nat->nat->bool")

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* parse_type tests *)

[<Test>]
let ``parse_type_'_test``() =

    prim_new_tyconst("->",big_int_of_string "2") |> ignore
    prim_new_tyconst("nat",big_int_of_string "0") |> ignore
    prim_new_tyconst("bool",big_int_of_string "0") |> ignore
    set_type_fixity("->",Infix (5,RightAssoc)) |> ignore

    let expected = Tycomp ("->",[Tyvar "a"; Tycomp ("->",[Tyvar "a"; Tycomp ("bool",[])])])

    let actual = parse_type("'a -> 'a -> bool")

    the_tyconsts := (dltree_empty : dltree<string,big_int>)
    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected