module NHolZ.Tests.Names

open NHolZ
open NUnit.Framework
open FsUnit

(* is_whitespace_char tests *)

[<Test>]
let ``is_whitespace_char_test``() =

    is_whitespace_char '\t'
    |> should equal true

(* is_whitespace_char tests *)

[<Test>]
let ``is_unprintable_char_test``() =

    is_unprintable_char '\t'
    |> should equal true

(* is_lowercase tests *)

[<Test>]
let ``is_lowercase_true_test``() =

    is_lowercase 'a'
    |> should equal true

[<Test>]
let ``is_lowercase_false_1_test``() =

    is_lowercase 'A'
    |> should equal false

[<Test>]
let ``is_lowercase_false_2_test``() =

    is_lowercase '3'
    |> should equal false

(* is_uppercase tests *)

[<Test>]
let ``is_uppercase_true_test``() =

    is_uppercase 'A'
    |> should equal true

(* is_letter tests *)

[<Test>]
let ``is_letter_true_test``() =

    is_uppercase 'A'
    |> should equal true

[<Test>]
let ``is_letter_false_test``() =

    is_uppercase '1'
    |> should equal false

(* is_digit tests *)

[<Test>]
let ``is_digit_false_test``() =

    is_digit 'A'
    |> should equal false

[<Test>]
let ``is_digit_true_test``() =

    is_digit '1'
    |> should equal true

(* is_alphanum_char1 tests *)

[<Test>]
let ``is_alphanum_char1_true1_test``() =

    is_alphanum_char1 's'
    |> should equal true

[<Test>]
let ``is_alphanum_char1_true2_test``() =

    is_alphanum_char1 '_'
    |> should equal true

[<Test>]
let ``is_alphanum_char1_false1_test``() =

    is_alphanum_char1 '1'
    |> should equal false

[<Test>]
let ``is_alphanum_char1_false2_test``() =

    is_alphanum_char1 ' '
    |> should equal false

(* is_alphanum_char2 tests *)

[<Test>]
let ``is_alphanum_char2_true1_test``() =

    is_alphanum_char2 's'
    |> should equal true

[<Test>]
let ``is_alphanum_char2_true2_test``() =

    is_alphanum_char2 '2'
    |> should equal true

[<Test>]
let ``is_alphanum_char2_true3_test``() =

    is_alphanum_char2 '_'
    |> should equal true

[<Test>]
let ``is_alphanum_char2_true4_test``() =

    is_alphanum_char2 '\''
    |> should equal true

[<Test>]
let ``is_alphanum_char2_false_test``() =

    is_alphanum_char2 ' '
    |> should equal false

(* is_alphanum tests *)

[<Test>]
let ``is_alphanum_true_test``() =

    is_alphanum "s128_n"
    |> should equal true

[<Test>]
let ``is_alphanum_false_test``() =

    is_alphanum "s12@8_n"
    |> should equal false

(* is_numeric tests *)

[<Test>]
let ``is_numeric_true_test``() =

    is_numeric "128"
    |> should equal true

[<Test>]
let ``is_numeric_false_test``() =

    is_numeric "s128"
    |> should equal false

(* is_symbolic tests *)

[<Test>]
let ``is_symbolic_true_test``() =

    is_symbolic "~"
    |> should equal true

[<Test>]
let ``is_symbolic_false_test``() =

    is_symbolic "s128"
    |> should equal false

(* is_punctuation_char tests *)

[<Test>]
let ``is_punctuation_char_true_test``() =

    is_punctuation_char '('
    |> should equal true

[<Test>]
let ``is_punctuation_char_false_test``() =

    is_punctuation_char '~'
    |> should equal false

(* is_keyword tests *)

[<Test>]
let ``is_keyword_true_test``() =

    is_keyword "|-"
    |> should equal true

[<Test>]
let ``is_keyword_false_test``() =

    is_keyword "~"
    |> should equal false

(* precedence_ok tests *)

[<Test>]
let ``precedence_ok_true_test``() =

    precedence_ok (Infix (1,NonAssoc))
    |> should equal true

[<Test>]
let ``precedence_ok_false_test``() =

    precedence_ok (Infix (0,NonAssoc))
    |> should equal false

(* is_nonfix_fixity tests *)

[<Test>]
let ``is_nonfix_fixity_true_test``() =

    is_nonfix_fixity Nonfix
    |> should equal true

[<Test>]
let ``is_nonfix_fixity_false_test``() =

    is_nonfix_fixity (Infix (1,NonAssoc))
    |> should equal false

(* get_type_fixity tests *)

[<Test>]
let ``get_type_fixity_test``() =

    the_type_fixities := Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

    let expected = Infix (2,LeftAssoc)
    let actual = get_type_fixity "+"

    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* get_all_type_fixities tests *)

[<Test>]
let ``get_all_type_fixities_test``() =

    the_type_fixities := Node (1,("+",Infix (2,LeftAssoc)),Node (1,("*",Infix (3,LeftAssoc)),Leaf,Leaf),Leaf)

    let expected = [("*",Infix (3,LeftAssoc));("+",Infix (2,LeftAssoc))]
    let actual = get_all_type_fixities()

    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* get_infix_type_info tests *)

[<Test>]
let ``get_infix_type_info_success_test``() =

    the_type_fixities := Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

    let expected = (2,LeftAssoc)
    let actual = get_infix_type_info "+"

    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

//[<Test>]
//let ``get_infix_type_info_fail_test``() =
//
//    the_type_fixities := Node (1,("~",Prefix),Leaf,Leaf)
//
//    let expected = (2,LeftAssoc)
//    let actual = get_infix_type_info "~"
//
//    the_type_fixities := (dltree_empty : dltree<string,fixity>)
//
//    actual
//    |> should equal expected

(* has_nonfix_type_fixity tests *)

[<Test>]
let ``has_nonfix_type_fixity_test``() =

    the_type_fixities := Node (1,("num",Nonfix),Leaf,Leaf)

    let expected = true
    let actual = has_nonfix_type_fixity "num"

    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* has_infix_type_fixity tests *)

[<Test>]
let ``has_infix_type_fixity_test``() =

    the_type_fixities := Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

    let expected = true
    let actual = has_infix_type_fixity "+"

    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* set_type_fixity tests *)

[<Test>]
let ``set_type_fixity_success_test``() =

    set_type_fixity("+",Infix (2,LeftAssoc)) |> ignore

    let expected = Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)
    let actual = !the_type_fixities

    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

//TODO: test for nonfix and tests for failure with other fixities

(* reset_type_fixity tests *)

[<Test>]
let ``reset_type_fixity_test``() =

    the_type_fixities := Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

    reset_type_fixity "+" |> ignore

    let expected = (dltree_empty : dltree<string,fixity>)
    let actual = !the_type_fixities

//    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* set_fixity tests *)

[<Test>]
let ``set_fixity_success_test``() =

    set_fixity("+",Infix (2,LeftAssoc)) |> ignore

    let expected = Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)
    let actual = !the_fixities

    the_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* reset_fixity tests *)

[<Test>]
let ``reset_fixity_test``() =

    the_fixities := Node (1,("+",Infix (2,LeftAssoc)),Leaf,Leaf)

    reset_fixity "+" |> ignore

    let expected = (dltree_empty : dltree<string,fixity>)
    let actual = !the_fixities

//    the_type_fixities := (dltree_empty : dltree<string,fixity>)

    actual
    |> should equal expected

(* get_enum_zero_op tests *)

[<Test>]
let ``get_enum_zero_op_test``() =

    the_enum_db := Node (1,("NIL",("CONS",("[","]"))),Leaf,Leaf)

    let expected = "CONS"
    let actual = get_enum_zero_op "NIL"

    the_enum_db := (dltree_empty :  dltree<string, string * (string * string)>)

    actual
    |> should equal expected

(* get_enum_zero_brackets tests *)

[<Test>]
let ``get_enum_zero_brackets_test``() =

    the_enum_db := Node (1,("NIL",("CONS",("[","]"))),Leaf,Leaf)

    let expected = ("[","]")
    let actual = get_enum_zero_brackets "NIL"

    the_enum_db := (dltree_empty :  dltree<string, string * (string * string)>)

    actual
    |> should equal expected

(* get_all_enum_info tests *)

[<Test>]
let ``get_all_enum_info_test``() =

    the_enum_db := Node (1,("NIL",("CONS",("[","]"))),Leaf,Leaf)

    let expected = [(("NIL","CONS"),("[","]"))]
    let actual = get_all_enum_info ()

    the_enum_db := (dltree_empty :  dltree<string, string * (string * string)>)

    actual
    |> should equal expected

(* is_enum_bracket tests *)

[<Test>]
let ``is_enum_bracket_1_test``() =

    the_enum_brackets := Node (1,("[","]"),Leaf,Leaf)

    let expected = true
    let actual = is_enum_bracket "["

    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

[<Test>]
let ``is_enum_bracket_2_test``() =

    the_enum_brackets := Node (1,("[","]"),Leaf,Leaf)

    let expected = false //enumeration bracket are indexed by the opening bracket
    let actual = is_enum_bracket "]"

    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

(* get_enum_bracket_zero tests *)

[<Test>]
let ``get_enum_bracket_zero_test``() =

    the_enum_brackets := Node (1,("[","]"),Leaf,Leaf)

    let expected = "]"
    let actual = get_enum_bracket_zero "["

    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

(* is_enum_open tests *)

[<Test>]
let ``is_enum_open_true_test``() =

    the_enum_db := Node (1,("NIL",("CONS",("[","]"))),Leaf,Leaf)
    the_enum_brackets := Node (1,("[","NIL"),Node (1,("]","NIL"),Leaf,Leaf),Node (1,("[]","NIL"),Leaf,Leaf))

    let expected = true
    let actual = is_enum_open "["

    the_enum_db := (dltree_empty :  dltree<string, string * (string * string)>)
    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

[<Test>]
let ``is_enum_open_false_test``() =

    the_enum_db := Node (1,("NIL",("CONS",("[","]"))),Leaf,Leaf)
    the_enum_brackets := Node (1,("[","NIL"),Node (1,("]","NIL"),Leaf,Leaf),Node (1,("[]","NIL"),Leaf,Leaf))

    let expected = false
    let actual = is_enum_open "]"

    the_enum_db := (dltree_empty :  dltree<string, string * (string * string)>)
    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

(* is_enum_close tests *)

[<Test>]
let ``is_enum_close_true_test``() =

    the_enum_db := Node (1,("NIL",("CONS",("[","]"))),Leaf,Leaf)
    the_enum_brackets := Node (1,("]","NIL"),Node (1,("]","NIL"),Leaf,Leaf),Node (1,("[]","NIL"),Leaf,Leaf))

    let expected = true
    let actual = is_enum_close "]"

    the_enum_db := (dltree_empty :  dltree<string, string * (string * string)>)
    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

(* is_enum_openclose tests *)

[<Test>]
let ``is_enum_openclose_true_test``() =

    the_enum_db := Node (1,("NIL",("CONS",("[","]"))),Leaf,Leaf)
    the_enum_brackets := Node (1,("[","NIL"),Node (1,("]","NIL"),Leaf,Leaf),Node (1,("[]","NIL"),Leaf,Leaf))

    let expected = true
    let actual = is_enum_openclose "[]"

    the_enum_db := (dltree_empty :  dltree<string, string * (string * string)>)
    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

(* check_bracket_name tests *)

[<Test>]
let ``check_bracket_name_success_test``() =

    the_enum_brackets := Node (1,("[","NIL"),Node (1,("]","NIL"),Leaf,Leaf),Node (1,("[]","NIL"),Leaf,Leaf))

    let expected = ()
    let actual = check_bracket_name "{"

    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected

[<Test>]
let ``check_bracket_name_fail1_test``() =

    the_enum_brackets := Node (1,("[","NIL"),Node (1,("]","NIL"),Leaf,Leaf),Node (1,("[]","NIL"),Leaf,Leaf))

    (fun () -> (check_bracket_name "[") |> ignore)
    |> should throw typeof<HolFail>
    
    the_enum_brackets := (dltree_empty : dltree<string, string>)

(* set_enum_brackets tests *)

[<Test>]
let ``set_enum_brackets_success_test``() =

    set_enum_brackets ("CONS","NIL") ("[","]") |> ignore

    let expected = Node (2,("[]","NIL"),Node (1,("[","NIL"),Leaf,Leaf),Node (1,("]","NIL"),Leaf,Leaf))
    let actual = !the_enum_brackets

    the_enum_brackets := (dltree_empty : dltree<string, string>)

    actual
    |> should equal expected
