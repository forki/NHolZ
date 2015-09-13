module NHolZ.Tests.Lexer

open NHolZ
open NUnit.Framework
open FsUnit

(* funcPunct tests *)

[<Test>]
let ``funcPunct_test``() =

    lex ['(';')';',']
    |> should equal [Resword_tok "("; Resword_tok ")"; Resword_tok ","]

(* funcAlphanumeric tests *)

[<Test>]
let ``funcAlphanumeric_test``() =

    lex ['_';'b';'c']
    |> should equal [Ident_tok (false, No_mark, "_bc")]

(* funcNumeric tests *)

[<Test>]
let ``funcNumeric_test``() =

    lex ['1';'2';'3']
    |> should equal [Numeric_tok (false, No_mark, "123")]

(* funcSymbolic tests *)

[<Test>]
let ``funcSymbolic_test``() =

    lex ['!';'#';'&';'*';'+';'-';'.';'/';';';'<';'=';'>';'?';'@';'[';'\\';']';'^';'{';';';'}';'~']
    |> should equal [Ident_tok (false, No_mark, "!#&*+-./;<=>?@[\\]^{;}~")]