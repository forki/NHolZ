module NHolZ.Tests.Reader

open NHolZ
open NUnit.Framework
open FsUnit

(* dltree_empty tests *)

[<Test>]
let ``ReformulateRHS_test``() =

    let lhdFunc x = "pippo " + x
    let readerFn x = ("pippo", x)

    (lhdFunc @| readerFn) "prova"
    |> should equal ("pippo pippo", "prova")

[<Test>]
let ``Exception if RHS succeeds test``() =

    let lhdFunc x = "pippo " + x
    let readerFn x = ("pippo", x)

    (lhdFunc @!| readerFn) "prova"
    |> should equal "pippo pippo"

[<Test>]
let ``Alternation test``() =

    let read_fn1 x = 
        match x with
        | "pippo" -> raise ReadFail
        | _ -> x

    let readerFn2 x = "pippo " + x

    (!|||) read_fn1  readerFn2 "pippo"
    |> should equal "pippo pippo"

//    (read_fn1 (!|||) readerFn2) "pippo"
//    |> should equal "pippo pippo"

[<Test>]
let ``Serial !>>> test``() =

    let read_fn1 (x:string) = 
        let x1 = x.Substring(0,2)
        let x2 = x.Replace(x1,"")
        x1,x2

    let read_fn2 (x:string) = 
        let x1 = x.Substring(0,2)
        let x2 = x.Replace(x1,"")
        x1,x2

    (!>>>) read_fn1 read_fn2 "pippo"
    |> should equal (("pi", "pp"), "o")
