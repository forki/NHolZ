module NHolZ.Tests

open NHolZ
open NUnit.Framework
open FsUnit

(* check tests *)

[<Test>]
[<ExpectedException(typeof<HolFail>, ExpectedMessage = "[HZ] FAIL: check - Test fails")>]
let ``check_fail``() =

    check ((=) 1) 2
    |> ignore

[<Test>]
let ``check_success``() =

    check ((=) 1) 1
    |> should equal 1
