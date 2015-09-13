module NHolZ.Tests.Exn

open NHolZ
open NUnit.Framework
open FsUnit

[<Test>]
[<ExpectedException(typeof<HolFail>, ExpectedMessage = "[HZ] FAIL: func - Empty list")>]
let ``Exn1``() =
    
    let func xs = 
        match xs with
        | [] -> hol_fail ("func","Empty list")
        | _ -> 1 + 2

    func [] 
    |> ignore