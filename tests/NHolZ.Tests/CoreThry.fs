module NHolZ.Tests.CoreThry

open NHolZ
open NUnit.Framework
open FsUnit

open FSharp.Compatibility.OCaml.Big_int
open System.Numerics

open NUnit.Framework
open FsUnit

(* lexer_new tests *)

[<Test>]
let ``true_tmtest``() =

    true
    |> should equal true

(* test commit *)