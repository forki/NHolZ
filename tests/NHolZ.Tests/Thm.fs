module NHolZ.Tests.Thm

open NHolZ
open NUnit.Framework
open FsUnit

open FSharp.Compatibility.OCaml.Big_int

(* dest_thm tests *)

[<Test>]
let ``dest_thm_test``() =

    dest_thm (Theorem ([Tmvar("x",Tyvar "num")],Tmvar("x",Tyvar "num")))
    |> should equal ([Tmvar("x",Tyvar "num")],Tmvar("x",Tyvar "num"))

(* asms tests *)

[<Test>]
let ``asms_test``() =

    asms (Theorem ([Tmvar("x",Tyvar "num")],Tmvar("x",Tyvar "num")))
    |> should equal [Tmvar("x",Tyvar "num")]

(* concl tests *)

[<Test>]
let ``concl_test``() =

    concl (Theorem ([Tmvar("x",Tyvar "num")],Tmvar("x",Tyvar "num")))
    |> should equal (Tmvar("x",Tyvar "num"))

(* thm_eq tests *)

[<Test>]
let ``thm_eq_test``() =

    thm_eq (Theorem ([Tmvar("x",Tyvar "num")],Tmvar("x",Tyvar "num"))) (Theorem ([Tmvar("x",Tyvar "num")],Tmvar("x",Tyvar "num")))
    |> should equal true