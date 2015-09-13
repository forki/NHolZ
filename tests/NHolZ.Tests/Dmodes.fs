module NHolZ.Tests.Dmodes

open NHolZ
open NUnit.Framework
open FsUnit

(* set_type_annotation_mode tests *)

[<Test>]
let ``set_type_annotation_mode_test``() =

    set_type_annotation_mode Full |> ignore
    let expected = Full
    let actual = !the_type_annotation_mode

    the_type_annotation_mode := Minimal

    actual
    |> should equal expected

(* get_type_annotation_mode tests *)

[<Test>]
let ``get_type_annotation_mode_test``() =

    let expected = Minimal
    let actual = get_type_annotation_mode ()

    actual
    |> should equal expected

(* set_tyvar_marking_mode tests *)

[<Test>]
let ``set_tyvar_marking_mode_test``() =

    set_tyvar_marking_mode Minimal |> ignore
    let expected = Minimal
    let actual = !the_tyvar_marking_mode

    the_tyvar_marking_mode := Full

    actual
    |> should equal expected

(* get_tyvar_marking_mode tests *)

[<Test>]
let ``get_tyvar_marking_mode_test``() =

    let expected = Full
    let actual = get_tyvar_marking_mode ()

    actual
    |> should equal expected

(* set_var_marking_mode tests *)

[<Test>]
let ``set_var_marking_mode_test``() =

    set_var_marking_mode Full |> ignore
    let expected = Full
    let actual = !the_var_marking_mode

    the_var_marking_mode := Minimal

    actual
    |> should equal expected

(* get_var_marking_mode tests *)

[<Test>]
let ``get_var_marking_mode_test``() =

    let expected = Minimal
    let actual = get_var_marking_mode ()

    actual
    |> should equal expected

(* set_language_level_mode tests *)

[<Test>]
let ``set_language_level_mode_test``() =

    set_language_level_mode Minimal |> ignore
    let expected = Minimal
    let actual = !the_language_level_mode

    the_language_level_mode := Full

    actual
    |> should equal expected

(* get_language_level_mode tests *)

[<Test>]
let ``get_language_level_mode_test``() =

    let expected = Full
    let actual = get_language_level_mode ()

    actual
    |> should equal expected