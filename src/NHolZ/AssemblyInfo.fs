namespace System
open System.Reflection

[<assembly: AssemblyTitleAttribute("NHolZ")>]
[<assembly: AssemblyProductAttribute("NHolZ")>]
[<assembly: AssemblyDescriptionAttribute("A porting in F# of the "Original OCaml version of HOL Zero" by Mark Adams")>]
[<assembly: AssemblyVersionAttribute("0.0.1")>]
[<assembly: AssemblyFileVersionAttribute("0.0.1")>]
do ()

module internal AssemblyVersionInformation =
    let [<Literal>] Version = "0.0.1"
