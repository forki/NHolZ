namespace System
open System.Reflection

[<assembly: AssemblyTitleAttribute("NHolZ")>]
[<assembly: AssemblyProductAttribute("NHolZ")>]
[<assembly: AssemblyDescriptionAttribute("A porting in F# of the "Original OCaml version of HOL Zero" by Mark Adams")>]
[<assembly: AssemblyVersionAttribute("1.0")>]
[<assembly: AssemblyFileVersionAttribute("1.0")>]
do ()

module internal AssemblyVersionInformation =
    let [<Literal>] Version = "1.0"
