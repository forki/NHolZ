(*** hide ***)
// This block of code is omitted in the generated HTML documentation. Use 
// it to define helpers that you do not want to show in the documentation.
#I "../../bin"

(**
NHolZ
======================

Descrizione

HOL Zero e' un dimostratore di teoremi, cioe' un programma che supporta la dimostrazione 
formale di teoremi e lo sviluppo di teorie nella logica HOL. Come l'autore evidenzia, si 
tratta di un dimostratore di teoremi relativamente semplice che lo rende anche adatto 
a scopi educativi per aiutare logici, programmatori e informatici, che lo desiderano, a 
imparare come funziona un dimostratore di teoremi.

NHolZ e' un porting in F# di HOL Zero, ed ha avuto per me il duplice scopo di imparare l'F# 
portando a termine il porting di un progetto esistente in un altro linguaggio simile all'F# 
e d'imparare il funzionamento del contenuto stesso del programma: la dimostrazione formale e 
meccanizzata di teoremi.

In questo lavoro mi sono ispirato all'analogo porting del codice e degli esempi del libro 
di John Harrison "[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/index.html)" 
portato a termine da [Jack Pappas](https://github.com/jack-pappas), [Eric Taucher](https://github.com/EricGT), [Anh-Dung Phan](https://github.com/dungpa) 
e disponibile al link http://github.com/jack-pappas/fsharp-logic-examples.

 1. [Introduzione a HOL](introduzione_a_hol.html)
 2. [Termini, Tipi e Teoremi](termini_tipi_teoremi.html): le espressioni nel linguaggio HOL.

<!--<div class="row">
  <div class="span1"></div>
  <div class="span6">
    <div class="well well-small" id="nuget">
      The NHolZ library can be <a href="https://nuget.org/packages/NHolZ">installed from NuGet</a>:
      <pre>PM> Install-Package NHolZ</pre>
    </div>
  </div>
  <div class="span1"></div>
</div>-->

Ciò che segue è tutto da aggiornare

Example
-------

This example demonstrates using a function defined in this sample library.

*)
#r "NHolZ.dll"
open NHolZ

printfn "hello = %i" <| Library.hello 0

(**
Some more info

Samples & documentation
-----------------------

The library comes with comprehensible documentation. 
It can include tutorials automatically generated from `*.fsx` files in [the content folder][content]. 
The API reference is automatically generated from Markdown comments in the library implementation.

 * [Tutorial](tutorial.html) contains a further explanation of this sample library.

 * [API Reference](reference/index.html) contains automatically generated documentation for all types, modules
   and functions in the library. This includes additional brief samples on using most of the
   functions.
 
Contributing and copyright
--------------------------

The project is hosted on [GitHub][gh] where you can [report issues][issues], fork 
the project and submit pull requests. If you're adding a new public API, please also 
consider adding [samples][content] that can be turned into a documentation. You might
also want to read the [library design notes][readme] to understand how it works.

The library is available under Public Domain license, which allows modification and 
redistribution for both commercial and non-commercial purposes. For more information see the 
[License file][license] in the GitHub repository. 

  [content]: https://github.com/fsprojects/NHolZ/tree/master/docs/content
  [gh]: https://github.com/fsprojects/NHolZ
  [issues]: https://github.com/fsprojects/NHolZ/issues
  [readme]: https://github.com/fsprojects/NHolZ/blob/master/README.md
  [license]: https://github.com/fsprojects/NHolZ/blob/master/LICENSE.txt
*)
