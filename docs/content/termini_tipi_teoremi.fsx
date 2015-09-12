(*** hide ***)
// This block of code is omitted in the generated HTML documentation. Use 
// it to define helpers that you do not want to show in the documentation.
#I "../../bin/NHolZ"

(**
Tipi, Termini e Teoremi
========================

Le espressioni nel linguaggio HOL sono chiamati termini HOL. In NHolZ i termini sono scritti 
utilizzando una serie di caratteri ASCII in stringhe passate come argomento alla funzione 
`parse_term`. Questo e' diverso dalle implementazioni classiche di HOL in SML o OCaml 
che di solito usano le cosiddette *term quotation* in cui i termini sono racchiusi da simboli 
di citazione come ad esempio apici acuti '`' ed e' dovuto alla mancanza, o possibilmente alla 
mia non conoscenza, dell'esistenza di una funzionalita' analoga in F#. Nel momento in cui si 
immette un termine in una sessione NHolZ, questo viene controllato e ristampato a video.

La sintassi dei termini e' semplice e intuitiva. Per esempio, il seguente termine significa 
'per tutti i numeri naturali *x*, *y* e *z*, se *x* e' minore di *y* e *y* e' 
minore di *z* allora *x* e' minore di *z*:

*)
#r "NHolZ.dll"
#load "initialization.fsx"
open NHolZ

parse_term("!x y z. x < y /\ y < z ==> x < z")
(**
Some more info
*)