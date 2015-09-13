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

parse_term("!x y z. x < y /\ y < z ==> x < z");;

(**
Se si immette un termine mal formato si ricevera' un messaggio di errore:
*)
parse_term("x=");;
// - NHolZ.Exn+HolErr: [HZ] SYNTAX ERROR: Unexpected end of quotation instead of RHS for infix "="

(**
Si noti che i messaggi specifici di NHolZ, diversamente da quelli che derivano dall'interprete 
F# in generale hanno il prefisso *[HZ]*. Questo vale per tutti i messaggi riportati da NHolZ, 
inclusi messaggi di errore, warning e feedback generici all'utente.

HOL e' un linguaggio tipizzato, cosi' ogni termine e sottotermine ha un tipo,
e i termini devono essere costruiti in modo da avere un tipo corretto. Questo
impedisce la costruzione di enunciati privi di significato come *3 e' uguale a vero*.
*)
parse_term("3 = true");;
// - NHolZ.Exn+HolErr: [HZ] TYPE ERROR: Function subterm domain type incompatible with argument 
//   subterm type

(**
I sottotermini nelle *term quotation* possono essere annotati per indicare il loro
tipo, facendo seguire al sottotermine il simbolo di i due punti (*:*) e poi il suo
tipo, il tutto chiuso tra parentesi. Di default, i termini sono ristampati a video con
annotazioni di tipo sufficienti almeno ad evitare qualsiasi ambiguita' circa il tipo di
ogni sottotermine.
*)
parse_term("!(x:nat) (y:nat). x = y");;
// - val it : term = `!(x:nat) y. x = y`

(**
Il meccanismo di inferenza del tipo e' usato per risolvere i tipi nei termini.Ad
ogni termine inputato senza annotazioni di tipo sufficienti sono assegnate delle
variabili di tipo numerate per tutti i tipi non determinabili.
*)
parse_term("!x y. x = y");;
// - val it : term = `!(x:'1) y. x = y`