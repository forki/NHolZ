(*** hide ***)
// This block of code is omitted in the generated HTML documentation. Use 
// it to define helpers that you do not want to show in the documentation.
#I "../../../bin/NHolZ"
#r "NHolZ.dll"
#load "../initialization.fsx"
open NHolZ

(**
Il modulo Dltree
========================

 1. [Introduzione agli Alberi AA](dltree.html#intro)
 2. [Il datatype dltree](dltree.html#datatype)
 3. [Operazioni base sui sotto alberi](dltree.html#operazioni)

<a id="intro">Introduzione agli Alberi AA</a>
--------------------------

Il modulo dltree implementa il datatype e le funzioni per la gestione di 
*alberi AA* (chiamati anche alberi di Anderson). Si tratta di *alberi 
binari auto-bilanciati* che memorizzano informazioni su nodi ordinati 
in base a un indice e che permettono una ricerca efficiente.

Con bilanciati s'intende che si cerca di mantenere simile la 
profondita' dei vari rami nell'albero e in particolare negli alberi AA 
la massima distanza dalla radice a una foglia non e' piu' grande del 
doppio della distanza minima: il ramo piu' lungo non e' comunque piu' 
lungo del doppio del ramo piu' corto. Questa proprieta', si ottiene 
garantendo la cosiddetta *invariante AA*, e permette di implementare 
operazioni di ricerca, inserimento e cancellazione in questi alberi 
con una complessita' di tempo spazio che nel peggiore dei casi e' pari 
a O(log n).

Con *invariante AA* si intendono quattro aspetti che devono essere 
mantenuti negli alberi ad ogni operazione eseguita su di essi:

1. il livello di ogni foglia deve essere 0;
2. il livello di ogni nodo sul ramo sinistro deve essere uguale a quello del suo padre meno uno.
3. il livello di ogni nodo sul ramo destro deve essere uguale a quello del suo padre o a quello del suo padre meno uno;
4. il livello di ogni nodo sul ramo piu' a destra nell'albero deve essere minore di quello dei suoi nonni.

In questo modo il livello rappresenta la distanza dal nodo alla foglia piu' a 
sinistra discendente dal nodo, e un limite superiore di meta' della 
distanza dal nodo alla sua foglia discendente piu' a destra. Cosi' il 
livello e' un limite superiore di meta' della profonodita' dell'albero, ed e' 
anche un limite superiore per la differenza tra le profondita' delle foglie 
piu' profonde e di quelle meno profonde.

Le operazioni di inserimento e cancellazione preservano l'invariante AA 
applicando una combinazione di due operazioni di ribilanciamento - `skew` 
e `split` - una volta che un elemento e' stato inserito/cancellato. `skew` e 
`split` hanno entrambe una complessita' tempo/spazio O(1), e il numero di 
nodi su cui hanno bisogno di operare per un inserimento o una cancellazione e' al 
massimo O(log n), assicurando cosi' che l'inserimento e la cancellazione 
siano O(log n). La particolare combinazione di `skew` e `split` impiegata 
dipende dal fatto che sia stata eseguita una cancellazione oppure un 
inserimento. 

Si noti che in un albero di ricerca binario classico per assicurare una corretta 
funzionalita' (cioe' che le voci possano essere cercate in base agli inserimenti e alle 
cancellazioni che sono avvenute), e' sufficiente che le operazioni di inserimento e 
cancellazione preservino un corretto ordinamento rispetto alla relazione di *<*. 
In altre parole, l'invariante AA e' puramente per question di efficienza, e non aggiunge 
nulla alla correttezza. Si noti inoltre che le due operazioni di ribilanciamento preservano 
tutte un corretto ordinamento. 

*)

(** 
<a id="datatype">Il datatype dltree</a>
---------------------------

Il datatype `dltree` e' la nostra specifica implementazione degli alberi AA per il 
nostro sistema: un datatype di albero di ricerca binario, dove ad 
ogni nodo sono mantenuti un indice e un elemento (una coppia in questo caso per l'uso 
specifico che sara' fatto di questra struttura nel sistema), e le foglie non hanno 
alcuna informazione. Il confronto tra indici e' fatto usando la relazione 
di oridinamento totale polimorfica '(<)'. Ogni nodo mantiene anche un 
intero per il suo livello AA, per poter mantenere l'invariante AA. Si noti 
che non c'e' alcuna necessita' che le foglie mantengano il proprio livello 
perche' esso e' sempre 0.

Ogni nodo (`Node`) nell'albero e' una tupla il cui primo elemento `int` e' l'intero che 
rappresenta il livello del nodo nell'albero; il secondo elemento `('a * 'b)` e' una 
coppia: l'informazione che vogliamo immagazzinare nel nodo (il motivo 
per cui viene immagazzinata una coppia dipende dal particolare uso che 
vogliamo fare del dltree nel sistema); i due elmenti successivi `dltree<'a,'b>` sono 
rispettivamente il sottoalbero sinistro e destro del nodo. Le foglie (`Leaf`) non mantengono 
alcuna informazione e indicano solo la terminazione dei rami:

*)

type dltree'<'a,'b> =
    | Node' of int * ('a * 'b) * dltree'<'a,'b> * dltree'<'a,'b>
    | Leaf'

(**
Con la funzione `dltree_empty` possiamo creare un albero vuoto che conterra' inzialmente 
solo una foglia e che possiamo usare come contenitore inziale vuoto a cui poter aggiungere 
informazioni:
*)

let dltree_empty' = Leaf

(**
Con la funzione `dltree_elems` possiamo estrarre l'informazione mantenuta in un dato albero di ricerca 
binario sotto forma di una lista di associazione in cui gli elementi dell'albero compariranno secondo il 
loro indice all'interno dell'albero in una lettura da sinistra a destra:
*)

let dltree_elems' tr = 
    /// Funzione tail-ricorsiva a supporto della definizione di dltree_elems
    let rec dltree_elems0' tr xys0 =
        match tr with
        | Node' (_,xy,tr1,tr2) -> dltree_elems0' tr1 (xy::(dltree_elems0' tr2 xys0))
        | Leaf'                -> xys0
    dltree_elems0' tr []

(**
Per capirne lo scopo, creiamo ad esempio un albero vuoto e inseriamo qualche informazione: 
ad esempio cinque coppie di stringhe (si notino di passaggio gli indici associati a ciascuna coppia 
inserita nell'albero). Per farlo useremo la funzione `dltree_insert` che e' spiegata 
piu' avanti:
*)

let tr = dltree_empty;;
// - val tr : dltree<'a,'b>
let tr1 = dltree_insert ("a","b") tr;;
// - val tr1 : dltree<string,string> = Node (1,("a", "b"),Leaf,Leaf)
let tr2 = dltree_insert ("c","d") tr1;;
// - val tr2 : dltree<string,string> =
//    Node (1,("a", "b"),Leaf,Node (1,("c", "d"),Leaf,Leaf))
let tr3 = dltree_insert ("e","e") tr2;;
// - val tr3 : dltree<string,string> =
//     Node
//       (2,("c", "d"),Node (1,("a", "b"),Leaf,Leaf),Node (1,("e", "e"),Leaf,Leaf))
let tr4 = dltree_insert ("w","z") tr3;;
// - val tr4 : dltree<string,string> =
//     Node
//       (2,("c", "d"),Node (1,("a", "b"),Leaf,Leaf),
//        Node (1,("e", "e"),Leaf,Node (1,("w", "z"),Leaf,Leaf)))
let tr5 = dltree_insert ("o","e") tr4;;
// - val tr5 : dltree<string,string> =
//     Node
//       (2,("c", "d"),Node (1,("a", "b"),Leaf,Leaf),
//        Node
//          (2,("o", "e"),Node (1,("e", "e"),Leaf,Leaf),
//           Node (1,("w", "z"),Leaf,Leaf)))
dltree_elems tr5;;
// - val it : (string * string) list = [("a", "b"); ("c", "d"); ("e", "e"); ("o", "e"); ("w", "z")]

(**
(
**Nota**: negli esempi, quando viene data l'implementazione delle funzioni e dei datatype, 
come nei blocchi di codice piu' sopra, ai nomi delle funzioni sono aggiunti degli apici per 
distinguerle dalle implentazioni del programma. Quando si danno, invece,  gli esempi del 
funzionamento delle funzioni, come nel blocco precedente, sono usate dirattamente le 
funzioni del programma (senza apici). )
*)

(**
Si noti la struttura dell'albero creato e l'ordine degli elementi estratti:
*)

//     (c,d)[2]      
//    /        \     
// (a,b)[1]     (o,e)[2] 
//             /       \   
//         (e,e)[1]   (w,z)[1]
// 
// [("a", "b"); ("c", "d"); ("e", "e"); ("o", "e"); ("w", "z")]
Node
    (2,("c", "d"),
        Node (1,("a", "b"),Leaf,Leaf),
        Node 
           (2,("o", "e"),
               Node (1,("e", "e"),Leaf,Leaf),
               Node (1,("w", "z"),Leaf,Leaf)
           )
    )

(** 
<a id="operazioni">Operazioni base sui sotto alberi</a>
---------------------------

Questa sezione del modulo implementa le funzioni base di gestione dell'albero tra cui 
l'inserimento, la cancellazione, le operazioni di `skew` e `split` per rigenerare gli 
indici e la struttura dell'albero in modo da garantire l'invariante AA in seguito agli 
inserimenti e cancellazione effettuati, e l'operazione di ricerca all'interno 
dell'albero.

Sono innanzitutto definite alcune funzioni di supproto.

La funzione `level` restituisce il livello dell'albero:

*)
let level' tr =
    match tr with
    | Node' (l,_,_,_) -> l
    | Leaf'           -> 0

(**
Ad esempio il livello dell'abero che abbiamo appena costruito di sopra `tr5` e' 2:
*)
level tr5;;
// - val it : int = 2

(**
La funzione `rightmost_elem` restituisce l'informazione mantenuta nel nodo piu' 
a destra dell'albero ed e' usata per applicare le operazioni di trasformazione `skew` e 
`split` in seguito a una cancellazione `dltree_delete` descritta piu' sotto. Oltre all'albero 
e' passata in input un argomento nel caso in cui l'albero contenga solo una foglia:
*)
/// Restituisce come una coppia il nodo piu' a destra nell'albero. 
/// Se l'albero e' solo una Leaf, allora non ha nodi e in questo 
/// caso la funzione restituisce solo la coppia in input.
let rec rightmost_elem' xy0 tr =
    match tr with
    | Node (_,xy,_,tr2) -> rightmost_elem' xy tr2
    | Leaf              -> xy0

rightmost_elem ("","") tr5;;
// - val it : string * string = ("w", "z")

rightmost_elem ("","") dltree_empty;;
// - val it : string * string = ("", "")

(**
La funzione `right_app` applica una funzione al primo nodo piu' a destra di 
un albero ed e' usata per applicare le operazioni di trasformazione `skew` e 
`split` in seguito a una cancellazione `dltree_delete` descritta piu' sotto:
*)
let right_app' f tr =
    match tr with
    | Node (l,xy,tr1,tr2)   -> Node (l, xy, tr1, f tr2)
    | _                     -> tr

(**
La funzione `decrease_level` decresce il livello della radice di un albero a 
un dato livello piu' basso. Se il livello dato e' maggiore o uguale al livello 
originario l'albero rimane invariato:
*)
let decrease_level' l' tr =
    match tr with
    | Node (l,xy,tr1,tr2) when (l > l') -> Node (l',xy,tr1,tr2)
    | _  -> tr

(**
Anche questa funzione e' usata per applicare le operazioni di trasformazione 
`skew` e `split` in seguito a una cancellazione `dltree_delete` descritta piu' 
sotto e non ha senso usarla al di fuori di questo contesto:
*)
decrease_level 1 tr5;;
// val it : dltree<string,string> =
//   Node
//     (1,("c", "d"),Node (1,("a", "b"),Leaf,Leaf),
//      Node
//        (2,("o", "e"),Node (1,("e", "e"),Leaf,Leaf),
//         Node (1,("w", "z"),Leaf,Leaf)))

(**
Si noti infatti che la radice ha indice 1 e l'albero non soddifa piu' l'invariante AA.
*)

(**
Vediamo ora le operazioni di trasformazione.

L'operazione di `skew` esegue una singola rotazione a destra ed e' usata per 
ribilanciare l'albero quando il ramo sinistro ha lo stesso livello del padre:
*)                                      

let skew' tr =
    match tr with
    Node (l, xy, Node (l1,xy1,tr11,tr12), tr2)
        -> if (l1 = l)
            then Node (l1, xy1, tr11, Node (l,xy,tr12,tr2))
            else tr
    | _  -> tr

(**
Per vederne un esempio creiamo esplicitamente un albero che non soddisfa 
l'invariante AA in quanto il ramo sinistro ha lo stesso livello della 
radice e violando quindi il punto 2. della definizione di invariante AA 
data sopra:
*)

let tr6 = 
    Node
        (2,("D",0),
            Node 
                (2,("B",0),
                    Node (1,("A",0),Leaf,Leaf),
                    Node (1,("C",0),Leaf,Leaf)
                ),
            Node (1,("E",0),Leaf,Leaf)
        )

//          ("D",0)[2]                            ("B",0)[2]
//         /          \                             /       \
//       ("B",0)[2]  ("E",0)[..]     -->    ("A",0)[..]  ("D",0)[2]
//      /         \                                        /   \
//   ("A",0)[..]  ("C",0)[..]                     ("C",0)[..]  ("E",0)[..]
//      
skew tr6;;
// val it : dltree<string,int> =
//   Node
//     (2,("B", 0),
//         Node (1,("A", 0),Leaf,Leaf),
//         Node 
//             (2,("D", 0),
//                 Node (1,("C", 0),Leaf,Leaf),
//                 Node (1,("E", 0),Leaf,Leaf)
//             )
//         )

(**
L'operazione ha creato un nuovo albero che contiene l'informazione originaria 
ma che in piu' ora soddisfa l'invariante AA. Si noti pero' che questo vale per 
questo caso particolare. L'operazione di per se' non ristabilisce l'invariante 
ma deve essere usata nelle situazioni opportune ed eventualmente in combinazione 
con l'operazione di `split`.

L'operazione di `split` esegue una singola rotazione a sinistra per ribilanciare 
quando il nodo piu' a destra ha lo stesso livello del suo nonno (violando quindi 
il punto 4. della definizione di invariante AA data sopra), e incrementa di uno 
il livello del nodo radice risultante.
*)