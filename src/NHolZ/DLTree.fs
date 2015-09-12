(* ========================================================================== *)
(* DYNAMIC LOOKUP TREES (HOL Zero)                                            *)
(* - Library support for data storage in dynamic indexed binary trees         *)
(*                                                                            *)
(* by Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2012                            *)
(* ========================================================================== *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* http://github.com/domasin/HolZeroFs                                        *)
(* ========================================================================== *)

///Questo modulo costituisce una libreria di operazioni su alberi dinamici 
///di ricerca - alberi binari auto-bilanciati che memorizzano informazioni 
///su nodi ordinati in base a un indice rispetto alla relazione (<)
[<AutoOpen>]
module NHolZ.DLTree

(* Questo è implementato come alberi AA (anche chiamati alberi di Andersson), *)
(* che rimangono bilanciati con un fattore di 2 - ovvero la massima distanza  *)
(* dalla radice a una foglia non è più grande del doppio della distanza       *)
(* minima. Questo ha un'implementazione piuttosto semplice eppure è una       *)
(* delle più efficienti forme di albero binario auto-bilanciato, con ricerca, *)
(* inserimento e cancellazione che nel peggiore dei casi hanno complessità    *)
(* di tempo/spazio pari a O(log n)                                            *)

(* AA trees *)

(* Gli alberi AA sono una variante dei classici alberi binari di ricerca che  *)
(* mantengono una proprietà invariante aggiuntiva, chiamata "invariante AA",  *)
(* per assicurare che l'albero rimanga bilanciato all'interno di un fattore   *)
(* 2. Questa invariante usa il concetto di "livello" - un valore intero di    *)
(* misura della profonidità di un dato albero o sottoalbero.                  *)

(* L'invariante AA ha quattro aspetti:                                        *)
(* 1. Il livello di ogni foglia è 0                                           *)
(* 2. Il livello di ogni nodo sul ramo sinistro è uguale a quello del suo     *)
(*    padre meno uno                                                          *)
(* 3. Il livello di ogni nodo sul ramo destro è uguale a quello del suo       *)
(*    padre o a quello del suo padre meno uno                                 *)
(* 4. Il livello di ogni nodo sul ramo destro-destro è minore di quello dei   *)
(*    suoi nonni.                                                             *)

(* Così il livello rappresenta la distanza dal nodo alla foglia più a         *)
(* più a sinistra discendente del nodo, e un limite superiore di metà della   *)
(* distanza dal nodo alla sua foglia discendente più a destra. Così il        *)
(* livelloè un limite superiore di metà della profonodità dell'albero, ed è   *)
(* anche un limite superiore per la differenza tra le profondità delle foglie *)
(* più profonde e di quelle meno profonde.                                    *)

(* Le operazioni di inserimento e la cancellazione preservano l'invariante AA *)
(* applicando una combinazione di due operazioni di ribilanciamento - "skew"  *)
(* e "split" - una volta che un elemento è stato inserito/cancellato. Skew e  *)
(* split hanno entrambe una complessità tempo/spazio O(1), e il numero di     *)
(* nodi su cui hanno bisogno di operare per inserimento/cancellazione è al    *)
(* massimo O(log n), assicurando così che l'inserimento e la cancellazione    *)
(* siano O(log n). La particolare combinazione di skew e split impiegata      *)
(* dipende dal fatto che sia stata eseguita una cancellazione oppure un       *)
(* inserimento.                                                               *)

(* Si noti che per assicurare una corretta funzionalità (ovvero che le voci   *)
(* possano essere cercate in base agli inserimenti e alle cancellazioni che   *)
(* sono avvenute), è sufficiente che le operazioni di inserimento e cancella- *)
(* zione preservino un corretto ordinamento rispetto a '(<)' nell'albero di   *)
(* ricerca binario classico. Ovvero, l'invariante AA è puramente per          *)
(* efficienza, piuttosto che per correttezza. Si noti inoltre che le tre      *)
(* operazioni di ribilanciamento preservano tutte un corretto ordinamento.    *)

(* dltree datatype *)

///The 'dltree' datatype is a binary lookup tree datatype, where an index and 
///item are held at each node, and leaves hold no information.  Comparison    
///between indexes is done using the polymorphic '(<)' total order relation.  
///Each node also holds an integer for its AA level, to enable the AA         
///invariant to be maintained.  Note that there is no need for leaves to hold 
///their level because it is always 0.
type dltree<'a,'b> =
    | Node of int * ('a * 'b) * dltree<'a,'b> * dltree<'a,'b>
    | Leaf

// dltree_empty : dltree<'a,'b>
//                              
///Returns a fresh empty dltree.
let dltree_empty = Leaf

let rec dltree_elems0 tr xys0 =
    match tr with
    Node (_,xy,tr1,tr2) -> dltree_elems0 tr1 (xy::(dltree_elems0 tr2 xys0))
    | Leaf                -> xys0

// dltree_elems : dltree<'a,'b> -> ('a * 'b) list                         
//                                                                         
///This converts the information held in a given lookup tree into an index-ordered
///association list.                                               
let dltree_elems tr = dltree_elems0 tr []

(* Basic subtree operations *)

// level : dltree<'a,'b> -> int
//
///Returns the level of the tree.
let level tr =
    match tr with
    Node (l,_,_,_) -> l
    | Leaf           -> 0

// rightmost_elem: 'a * 'b -> dltree<'a,'b> -> 'a * 'b
//
///Returns the rightmost node in the tree as a pair. If the tree is just a Leaf, 
///than it has no nodes and in this case the function returns just the pair in input.
let rec rightmost_elem xy0 tr =
    match tr with
    Node (_,xy,_,tr2) -> rightmost_elem xy tr2
    | Leaf              -> xy0

// right_app: (dltree<'a,'b> -> dltree<'a,'b>) -> dltree<'a,'b> -> dltree<'a,'b>
//
///Applies a function to the rightmost node of a tree.
let right_app f tr =
    match tr with
    Node (l,xy,tr1,tr2)
        -> Node (l, xy, tr1, f tr2)
    | _  -> tr

// decrease_level: int -> dltree<'a,'b> -> dltree<'a,'b>
//
///Decreases the level of the root of a tree to a given lower level. If the given level is 
///equal or greater than the original level the tree remains unchanged.
let decrease_level l' tr =
    match tr with
    Node (l,xy,tr1,tr2) when (l > l')
        -> Node (l',xy,tr1,tr2)
    | _  -> tr

(* skew *)

// skew : dltree<'a,'b> -> dltree<'a,'b>
//
///The skew operation performs a single right rotation to rebalance when the
///left child has the same level as its parent.                             
//                                                                         
//          D[n]                     B[n]                                  
//         /    \                   /    \                                 
//       B[n]  E[..]     -->     A[..]  D[n]                               
//      /   \                           /   \                              
//   A[..]  C[..]                    C[..]  E[..]
let skew tr =
    match tr with
    Node (l, xy, Node (l1,xy1,tr11,tr12), tr2)
        -> if (l1 = l)
            then Node (l1, xy1, tr11, Node (l,xy,tr12,tr2))
            else tr
    | _  -> tr


(* split *)

// split : dltree<'a,'b> -> dltree<'a,'b>
//
///The split operation performs a single left rotation to rebalance when the 
///right-right grandchild has the same level as its grandparent, incrementing
///the level of the resulting top-level node.
//                                            
//        B[n]                      D[n+1]    
//       /    \                     /    \    
//    A[..]  D[n]      -->        B[n]  E[n]  
//           /  \                /   \        
//       C[..]  E[n]          A[..]  C[..]    
//
let split tr =
    match tr with
    Node (l, xy, tr1, Node (l2,xy2,tr21,tr22))
        -> if (level tr22 = l)
            then Node (l2 + 1, xy2, Node (l,xy,tr1,tr21), tr22)
            else tr
    | _  -> tr

// dltree_insert : ('a * 'b) -> dltree<'a,'b> -> dltree<'a,'b> when 'a : comparison             
//                                                                           
///This inserts the supplied single indexed item into a given lookup tree.   
///Fails if the tree already contains an entry for the supplied index.       
//                                                                           
// The tree potentially needs to be rebalanced at each node descending to the
// insertion point, and this can be done by a skew followed by split.        
let rec dltree_insert ((x0,_) as xy0) tr =
    match tr with
    Node (l,((x,_) as xy),tr1,tr2)
        -> let tr' = (* 1. Insert into tree, perserving correct order  *)
                    if (x0 < x)
                        then (* Put into left branch     *)
                            Node (l, xy, dltree_insert xy0 tr1, tr2)
                    else if (x < x0)
                        then (* Put into right branch    *)
                            Node (l, xy, tr1, dltree_insert xy0 tr2)
                        else (* Element already in tree  *)
                            hol_fail ("dltree_insert","Already in tree") in
            let tr'' = (* 2. Rebalance tree, to preserve AA invariant   *)
                        (split <* skew) tr' in
            tr''
    | Leaf
        -> (* Put element here *)
            Node (1, xy0, Leaf, Leaf)

// dltree_delete : 'a -> dltree<'a,'b> -> dltree<'a,'b> when 'a : comparison                    
//                                                                           
///This deletes the entry at the supplied index in a given lookup tree.      
///Fails if the tree does not contain an entry for the supplied index.       
// 
// The tree potentially needs to be rebalanced at each node descending to the
// deletion point, and this can be done by adjusting the level of the node,  
// followed by a series of skews and then splits.                            
//
let rec dltree_delete x0 tr =
    match tr with
    Node (l,((x,_) as xy),tr1,tr2)
        -> let tr' = (* 1. Delete from tree, perserving correct order  *)
                    if (x0 < x)
                        then (* Element should be in left branch *)
                            Node (l, xy, dltree_delete x0 tr1, tr2)
                    else if (x < x0)
                        then (* Element should be in right branch *)
                            Node (l, xy, tr1, dltree_delete x0 tr2)
                        else (* Node holds element to be deleted *)
                            (match (tr1,tr2) with
                                | (Leaf,_) -> tr2
                                | (_,Leaf) -> tr1
                                | _ -> let (x1,_) as xy1 = rightmost_elem xy tr1 in
                                        Node (l, xy1, dltree_delete x1 tr1, tr2)) in
            if (level tr1 < l-1) || (level tr2 < l-1)
            then (* 2. Rebalance tree, to preserve AA invariant   *)
                    (right_app split <* split <*
                     right_app (right_app skew) <* right_app skew <* skew <*
                     right_app (decrease_level (l-1)) <* decrease_level (l-1)) tr'
            else tr'
    | Leaf
        -> (* Element not in tree *)
            hol_fail ("dltree_delete","Not in tree")

// dltree_elem : 'a -> dltree<'a,'b> -> 'a * 'b when 'a : comparison                        
//                                                                       
///This returns the index and item held at the supplied index in a given 
///lookup tree.  Fails if the tree has no entry for the supplied index.
let rec dltree_elem x0 tr =
    match tr with
    Node (_, ((x,_) as xy), tr1, tr2)
            -> if (x0 < x) then dltree_elem x0 tr1
                else if (x < x0) then dltree_elem x0 tr2
                else xy
    | Leaf -> hol_fail ("dltree_elem","Not in tree")

// dltree_lookup : 'a -> dltree<'a,'b> -> 'b                            
//                                                                         
///This returns the item held at the supplied index in a given lookup tree.
let rec dltree_lookup x0 tr =
    let (_,y) = try2 (dltree_elem x0) tr "dltree_lookup" in
    y

// dltree_mem : 'a -> dltree<'a,'b> -> bool when 'a : comparison                                
//                                                                           
///This returns "true" iff the supplied index occurs in a given lookup tree.
let rec dltree_mem x0 tr =
    match tr with
    Node (_,(x,_),tr1,tr2)
            -> if (x0 < x) then dltree_mem x0 tr1
                else if (x < x0) then dltree_mem x0 tr2
                else true
    | Leaf -> false