(*** hide ***)
// This block of code is omitted in the generated HTML documentation. Use 
// it to define helpers that you do not want to show in the documentation.
#I "../../bin/NHolZ"

(**
Introduzione a HOL
========================

I sistemi *HOL* sono sviluppati per supportare la dimostrazione interattiva di teoremi 
in una logica di ordine superiore (da qui l'acronimo *HOL* che sta per Higher Order 
Logic). Per questo scopo, la logica formale e' interfacciata a un linguaggio di programmazione 
di scopo generale. Tradizionalmente il linguaggio utilizzato a questo scopo e' uno dei  
lingaggi della famiglia ML (che sta appunto per meta-linguaggio) come SML, OCaml, ecc. 
In particolare HOL Zero da cui deriva NHolZ e' sviluppato in OCaml che puo' essere tranquillamente 
chiamato il papa' di F# (mentre l'SML ne e' il nonno volendo mantenere questa metafora 
famigliare). Attraverso il linguaggio di programmazione in cui il sistem e' sviluppato e' 
possibile denotare i termini e i teoremi della logica formale, e svilupparne le teorie.

La logica formale di HOL Zero e' una logica predicativa tipizzata, classica, di ordine superiore, 
cioe' una logica predicativa con un sistema di tipi, con la legge del terzo escluso come teorema, 
e con la possibilita' di quantificare su funzioni. E' basata sul lambda calcolo tipizzato di 
Alonzo Church (teoria semplice dei tipi) che e' stato originariamente sviluppato come un fondamento 
per la matematica (A. Church. A formulation of the simple theory of types. *Journal of Symbolic 
Logic*, 5:56-68, 1940). La principale area di applicazione di HOL fu intesa inizalmente per la 
specifica e la verifica di sistemi hardware, tuttavia nel corso del tempo HOL e' stato applicato 
in molte altre aree.

La storia dei sistemi HOL
---------------------------

L'approccio alla meccanizzazione delle dimostrazioni formali usato dai sistemi HOL e' dovuto a 
Robin Milner (R. Milner M. Gordon and C. P. Wadsworth. *Edinburgh LCF: A Mechanised Logic
of Computation, volume 78 of Lecture Notes in Computer Science*. Springer-Verlag,
1979.) che e' anche stato il capo del team che ha sviluppato e implementato il linguaggio ML. 
Quel lavoro fu centrato su un sistema chiamato LCF (logic for computable functions: logica per 
funzioni computabili), che fu inteso per il ragionamento interattivo automatico su funzioni di 
ordine superiore definite ricorsivamente. L'interfacciamento alla logica del meta-linguaggio fu 
resa esplicita, usando la struttura di tipi dell'ML, con l'intenzione di provare successivamente 
altre logiche al posto di quella originaria. I sistemi HOL sono discendenti di LCF e cosi' soddisfano 
questa intenzione originaria di applicare la metodologia LCF ad altre logiche.

L'LCF originario fu sviluppato ad Edinburgo nei primi anni 1970, e oggi ci si riferisce ad esso 
come all'*Edinburgh LFC*. Fu sviluppato inizialmente in Lisp. Il suo codice fu portato dallo Stanford 
Lisp al Franz Lisp da Gerard Huet presso l'INRIA, e fu usato in un progetto di ricerca Francese 
chiamato *Formel*. La versione Franz Lisp dell'LCF di Huet fu ulteriormente sviluppata a Cambridge 
da Larry Paulson, e divenne conosciuta come il *Cambridge LCF*. Il primo sistema *HOL* propriamente 
detto fu implementato sulla base di una prima versione del Cambridge LCF e conseguentemente eredito' 
molte delle caratteristiche di entrambi l'Edinburgh e il Cambridge LCF. Per esempio, l'assiomatizzazione 
della logica di ordine superiore non e' quella classica dovuta a Church, ma una formulazione 
equivalente influenzata da LCF.

Una versione ampliata e razionalizzata di HOL, chiamata HOL88, fu rilasciata (nel 1988), dopo che il 
sistema HOL originario era stato in uso per molti anni. HOL90 (rilasciato nel 1990) e' stato un porting 
di HOL88 in SML (R. Milner, M. Tofte, and R. Harper. *The Definition of Standard ML*. MIT Press,
1990.) da parte di Konrad Slind.

*)