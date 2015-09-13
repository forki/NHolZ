(*** hide ***)
// This block of code is omitted in the generated HTML documentation. Use 
// it to define helpers that you do not want to show in the documentation.
#I "../../bin/NHolZ"

(**
Implementazione sperimentale di tattiche
========================

Hol Zero implementa solo regole di derivazione cosiddette *in avanti*. Gli ultimi 5 file 
in NHolZ sono derivati da hol_light di John Harrison per provare ad aggiungere delle 
funzionalità di dimostrazione interattiva *all'indietro* al codice originario.

Il seguente codice carica le funzioni di stampa e mostra in qualche modo come funzionano 
le tattiche al loro interno: si creano a partire da un goal *all'indietro* dei sottogoal 
e una funzione di giustificazione che tiene traccia di quale regola deve essere applicata 
*in avanti* ai sottogoal una volta che questi ultimi sono stati dimostrati.

*)
#r "NHolZ.dll"
#load "initialization.fsx"
open NHolZ

// se si deve dimostrare una congiunzione andranno dimostrati 
// entrambi i congiunti.
let goal1:goal = ([], (parse_term @"true /\ true"));;
let goal1_1 = CONJ_TAC goal1;;
let (_,goal_list1,just_fn1) = goal1_1;;
let th1 = (just_fn1:justification) null_inst [truth_thm;truth_thm]

// questo esempio e' un po' banale. Teoricamente da un'implicazione 
// all'indietro si assume l'antecedente e si dimostra il sotto goal 
// sotto l'assunzione dell'antecedente. Qui il sottogoal e' dimostrabile 
// indipendentemente dall'antecedente.
let goal2:goal = ([], (parse_term @"false ==> true"));;
let goal2_1 = DISCH_TAC goal2;;
let (_,goal_list2,just_fn2) = goal2_1;;
let th2 = (just_fn2:justification) null_inst [truth_thm]

// se si deve dimostrare una disgiunzione basta dimostrare 
// uno dei disgiunti.
let goal3:goal = ([], (parse_term @"true \/ p:bool"));;
let goal3_1 = DISJ1_TAC goal3;;
let (_,goal_list3,just_fn3) = goal3_1;;
let th3 = (just_fn3:justification) null_inst [truth_thm]

(**
Dimostrazione interattiva all'indietro
----------------------------------------

Il funzionamento interno delle tattiche qui viene nascosto con delle 
funzionalita' interattive piu' maneggevoli.

La funzione `g` dichiara il goal che si vuoe dimostrare. 
La funzione `e1` applica una tattica al goal attuale.
*)
g (parse_term @"true /\ true");;                                        // 1 true /\ true
e1 CONJ_TAC;;                                                           // 2 subgoal: true, true
e1 (ACCEPT_TAC(truth_thm))                                              // 1 subgoal: true. Il primpo subgoal e' stato dimostrato con il teorema truth_tm
e1 (ACCEPT_TAC(truth_thm))                                              // No subgoals. Anche il secondo subgoal e' stato dimostrato con il teorema truth_tm

(**
Esempi analoghi
*)

g (parse_term @"!x. x = x");;                                           // 1 subgoal: !x. x = x
e1 GEN_TAC;;                                                            // 1 subgoal: x = x
e1 REFL_TAC;;                                                           // No subgoals: il goal iniziale e' stato dimostrato

g (parse_term @"!(x:'1) y. (x = y) ==> (y = x)");;                      // 1 subgoal: !x y. x = y <=> y = x)
e1 (GEN_TAC);;                                                          // 1 subgoal: !(y:'1). x = y ==> y = x
e1 (GEN_TAC);;                                                          // 1 subgoal: (x:'1) = y ==> y = x
e1 (DISCH_THEN(ACCEPT_TAC << SYM))                                      // No subgoals: x = y ==> y = x e' stato dimostrato con il teorema della simmetria


(**
Questo fallisce: l'implementazione delle tattiche e' per ora solo un esperimento da mettere a posto
*)
//g (parse_term @"!(x:nat). (x = x) <=> true");;                          // 1 subgoal: !x. x = x <=> T)
//e1 GEN_TAC;;                                                            // 1 subgola: x = x <=> T)
//e1 (MATCH_ACCEPT_TAC(eqt_intro_rule(spec_all_rule eq_refl_lemma)));;    