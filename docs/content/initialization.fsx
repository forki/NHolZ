#I "../../bin/NHolZ"
#r "NHolZ.dll"
open NHolZ

fsi.AddPrinter print_type;;
fsi.AddPrinter print_qtype;;
fsi.AddPrinter print_term;;
fsi.AddPrinter print_qterm;;
fsi.AddPrinter print_thm;;

// This forces evaluation of modules

bool_ty;;               //CoreThry
let_def;;               //Equal
false_def;;             //Bool
not_true_thm;;          //BoolAlg
excluded_middle_thm;;   //BoolClass
mk_pair_rep_def;;       //Pair
ind_ty;;                //Ind
is_nat_rep_def;;        //Nat
numeral_def;;           //NatNumrl
add_def;;               //NatArith
lt_def;;                //NatRel

// printing functions per le tattiche: 
// vanno caricate solo dopo l'inizializzazione.
fsi.AddPrinter string_of_justification;;
fsi.AddPrinter string_of_refinement;;
fsi.AddPrinter string_of_tactic;;
fsi.AddPrinter string_of_thm_tactic;;
fsi.AddPrinter string_of_thm_tactical;;
fsi.AddPrinter string_of_goal;;
fsi.AddPrinter string_of_goalstack;;
fsi.AddPrinter string_of_goalstate;;