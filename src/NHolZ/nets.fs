(* ========================================================================= *)
(* Term nets: reasonably fast lookup based on term matchability.             *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

(* ========================================================================== *)
(* F# Porting                                                                 *)
(*                                                                            *)
(* by Domenico Masini 2013                                                    *)
(* derived from NHol by Jack Pappas, Anh-Dung Phan, Eric Taucher              *)
(* ========================================================================== *)

[<AutoOpen>]
module NHolZ.nets

(* TODO :   If possible, modify the Lcnet and Cnet cases of 'term_label' by removing
            the parentheses around their element type -- the parentheses cause the values
            to be combined into a tuple, which adds an extra level of indirection when
            we want to retrieve their values (not a desirable behavior for a lookup mechanism). *)

/// Term nets are a finitely branching tree structure; at each level we
/// have a set of branches and a set of "values". Linearization is
/// performed from the left of a combination; even in iterated
/// combinations we look at the head first. This is probably fastest, and
/// anyway it's useful to allow our restricted second order matches: if
/// the head is a variable then then whole term is treated as a variable.
type term_label =
    /// variable (instantiable)
    | Vnet
    /// local constant
    | Lcnet of (string * int)
    /// constant
    | Cnet of (string * int)
    /// lambda term (abstraction)
    | Lnet of int
    override this.ToString() = 
        match this with
        | Vnet -> "Vnet"
        | Lcnet(s, i) ->
            sprintf "Lcnet (\"%s\", %i)" s i
        | Cnet(s, i) ->
            sprintf "Cnet (\"%s\", %i)" s i
        | Lnet i ->
            sprintf "Lnet (%i)" i

type net<'a> = 
    | Netnode of (term_label * 'a net) list * 'a list
    override this.ToString() = 
        match this with
        | Netnode(tlList, aList) ->
            // TODO : Should these use %A instead of %O?
            sprintf "Netnode (%O, %O)" tlList aList

(* ------------------------------------------------------------------------- *)
(* The empty net.                                                            *)
(* ------------------------------------------------------------------------- *)

/// The empty net.
let empty_net = Netnode([], [])

(* ------------------------------------------------------------------------- *)
(* Insert a new element into a net.                                          *)
(* ------------------------------------------------------------------------- *)

// from lib
let rec remove1 p l =
  match l with
    [] -> failwith "remove"
  | (h::t) -> if p(h) then h,t else
              let y,n = remove1 p t in y,h::n

let enter : _ -> _ -> _ -> net<'T> =
  let label_to_store lconsts tm =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then
      let bv,bod = dest_abs op in
      let bod' = if mem bv lconsts then vsubst [genvar(type_of bv),bv] bod
                 else bod in
      Lnet(length args),bod'::args
    else if mem op lconsts then Lcnet(fst(dest_var op),length args),args
    else Vnet,[] in
  let canon_eq x y =
    // NOTE: unsafe comparison could fail
        // Revise this to ensure original intentions
        try Unchecked.compare x y = 0 
        with _ -> false
  let canon_lt x y =
    try Unchecked.compare x y < 0
        with _ -> false
  let rec sinsert x l  =
    match l with
    | [] -> [x]
    | hd::tl -> 
        if canon_eq hd x then 
            failwith "sinsert" 
        elif canon_lt x hd then 
            x::l 
        else
            let tl = sinsert x tl
            hd :: tl
  let set_insert x l = try sinsert x l with Failure "sinsert" -> l in
  let rec net_update lconsts (elem,tms,Netnode(edges,tips)) =
    match tms with
      [] -> Netnode(edges,set_insert elem tips)
    | (tm::rtms) ->
          let label,ntms = label_to_store lconsts tm in
          let child,others =
            try (snd ||>> id) (remove1 (fun (x,y) -> x = label) edges)
            with Failure _ -> (empty_net,edges) in
          let new_child = net_update lconsts (elem,ntms@rtms,child) in
          Netnode ((label,new_child)::others,tips) in
  fun lconsts (tm,elem) net -> net_update lconsts (elem,[tm],net)

(* ------------------------------------------------------------------------- *)
(* Look up a term in a net and return possible matches.                      *)
(* ------------------------------------------------------------------------- *)

let lookup =
  let label_for_lookup tm =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then Lnet(length args),(body op)::args
    else Lcnet(fst(dest_var op),length args),args in
  let rec follow (tms,Netnode(edges,tips)) =
    match tms with
      [] -> tips
    | (tm::rtms) ->
          let label,ntms = label_for_lookup tm in
          let collection =
            try let child = assoc label edges in
                follow(ntms @ rtms, child)
            with Failure _ -> [] in
          if label = Vnet then collection else
          try collection @ follow(rtms,assoc Vnet edges)
          with Failure _ -> collection in
  fun tm net -> follow([tm],net)
