[<AutoOpen>]
module NHolZ.lib2

open FSharp.Compatibility.OCaml

// derived from hol_light lib.fs and fusion.fs

/// Looks up item in association list taking default in case of failure.
// From Lib
let rec rev_assocd a l d = 
    match l with
    | [] -> d
    | (x, y) :: t -> 
        if compare y a = 0 then x
        else rev_assocd a t d

/// Substitute terms for variables inside a term.
// from fusion
let vsubst =
  let rec vsubst ilist (tm:term) =
    match tm with
      Tmvar(_,_) -> rev_assocd tm ilist tm
    | Tmconst(_,_) -> tm
    | Tmcomb(s,t) -> let s' = vsubst ilist s 
                     let t' = vsubst ilist t in
                     if s' = s && t' = t then tm else Tmcomb(s',t')
    | Tmabs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                       if ilist' = [] then tm else
                       let s' = vsubst ilist' s in
                       if s' = s then tm else
                       if exists (fun (t,x) -> var_free_in v t && var_free_in x s) ilist'
                       then let v' = variant [s'] v in
                            Tmabs(v',vsubst ((v',v)::ilist') s)
                       else Tmabs(v,s') in
  fun theta ->
    if theta = [] then (fun tm -> tm) else
    if forall (fun (t,x) -> type_of t = snd(dest_var x)) theta
    then vsubst theta else failwith "vsubst: Bad substitution list"

/// Changes the name of a bound variable.
let alpha v tm =
    let v0,bod = try dest_abs tm
                 with Failure _ -> failwith "alpha: Not an abstraction"in
    if v = v0 then tm else
    if type_of v = type_of v0 && not (var_free_in v bod) then
      mk_abs(v,vsubst[v,v0]bod)
    else failwith "alpha: Invalid new variable"

/// Applies a binary function between adjacent elements of the reverse of a list.
// From Lib
let rec rev_itlist f l b = 
    match l with
    | [] -> b
    | (h :: t) -> rev_itlist f t (f h b)

/// Searches a list of pairs for a pair whose second component equals a specified value.
// From Lib
let rec rev_assoc a l = 
    match l with
    | (x, y) :: t -> 
        if compare y a = 0 then x
        else rev_assoc a t
    | [] -> failwith "find"

// from lib
let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t

/// Returns position of given element in list.
// OPTIMIZE : Make this an alias for List.findIndex.
// Or, for more safety, modify this to return an option value, fix the call sites,
// then make this an alias for List.tryFindIndex.
let index x = 
    let rec ind n l = 
        match l with
        | [] -> failwith "index"
        | (h :: t) -> 
            if compare x h = 0 then n
            else ind (n + 1) t
    ind 0

(* ------------------------------------------------------------------------- *)
(* Issue a report with a newline.                                            *)
(* ------------------------------------------------------------------------- *)

/// Prints a string and a following line break.
let report s =
    Format.print_string s
    Format.print_newline()

(* ------------------------------------------------------------------------- *)
(* Convenient function for issuing a warning.                                *)
(* ------------------------------------------------------------------------- *)

/// Prints out a warning string.
let warn cond s =
    if cond then
        report("Warning: " + s)

let rec mapfilter f l =
  match l with
    [] -> []
  | (h::t) -> let rest = mapfilter f t in
              try (f h)::rest with Failure _ -> rest

(* ------------------------------------------------------------------------- *)
(* Time a function.                                                          *)
(* ------------------------------------------------------------------------- *)

/// Flag to determine whether 'time' function outputs CPU time measure.
let report_timing = ref true

/// Report CPU time taken by a function.
let time f x = 
    if not(!report_timing) then f x
    else 
        let start_time = Sys.time()
        try 
            let result = f x
            let finish_time = Sys.time()
            report("CPU time (user): " + (string_of_float(finish_time -. start_time)))
            result
        with _ -> 
            let finish_time = Sys.time()
            Format.print_string
                ("Failed after (user) CPU time of " + (string_of_float(finish_time -. start_time)) + ": ")
            reraise ()

let rec butlast l = 
    match l with
    | [_] -> []
    | (h :: t) -> h :: (butlast t)
    | [] -> failwith "butlast"