module NHolZ.Tests.Exn

open NHolZ
open NUnit.Framework
open FsUnit

(* check tests *)

[<Test>]
[<ExpectedException(typeof<HolFail>, ExpectedMessage = "[HZ] FAIL: check - Test fails")>]
let ``check_fail``() =

    check ((=) 1) 2
    |> ignore

[<Test>]
let ``check_success``() =

    check ((=) 1) 1
    |> should equal 1

(* assert0 tests *)

[<Test>]
let ``assert0_fail``() =

    (fun () -> (assert0 (1 <> 1) (HolFail("prova","pippo"))) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``assert0_success``() =

    assert0 (1 = 1) (HolFail("prova","pippo"))
    |> should equal ()

(* try0 tests *)

[<Test>]
let ``try0_fail``() =
    
    let func xs = 
        match xs with
        | [] -> hol_fail ("func","Empty list")
        | _ -> 1 + 2

    (fun () -> (try0 func [] (HolFail("prova","pippo"))) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``try0_success``() =

    let func xs = 
        match xs with
        | [] -> hol_fail ("func","Empty list")
        | _ -> 1 + 2

    try0 func [1] (HolFail("prova","pippo"))
    |> should equal 3

(* try1 tests *)

[<Test>]
let ``try1_fail``() =
    
    let func xs = 
        match xs with
        | [] -> hol_fail ("func","Empty list")
        | _ -> 1 + 2

    (fun () -> (try1 func [] ("prova","pippo")) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``try1_success``() =

    let func xs = 
        match xs with
        | [] -> hol_fail ("func","Empty list")
        | _ -> 1 + 2

    try1 func [1] ("prova","pippo")
    |> should equal 3

(* try2 tests *)

[<Test>]
let ``try2_fail``() =
    
    let func xs = 
        match xs with
        | [] -> hol_fail ("func","Empty list")
        | _ -> 1 + 2

    (fun () -> (try2 func [] "prova") |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``try2_success``() =

    let func xs = 
        match xs with
        | [] -> hol_fail ("func","Empty list")
        | _ -> 1 + 2

    try2 func [1] "prova"
    |> should equal 3

(* try_find tests *)

[<Test>]
let ``try_find_fail``() =
    
    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | _ -> x + 2

    (fun () -> (try_find func [1;2]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``try_find_success``() =

    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | _ -> x + 2

    try_find func [1;2;3;4]
    |> should equal 5

(* try_filter tests *)

[<Test>]
let ``try_filter_fail``() =
    
    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | 4 -> hol_fail ("func","4")
        | _ -> x + 2

    try_filter func [1;2;4]
    |> should equal []

[<Test>]
let ``try_filter_success``() =

    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | 4 -> hol_fail ("func","4")
        | _ -> x + 2

    try_filter func [1;2;3;4;5]
    |> should equal [5;7]

[<Test>]
let ``try_filter_2_success``() =

    try_filter hd [[1;2;3];[4;5];[];[6;7;8];[]]
    |> should equal [1; 4; 6]

(* can tests *)

[<Test>]
let ``can_fail``() =
    
    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | 4 -> hol_fail ("func","4")
        | _ -> x + 2

    can func 1
    |> should equal false

[<Test>]
let ``can_success``() =

    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | 4 -> hol_fail ("func","4")
        | _ -> x + 2

    can func 3
    |> should equal true

(* cannot tests *)

[<Test>]
let ``cannot_fail``() =
    
    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | 4 -> hol_fail ("func","4")
        | _ -> x + 2

    cannot func 3
    |> should equal false

[<Test>]
let ``cannot_success``() =

    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | 4 -> hol_fail ("func","4")
        | _ -> x + 2

    cannot func 1
    |> should equal true

(* repeat tests *)

//[<Test>]
//let ``repeat_fail``() =
//
//    let func x = 
//        match x with
//        | 1 -> hol_fail ("func","1")
//        | 2 -> hol_fail ("func","2")
//        | 9 -> hol_fail ("func","4")
//        | _ -> x + 2
//
//    repeat func 10
//    |> should equal 9
// qui bisogna mettere un test per verificare lo StackOverFlow

[<Test>]
let ``repeat_success``() =

    let func x = 
        match x with
        | 1 -> hol_fail ("func","1")
        | 2 -> hol_fail ("func","2")
        | 9 -> hol_fail ("func","4")
        | _ -> x + 2

    repeat func 3
    |> should equal 9

(* pair tests *)

[<Test>]
let ``pair_test1``() =
    
    pair 1 3
    |> should equal (1,3)

(* switch tests *)

[<Test>]
let ``switch_test1``() =
    
    switch (1,3)
    |> should equal (3,1)

(* length tests *)

[<Test>]
let ``length_test1``() =
    
    length [1..10]
    |> should equal 10

//(* length_big_int tests *)
//
//[<Test>]
//let ``length_big_int_test``() =
//    
//    length_big_int [1..10]
//    |> should equal (new System.Numerics.BigInteger(10))

(* cons tests *)

[<Test>]
let ``cons_test``() =
    
    cons 1 [2;3]
    |> should equal [1;2;3]

(* is_empty tests *)

[<Test>]
let ``is_empty_fail``() =
    
    is_empty [1]
    |> should equal false

[<Test>]
let ``is_empty_success``() =
    
    is_empty []
    |> should equal true

(* is_nonempty tests *)

[<Test>]
let ``is_nonempty_fail``() =
    
    is_nonempty []
    |> should equal false

[<Test>]
let ``is_nonempty_success``() =
    
    is_nonempty [1]
    |> should equal true

(* hd tests *)

[<Test>]
let ``hd_fail``() =
    
    (fun () -> (hd []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``hd_success``() =

    hd [1;2;3;4]
    |> should equal 1

(* tl tests *)

[<Test>]
let ``tl_fail``() =
    
    (fun () -> (tl []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``tl_success``() =

    tl [1;2;3;4]
    |> should equal [2;3;4]

(* hd_tl tests *)

[<Test>]
let ``hd_tl_fail``() =
    
    (fun () -> (hd_tl []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``hd_tl_success``() =

    hd_tl [1;2;3;4]
    |> should equal (1,[2;3;4])

(* front tests *)

[<Test>]
let ``front_fail``() =
    
    (fun () -> (front []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``front_success``() =

    front [1;2;3;4]
    |> should equal [1;2;3]

(* last tests *)

[<Test>]
let ``last_fail``() =
    
    (fun () -> (last []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``last_success``() =

    last [1;2;3;4]
    |> should equal 4

(* front_last tests *)

[<Test>]
let ``front_last_fail``() =
    
    (fun () -> (front_last []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``front_last_success``() =

    front_last [1;2;3;4]
    |> should equal ([1;2;3],4)

(* list_eq tests *)

[<Test>]
let ``list_eq_false``() =
    
    list_eq (=) [1;2;3] [1;2;5]
    |> should equal false

[<Test>]
let ``list_eq_true``() =

    list_eq (=) [1;2;3] [1;2;3]
    |> should equal true

(* rev tests *)

[<Test>]
let ``rev_empty``() =
    
    rev []
    |> should equal []

[<Test>]
let ``rev_non_empty``() =

    rev [1;2;3]
    |> should equal [3;2;1]

(* append tests *)

[<Test>]
let ``append_empty``() =
    
    append [] []
    |> should equal []

[<Test>]
let ``append_non_empty``() =

    append [1;2] [3;4]
    |> should equal [1;2;3;4]

(* flatten tests *)

[<Test>]
let ``flatten_test1``() =
    
    flatten [[1;2];[3;4];[5;6]]
    |> should equal [1;2;3;4;5;6]

(* enumerate tests *)

[<Test>]
let ``enumerate_empty``() =
    
    enumerate []
    |> should equal []

[<Test>]
let ``enumerate_non_empty``() =

    enumerate ["a";"b";"c";"d"]
    |> should equal [(1,"a");(2,"b");(3,"c");(4,"d")]

(* zip tests *)

[<Test>]
let ``zip_fail``() =
    
    (fun () -> (zip [1;2;3] []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``zip_success``() =

    zip [1;2;3;4] ["a";"b";"c";"d"]
    |> should equal [(1,"a");(2,"b");(3,"c");(4,"d")]

(* unzip tests *)

[<Test>]
let ``unzip_empty``() =

    unzip []
    |> should equal ([],[])

[<Test>]
let ``unzip``() =

    unzip [(1,"a");(2,"b");(3,"c");(4,"d")]
    |> should equal ([1;2;3;4],["a";"b";"c";"d"])

(* el tests *)

[<Test>]
let ``el_fail_greater_index``() =

    (fun () -> (el 4 [1;2;3]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``el_fail_negative_index``() =

    (fun () -> (el -1 [1;2;3]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``el_success``() =

    el 3 ["a";"b";"c";"d"]
    |> should equal "c"

(* el0 tests *)

[<Test>]
let ``el0_fail_greater_index``() =

    (fun () -> (el0 4 [1;2;3]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``el0_fail_negative_index``() =

    (fun () -> (el0 -1 [1;2;3]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``el0_success``() =

    el0 3 ["a";"b";"c";"d"]
    |> should equal "d"

(* cut tests *)

[<Test>]
let ``cut_fail_greater_index``() =

    (fun () -> (cut 4 [1;2;3]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``cut_fail_negative_index``() =

    (fun () -> (cut -1 [1;2;3]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``cut_success``() =

    cut 2 ["a";"b";"c";"d";"e"]
    |> should equal (["a";"b"],["c";"d";"e"])

(* cut_while tests *)

[<Test>]
let ``cut_while_success``() =

    cut_while (fun x -> x < 3) [1;2;3;4;5]
    |> should equal ([1;2],[3;4;5])

(* decrement tests *)

[<Test>]
let ``decrement_negative``() =

    decrement -1
    |> should equal 0

[<Test>]
let ``decrement_zero``() =

    decrement 0
    |> should equal 0

[<Test>]
let ``decrement_positive``() =

    decrement 8
    |> should equal 7

(* up_to tests *)

[<Test>]
let ``up_to_when_second_less_first``() =

    up_to 8 7
    |> should equal []

[<Test>]
let ``up_to``() =

    up_to 8 12
    |> should equal [8;9;10;11;12]

(* <* tests *)

[<Test>]
let ``<*_test``() =

    let func = (fun x -> x ** 2.)

    ((fun x -> x * 2.) <* (fun x -> x ** 2.)) 3.
    |> should equal 18

[<Test>]
let ``<* corrisponde a <<``() =

    let func = (fun x -> x ** 2.)

    ((fun x -> x * 2.) <* (fun x -> x ** 2.)) 3.
    |> should equal (((fun x -> x * 2.) << (fun x -> x ** 2.)) 3.)

(* curry tests *)

[<Test>]
let ``curry_test``() =

    curry snd 1 2
    |> should equal 2

(* uncurry tests *)

[<Test>]
let ``uncurry_test``() =

    uncurry max (1,2)
    |> should equal 2

(* funpow tests *)

[<Test>]
let ``funpow_test``() =

    funpow 3 ((*) 2) 2
    |> should equal 16

(* swap_arg tests *)

[<Test>]
let ``swap_arg_test``() =

    swap_arg ( ** ) 2. 3.
    |> should equal 9.

(* dbl_arg tests *)

[<Test>]
let ``dbl_arg_test``() =

    dbl_arg (fun x y -> x + y) 4
    |> should equal 8

(* id_fn tests *)

[<Test>]
let ``id_fn_test``() =

    id_fn 4
    |> should equal 4

(* arg1_fn tests *)

[<Test>]
let ``arg1_fn_test``() =

    arg1_fn 4 5
    |> should equal 4

(* pair_apply tests *)

[<Test>]
let ``pair_apply_test``() =

    pair_apply ((fun x -> x + 1),(fun x -> x + 2)) (1,2)
    |> should equal (2,4)

(* map tests *)

[<Test>]
let ``map_test``() =

    map (fun x -> x + 1) [1;2;3]
    |> should equal [2;3;4]

(* map2 tests *)

[<Test>]
let ``map2_fail``() =

    (fun () -> (map2 (+) [1;2;3;5] [1;2;3]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``map2_success``() =

    map2 (+) [1;2;3] [1;2;3]
    |> should equal [2;4;6]

(* foldl tests *)

[<Test>]
let ``foldl_empty``() =

    foldl (+) 1 []
    |> should equal 1

[<Test>]
let ``foldl_non_empty``() =

    foldl (+) 1 [1;2;3]
    |> should equal 7

[<Test>]
let ``foldl_is_different_from_foldr``() =

    foldl (-) 1 [1;2;3]
    |> should equal -5 //check the different result of foldr_is_different_from_foldl

(* foldl1 tests *)

[<Test>]
let ``foldl1_empty_fails``() =

    (fun () -> (foldl1 (+) []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``foldl1_non_empty_succeds``() =

    foldl1 (+) [1;2;3]
    |> should equal 6

[<Test>]
let ``foldl1_is_different_from_foldr1``() =

    foldl1 (-) [1;2;3]
    |> should equal -4 //check the different result of foldr1_is_different_from_foldl1

(* foldr tests *)

[<Test>]
let ``foldr_empty``() =

    foldr (+) [] 1
    |> should equal 1

[<Test>]
let ``foldr_non_empty``() =

    foldr (+) [1;2;3] 1
    |> should equal 7

[<Test>]
let ``foldr_is_different_from_foldl``() =

    foldr (-) [1;2;3] 1
    |> should equal 1 //check the different result of foldl_is_different_from_foldr

(* foldr1 tests *)

[<Test>]
let ``foldr1_empty_fails``() =

    (fun () -> (foldr1 (+) []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``foldr1_non_empty_succeds``() =

    foldr1 (+) [1;2;3]
    |> should equal 6

[<Test>]
let ``foldr1_is_different_from_foldl1``() =

    foldr1 (-) [1;2;3]
    |> should equal 2 //check the different result of foldl1_is_different_from_foldr1

(* foldl' tests *)

[<Test>]
let ``foldl' empty equals foldl empty``() =

    foldl' (uncurry (+)) (1,[])
    |> should equal (foldl (+) 1 [])

[<Test>]
let ``foldl' non empty equals foldl non empty``() =

    foldl' (uncurry (+)) (1,[1;2;3])
    |> should equal (foldl (+) 1 [1;2;3])

(* foldr' tests *)

[<Test>]
let ``foldr' empty equals foldl empty``() =

    foldr' (uncurry (+)) ([],1)
    |> should equal (foldr (+) [] 1)

[<Test>]
let ``foldr' non empty equals foldl non empty``() =

    foldr' (uncurry (+)) ([1;2;3],1)
    |> should equal (foldr (+) [1;2;3] 1)

(* foldl1' tests *)

[<Test>]
let ``foldl1'_empty_fails``() =

    (fun () -> (foldl1' (uncurry (+)) []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``foldl1'_non_empty_succeds``() =

    foldl1' (uncurry (+)) [1;2;3]
    |> should equal (foldl1 (+) [1;2;3])

[<Test>]
let ``foldl1'_is_different_from_foldr1``() =

    foldl1' (uncurry (-)) [1;2;3]
    |> should equal (foldl1 (-) [1;2;3]) //check the different result of foldr1_is_different_from_foldl1

(* foldr1' tests *)

[<Test>]
let ``foldr1'_empty_fails``() =

    (fun () -> (foldr1' (uncurry (+)) []) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``foldr1'_non_empty_succeds``() =

    foldr1' (uncurry (+)) [1;2;3]
    |> should equal (foldr1 (+) [1;2;3])

[<Test>]
let ``foldr1'_is_different_from_foldl1``() =

    foldr1' (uncurry (-)) [1;2;3]
    |> should equal (foldr1 (-) [1;2;3]) //check the different result of foldl1_is_different_from_foldr1

(* unfoldl tests *)

type prova = 
    | Prova1 of int
    | Prova of prova * prova
    with
    override this.ToString() =  
        match this with
        | Prova1 x -> sprintf "Prova1 (%A)" x 
        | Prova (x,y) -> sprintf "Prova (%A,%A)" x y

[<Test>]
let ``unfoldl_test``() = 

    let dest_fn x = 
        match x with
        | Prova (x1,x2) -> (x1,x2)
        | _             -> hol_fail ("dest_fn","?")

    let actual = unfoldl dest_fn (Prova(Prova(Prova1(5),Prova1(6)),Prova1(2)))
    let expected = (Prova1 5,[Prova1 6;Prova1 2])

    actual
    |> should equal expected

(* unfoldl1 tests *)

[<Test>]
let ``unfoldl1_test``() = 

    let dest_fn x = 
        match x with
        | Prova (x1,x2) -> (x1,x2)
        | _             -> hol_fail ("dest_fn","?")

    unfoldl1 dest_fn (Prova(Prova(Prova1(5),Prova1(6)),Prova1(2)))
    |> should equal [Prova1 5;Prova1 6;Prova1 2]

(* unfoldr tests *)

[<Test>]
let ``unfoldr_test``() = 

    let dest_fn x = 
        match x with
        | Prova (x1,x2) -> (x1,x2)
        | _             -> hol_fail ("dest_fn","?")

    let actual = unfoldr dest_fn (Prova(Prova(Prova1(5),Prova1(6)),Prova1(2)))
    let expected = ([Prova(Prova1(5),Prova1(6))],Prova1 2)

    actual
    |> should equal expected

(* unfoldl1 tests *)

[<Test>]
let ``unfoldr1_test``() = 

    let dest_fn x = 
        match x with
        | Prova (x1,x2) -> (x1,x2)
        | _             -> hol_fail ("dest_fn","?")

    unfoldr1 dest_fn (Prova(Prova(Prova1(5),Prova1(6)),Prova1(2)))
    |> should equal [Prova(Prova1(5),Prova1(6));Prova1 2]

(* unfold tests *)

[<Test>]
let ``unfold_test``() = 

    let dest_fn x = 
        match x with
        | Prova (x1,x2) -> (x1,x2)
        | _             -> hol_fail ("dest_fn","?")

    let actual = unfold dest_fn (Prova(Prova(Prova1(5),Prova1(6)),Prova1(2)))
    let expected = [Prova1(5);Prova1(6);Prova1(2)]

    actual
    |> should equal expected

(* find tests *)

[<Test>]
let ``find_test``() =
    
    find (fun x -> x > 3) [1;2;3;4;5]
    |> should equal 4

(* filter tests *)

[<Test>]
let ``filter_test``() =
    
    filter (fun x -> x % 2 = 0) [1;2;3;4;5;6;7;8;9;10]
    |> should equal [2;4;6;8;10]

(* partition tests *)

[<Test>]
let ``partition_test``() =
    
    partition (fun x -> x % 2 = 0) [1;2;3;4;5;6;7;8;9;10]
    |> should equal ([2;4;6;8;10],[1;3;5;7;9])

(* exists tests *)

[<Test>]
let ``exists_false``() =
    
    exists (fun x -> x % 2 = 0) [1;3;5;7;9]
    |> should equal false

[<Test>]
let ``exists_true``() =
    
    exists (fun x -> x % 2 = 0) [1;3;6;7;9]
    |> should equal true

(* forall tests *)

[<Test>]
let ``forall_false``() =
    
    forall (fun x -> x % 2 = 0) [1;3;6;7;9]
    |> should equal false

[<Test>]
let ``forall_true``() =
    
    forall (fun x -> x % 2 = 0) [2;4;6;8;10]
    |> should equal true

(* assoc tests *)

[<Test>]
let ``assoc_false``() =
    
    (fun () -> (assoc "tre" [("uno",1);("due",2);("quattro",4)]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``assoc_true``() =
    
    assoc "tre" [("uno",1);("due",2);("tre",5);("tre",3);("quattro",4)]
    |> should equal 5

(* inv_assoc tests *)

[<Test>]
let ``inv_assoc_false``() =
    
    (fun () -> (inv_assoc 3 [("uno",1);("due",2);("quattro",4)]) |> ignore)
    |> should throw typeof<HolFail>

[<Test>]
let ``inv_assoc_true``() =
    
    inv_assoc 3 [("uno",1);("due",2);("tre",5);("tre",3);("quattro",4)]
    |> should equal "tre"

(* fst_map tests *)

[<Test>]
let ``fst_map_test``() =
    
    fst_map ((+) "pippo_") [("uno",1);("due",2);("tre",5);("tre",3);("quattro",4)]
    |> should equal [("pippo_uno",1);("pippo_due",2);("pippo_tre",5);("pippo_tre",3);("pippo_quattro",4)]

(* snd_map tests *)

[<Test>]
let ``snd_map_test``() =
    
    snd_map ((+) 1) [("uno",1);("due",2);("tre",5);("tre",3);("quattro",4)]
    |> should equal [("uno",2);("due",3);("tre",6);("tre",4);("quattro",5)]

(* fst_filter tests *)

[<Test>]
let ``fst_filter_test``() =
    
    fst_filter ((=) "tre") [("uno",1);("due",2);("tre",5);("tre",3);("quattro",4)]
    |> should equal [("tre",5);("tre",3)]

(* snd_filter tests *)

[<Test>]
let ``snd_filter_test``() =
    
    snd_filter ((=) 3) [("uno",1);("due",2);("tre",5);("tre",3);("quattro",4)]
    |> should equal [("tre",3)]

(* do_map tests *)

//un wraper per farsi restituire il side-effect di stampa sullo standard output
let testPrintf f arg =
    let oldOut = System.Console.Out
    use out = new System.IO.StringWriter()
    System.Console.SetOut(out)
    f arg |>ignore
    System.Console.SetOut(oldOut)
    out.GetStringBuilder().ToString()

let stampa x = printfn "%s" x

[<Test>]
let ``stampa_test``() =

    testPrintf stampa "pippo"
    |> should equal "pippo\r\n"

[<Test>]
let ``do_map_test``() =
    
    let do_map_stampa = do_map stampa

    testPrintf do_map_stampa ["p";"c"]
    |> should equal "p\r\nc\r\n"

(* mem tests *)

[<Test>]
let ``mem_false``() =
    
    mem 3 [1;2;4;5]
    |> should equal false

[<Test>]
let ``mem_true``() =
    
    mem 3 [1;2;3;4;5]
    |> should equal true

(* mem' tests *)

let eqWithin tollerance (x:int) y = 
    let delta = (abs (System.Convert.ToDecimal(x) - y)) 
    let res = delta <= tollerance
    res

[<Test>]
let ``mem'_true``() =
    
    mem' (eqWithin 0.001M) 3 [1.01M;2.001M;3.001M;4.001M;5.001M]
    |> should equal true

[<Test>]
let ``mem'_false``() =
    
    mem' (eqWithin 0.001M) 3 [1.01M;2.001M;3.002M;4.001M;5.001M]
    |> should equal false

(* insert tests *)

[<Test>]
let ``insert_already_in``() =
    
    insert 3 [1;2;3]
    |> should equal [1;2;3]

[<Test>]
let ``insert_not_in``() =
    
    insert 3 [1;2]
    |> should equal [3;1;2]

(* insert' tests *)

let eqWithin2 tollerance (x:decimal) y = 
    let delta = abs (x - y) 
    let res = delta <= tollerance
    res

[<Test>]
let ``insert'_already_in``() =
    
    insert' (eqWithin2 0.001M) 3M [1.01M;2.001M;3.001M;4.001M;5.001M]
    |> should equal [1.01M;2.001M;3.001M;4.001M;5.001M]

[<Test>]
let ``insert'_not_in``() =
    
    insert' (eqWithin2 0.001M) 3M [1.01M;2.001M;3.002M;4.001M;5.001M]
    |> should equal [3M;1.01M;2.001M;3.002M;4.001M;5.001M]

(* setify tests *)

[<Test>]
let ``setify_test``() =
    
    setify [1;2;3;3]
    |> should equal [1;2;3]

(* setify' tests *)

[<Test>]
let ``setify'_test``() =
    
    setify' (eqWithin2 0.001M) [1M;2M;3.001M;3M]
    |> should equal [1M;2M;3.001M]

(* union tests *)

[<Test>]
let ``union_test``() =

    union [1;2;3;3] [1;2;7;8]
    |> should equal [3;1;2;7;8]

(* union' tests *)

[<Test>]
let ``union'_test``() =

    union' (eqWithin2 0.001M) [1M;2M;3.001M] [3M;1M;2M;7M;8M]
    |> should equal [3M;1M;2M;7M;8M]

(* unions tests *)

[<Test>]
let ``unions_test``() =

    unions [[1;2];[3;3;1];[2;7;8]]
    |> should equal [3;1;2;7;8]

(* unions' tests *)

[<Test>]
let ``unions'_test``() =

    unions' (eqWithin2 0.001M) [[1M;2M];[3.001M];[3M;1M;2M;7M;8M]]
    |> should equal [3M;1M;2M;7M;8M]

(* intersect tests *)

[<Test>]
let ``intersect_test``() =

    intersect [1;2;3;3] [1;2;7;8]
    |> should equal [1;2]

(* intersect' tests *)

[<Test>]
let ``intersect'_test``() =

    intersect' (eqWithin 0.001M) [1;2;3;3] [1.0001M;2.001M;7.001M;8.001M]
    |> should equal [1;2]

(* subtract tests *)

[<Test>]
let ``subtract_test``() =

    subtract [1;2;3;3] [1;2;7;8]
    |> should equal [3;3]

(* subtract' tests *)

[<Test>]
let ``subtract'_test``() =

    subtract' (eqWithin 0.001M) [1;2;3;3] [1.0001M;2.001M;7.001M;8.001M]
    |> should equal [3;3]

(* subset tests *)

[<Test>]
let ``subset_false``() =

    subset [1;2;3;3] [1;2;7;8]
    |> should equal false

[<Test>]
let ``subset_true``() =

    subset [1;2] [1;2;7;8]
    |> should equal true

(* subset' tests *)

[<Test>]
let ``subset'_false``() =

    subset' (eqWithin 0.001M) [1;2;3;3] [1.0001M;2.001M;7.001M;8.001M]
    |> should equal false

[<Test>]
let ``subset'_true``() =

    subset' (eqWithin 0.001M) [1;2] [1.0001M;2.001M;7.001M;8.001M]
    |> should equal true

(* disjoint tests *)

[<Test>]
let ``disjoint_false``() =

    disjoint [1;2;3;3] [1;2;7;8]
    |> should equal false

[<Test>]
let ``disjoint_true``() =

    disjoint [3;3] [1;2;7;8]
    |> should equal true

(* disjoint' tests *)

[<Test>]
let ``disjoint'_false``() =

    disjoint' (eqWithin 0.001M) [1;2;3;3] [1.0001M;2.001M;7.001M;8.001M]
    |> should equal false

[<Test>]
let ``disjoint'_true``() =

    disjoint' (eqWithin 0.001M) [1;2;3;3] [1.003M;2.002M;7.001M;8.001M]
    |> should equal true

(* set_eq tests *)

[<Test>]
let ``set_eq_false``() =

    set_eq [1;2;3] [1;2;3;4]
    |> should equal false

[<Test>]
let ``set_eq_true``() =

    set_eq [1;2;3;3] [1;2;3]
    |> should equal true

(* set_eq' tests *)

[<Test>]
let ``set_eq'_false``() =

    set_eq' (eqWithin2 0.001M) [1.003M;2M;3M] [1.001M;2.001M;3.001M]
    |> should equal false

[<Test>]
let ``set_eq'_true``() =

    set_eq' (eqWithin2 0.001M) [1.002M;2M;3M] [1.001M;2.001M;3.001M]
    |> should equal true

(* no_dups tests *)

[<Test>]
let ``no_dups_false``() =

    no_dups [1;2;3;3]
    |> should equal false

[<Test>]
let ``no_dups_true``() =

    no_dups [1;2;3]
    |> should equal true

(* no_dups' tests *)

[<Test>]
let ``no_dups'_false``() =

    no_dups' (eqWithin2 0.001M) [1M;2M;3.001M;3M]
    |> should equal false

[<Test>]
let ``no_dups'_true``() =

    no_dups' (eqWithin2 0.001M) [1M;2M;3.002M;3M]
    |> should equal true

(* string_of_int tests *)

[<Test>]
let ``string_of_int_false``() =

    string_of_int 1
    |> should equal "1"

(* char_implode tests *)

[<Test>]
let ``char_implode_test``() =

    char_implode ['d';'o';'m']
    |> should equal "dom"

(* char_implode tests *)

[<Test>]
let ``char_explode_test``() =

    char_explode "dom"
    |> should equal ['d';'o';'m']

(* implode tests *)

[<Test>]
let ``implode_test``() =

    implode ["dom";"enico"]
    |> should equal "domenico"

(* explode tests *)

[<Test>]
let ``explode_test``() =

    explode "domenico"
    |> should equal ["d";"o";"m";"e";"n";"i";"c";"o"]

(* string_variant tests *)

[<Test>]
let ``string_variant_test``() =

    let actual = string_variant ["prova"] "prova"

    string_variant ["prova"] "prova"
    |> should equal "prova'"

(* quote0 tests *)

[<Test>]
let ``quote0_test``() =

    quote0 "prova"
    |> should equal "'prova'"

(* quote tests *)

[<Test>]
let ``quote_test``() =

    quote "p\ro/v a"
    |> should equal "\"p\\013o/v a\""

(* report tests *)

[<Test>]
let ``report_test``() =

    testPrintf report "prova"
    |> should equal "[HZ] prova.\r\n"

(* warn tests *)

//qualcosa nel testPrint non mi permette di invocarlo subito dopo: eseguire questo test singolarmente

//[<Test>]
//let ``warn_test``() =
//
//    testPrintf warn "prova"
//    |> should equal "[HZ] WARNING: prova.\n"

(* merge tests *)

[<Test>]
let ``merge_decreasing_test``() =

    merge (>) [1;3;5] [2;4;6]
    |> should equal [2;4;6;1;3;5] //questo risultato però non lo capisco 

[<Test>]
let ``merge_increasing_test``() =

    let actual = merge (<) [1;3;5] [2;4;6]

    merge (<) [1;3;5] [2;4;6]
    |> should equal [1;2;3;4;5;6]

(* merge_sort tests *)

[<Test>]
let ``merge_sort_decreasing_test``() =

    let actual = mergesort (>) [1;3;5;2;4;6]

    mergesort (>) [1;3;5;2;4;6]
    |> should equal [6;5;4;3;2;1]

[<Test>]
let ``merge_sort_increasing_test``() =

    let actual = mergesort (>) [1;3;5;2;4;6]

    mergesort (<) [1;3;5;2;4;6]
    |> should equal [1;2;3;4;5;6]