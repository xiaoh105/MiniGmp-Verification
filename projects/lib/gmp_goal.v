Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import GmpLib.GmpNumber. Import Internal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition Zmax := Z.max.

(*----- Function gmp_abs -----*)

Definition gmp_abs_safety_wit_1 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (x_pre <> (INT_MIN)) |]
.

Definition gmp_abs_return_wit_1_1 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((-x_pre) = (Zabs (x_pre))) |]
  &&  emp
.

Definition gmp_abs_return_wit_1_2 := 
forall (x_pre: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| (x_pre = (Zabs (x_pre))) |]
  &&  emp
.

(*----- Function gmp_max -----*)

Definition gmp_max_return_wit_1_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre <= b_pre) |]
  &&  emp
|--
  [| (b_pre = (Zmax (a_pre) (b_pre))) |]
  &&  emp
.

Definition gmp_max_return_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre > b_pre) |]
  &&  emp
|--
  [| (a_pre = (Zmax (a_pre) (b_pre))) |]
  &&  emp
.

(*----- Function gmp_cmp -----*)

Definition gmp_cmp_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((0 - 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 - 0 )) |]
.

Definition gmp_cmp_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((0 - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 - 1 )) |]
.

Definition gmp_cmp_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre > b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| ((1 - 0 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 - 0 )) |]
.

Definition gmp_cmp_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < b_pre) |] 
  &&  [| (a_pre > b_pre) |]
  &&  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| False |]
.

Definition gmp_cmp_return_wit_1_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre > b_pre) |]
  &&  emp
|--
  ([| (a_pre < b_pre) |] 
  &&  [| ((1 - 0 ) = (-1)) |]
  &&  emp)
  ||
  ([| (a_pre = b_pre) |] 
  &&  [| ((1 - 0 ) = 0) |]
  &&  emp)
  ||
  ([| (a_pre > b_pre) |] 
  &&  [| ((1 - 0 ) = 1) |]
  &&  emp)
.

Definition gmp_cmp_return_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre < b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  emp
|--
  ([| (a_pre < b_pre) |] 
  &&  [| ((0 - 1 ) = (-1)) |]
  &&  emp)
  ||
  ([| (a_pre = b_pre) |] 
  &&  [| ((0 - 1 ) = 0) |]
  &&  emp)
  ||
  ([| (a_pre > b_pre) |] 
  &&  [| ((0 - 1 ) = 1) |]
  &&  emp)
.

Definition gmp_cmp_return_wit_1_3 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre >= b_pre) |] 
  &&  [| (a_pre <= b_pre) |]
  &&  emp
|--
  ([| (a_pre < b_pre) |] 
  &&  [| ((0 - 0 ) = (-1)) |]
  &&  emp)
  ||
  ([| (a_pre = b_pre) |] 
  &&  [| ((0 - 0 ) = 0) |]
  &&  emp)
  ||
  ([| (a_pre > b_pre) |] 
  &&  [| ((0 - 0 ) = 1) |]
  &&  emp)
.

(*----- Function mpn_copyi -----*)

Definition mpn_copyi_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) ,
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_uint_array_rec d_pre 0 cap2 l2 )
  **  (store_uint_array d_pre 0 nil )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_uint_array s_pre n_pre l )
  **  (store_undef_uint_array_rec s_pre (n_pre + 1 ) cap1 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_copyi_safety_wit_2 := 
forall (n_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (l': (@list Z)) (d: Z) (s: Z) (l_2: (@list Z)) (n: Z) (i: Z) (a: Z) (l2': (@list Z)) ,
  [| (l' = (cons (a) (l2'))) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |] 
  &&  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_2)) = n) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array d (i + 1 ) (replace_Znth (i) ((Znth i l_2 0)) ((app ((sublist (0) (i) (l_2))) ((cons (a) (nil)))))) )
  **  (store_uint_array s n l_2 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (store_uint_array_rec d (i + 1 ) cap2 l2' )
  **  ((( &( "s" ) )) # Ptr  |-> s)
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_copyi_entail_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) ,
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array_rec d_pre 0 cap2 l2 )
  **  (store_uint_array d_pre 0 nil )
  **  (store_uint_array s_pre n_pre l_2 )
  **  (store_undef_uint_array_rec s_pre (n_pre + 1 ) cap1 )
|--
  EX (l': (@list Z))  (l: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array s_pre n_pre l )
  **  (store_undef_uint_array_rec s_pre (n_pre + 1 ) cap1 )
  **  (store_uint_array d_pre 0 (sublist (0) (0) (l)) )
  **  (store_uint_array_rec d_pre 0 cap2 l' )
.

Definition mpn_copyi_entail_wit_2 := 
forall (n_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) (l'_2: (@list Z)) (d: Z) (s: Z) (l_3: (@list Z)) (n: Z) (i: Z) (a: Z) (l2': (@list Z)) ,
  [| (l'_2 = (cons (a) (l2'))) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |] 
  &&  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_3)) = n) |] 
  &&  [| (list_store_Z l_3 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array d (i + 1 ) (replace_Znth (i) ((Znth i l_3 0)) ((app ((sublist (0) (i) (l_3))) ((cons (a) (nil)))))) )
  **  (store_uint_array s n l_3 )
  **  (store_uint_array_rec d (i + 1 ) cap2 l2' )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
|--
  EX (l': (@list Z))  (l: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array s n l )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
  **  (store_uint_array d (i + 1 ) (sublist (0) ((i + 1 )) (l)) )
  **  (store_uint_array_rec d (i + 1 ) cap2 l' )
.

Definition mpn_copyi_return_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) (l': (@list Z)) (d: Z) (s: Z) (l: (@list Z)) (n: Z) (i: Z) ,
  [| (i >= n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array s n l )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
  **  (store_uint_array d i (sublist (0) (i) (l)) )
  **  (store_uint_array_rec d i cap2 l' )
|--
  (mpd_store_Z s_pre val n_pre cap1 )
  **  (mpd_store_Z d_pre val n_pre cap2 )
.

Definition mpn_copyi_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) ,
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (mpd_store_Z s_pre val n_pre cap1 )
  **  (store_uint_array d_pre cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (mpd_store_Z s_pre val n_pre cap1 )
  **  (store_uint_array d_pre cap2 l2 )
.

Definition mpn_copyi_partial_solve_wit_2_pure := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) ,
  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_uint_array s_pre n_pre l )
  **  (store_undef_uint_array_rec s_pre (n_pre + 1 ) cap1 )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (store_uint_array d_pre cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |]
.

Definition mpn_copyi_partial_solve_wit_2_aux := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) ,
  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array s_pre n_pre l )
  **  (store_undef_uint_array_rec s_pre (n_pre + 1 ) cap1 )
  **  (store_uint_array d_pre cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array d_pre cap2 l2 )
  **  (store_uint_array s_pre n_pre l )
  **  (store_undef_uint_array_rec s_pre (n_pre + 1 ) cap1 )
.

Definition mpn_copyi_partial_solve_wit_2 := mpn_copyi_partial_solve_wit_2_pure -> mpn_copyi_partial_solve_wit_2_aux.

Definition mpn_copyi_partial_solve_wit_3_pure := 
forall (n_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) (l': (@list Z)) (d: Z) (s: Z) (l: (@list Z)) (n: Z) (i: Z) ,
  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s)
  **  (store_uint_array s n l )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
  **  ((( &( "d" ) )) # Ptr  |-> d)
  **  (store_uint_array d i (sublist (0) (i) (l)) )
  **  (store_uint_array_rec d i cap2 l' )
|--
  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |]
.

Definition mpn_copyi_partial_solve_wit_3_aux := 
forall (n_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (l': (@list Z)) (d: Z) (s: Z) (l_2: (@list Z)) (n: Z) (i: Z) ,
  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_2)) = n) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array s n l_2 )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
  **  (store_uint_array d i (sublist (0) (i) (l_2)) )
  **  (store_uint_array_rec d i cap2 l' )
|--
  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |] 
  &&  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_2)) = n) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array_rec d i cap2 l' )
  **  (store_uint_array d i (sublist (0) (i) (l_2)) )
  **  (store_uint_array s n l_2 )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
.

Definition mpn_copyi_partial_solve_wit_3 := mpn_copyi_partial_solve_wit_3_pure -> mpn_copyi_partial_solve_wit_3_aux.

Definition mpn_copyi_partial_solve_wit_4 := 
forall (n_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (l': (@list Z)) (d: Z) (s: Z) (l_2: (@list Z)) (n: Z) (i: Z) (a: Z) (l2': (@list Z)) ,
  [| (l' = (cons (a) (l2'))) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |] 
  &&  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_2)) = n) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array_rec d (i + 1 ) cap2 l2' )
  **  (store_uint_array d (i + 1 ) (app ((sublist (0) (i) (l_2))) ((cons (a) (nil)))) )
  **  (store_uint_array s n l_2 )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
|--
  [| (l' = (cons (a) (l2'))) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |] 
  &&  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_2)) = n) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (((s + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_2 0))
  **  (store_uint_array_missing_i_rec s i 0 n l_2 )
  **  (store_uint_array_rec d (i + 1 ) cap2 l2' )
  **  (store_uint_array d (i + 1 ) (app ((sublist (0) (i) (l_2))) ((cons (a) (nil)))) )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
.

Definition mpn_copyi_partial_solve_wit_5 := 
forall (n_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (l': (@list Z)) (d: Z) (s: Z) (l_2: (@list Z)) (n: Z) (i: Z) (a: Z) (l2': (@list Z)) ,
  [| (l' = (cons (a) (l2'))) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |] 
  &&  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_2)) = n) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (store_uint_array s n l_2 )
  **  (store_uint_array_rec d (i + 1 ) cap2 l2' )
  **  (store_uint_array d (i + 1 ) (app ((sublist (0) (i) (l_2))) ((cons (a) (nil)))) )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
|--
  [| (l' = (cons (a) (l2'))) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |] 
  &&  [| (i < n) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| ((Zlength (l_2)) = n) |] 
  &&  [| (list_store_Z l_2 val ) |] 
  &&  [| (n <= cap1) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |]
  &&  (((d + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (store_uint_array_missing_i_rec d i 0 (i + 1 ) (app ((sublist (0) (i) (l_2))) ((cons (a) (nil)))) )
  **  (store_uint_array s n l_2 )
  **  (store_uint_array_rec d (i + 1 ) cap2 l2' )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
.

Definition mpn_copyi_which_implies_wit_1 := 
forall (cap1: Z) (val: Z) (n: Z) (s: Z) ,
  (mpd_store_Z s val n cap1 )
|--
  EX (l: (@list Z)) ,
  [| (n <= cap1) |] 
  &&  [| ((Zlength (l)) = n) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z l val ) |]
  &&  (store_uint_array s n l )
  **  (store_undef_uint_array_rec s (n + 1 ) cap1 )
.

Definition mpn_copyi_which_implies_wit_2 := 
forall (cap2: Z) (l2: (@list Z)) (d: Z) ,
  [| ((Zlength (l2)) = cap2) |]
  &&  (store_uint_array d cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |]
  &&  (store_uint_array_rec d 0 cap2 l2 )
  **  (store_uint_array d 0 nil )
.

Definition mpn_copyi_which_implies_wit_3 := 
forall (cap2: Z) (l': (@list Z)) (l: (@list Z)) (i: Z) (n: Z) (d: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |]
  &&  (store_uint_array_rec d i cap2 l' )
  **  (store_uint_array d i (sublist (0) (i) (l)) )
|--
  EX (a: Z)  (l2': (@list Z)) ,
  [| (l' = (cons (a) (l2'))) |] 
  &&  [| (i < n) |] 
  &&  [| (n <= cap2) |]
  &&  (store_uint_array_rec d (i + 1 ) cap2 l2' )
  **  (store_uint_array d (i + 1 ) (app ((sublist (0) (i) (l))) ((cons (a) (nil)))) )
.

Module Type VC_Correct.

Axiom proof_of_gmp_abs_safety_wit_1 : gmp_abs_safety_wit_1.
Axiom proof_of_gmp_abs_return_wit_1_1 : gmp_abs_return_wit_1_1.
Axiom proof_of_gmp_abs_return_wit_1_2 : gmp_abs_return_wit_1_2.
Axiom proof_of_gmp_max_return_wit_1_1 : gmp_max_return_wit_1_1.
Axiom proof_of_gmp_max_return_wit_1_2 : gmp_max_return_wit_1_2.
Axiom proof_of_gmp_cmp_safety_wit_1 : gmp_cmp_safety_wit_1.
Axiom proof_of_gmp_cmp_safety_wit_2 : gmp_cmp_safety_wit_2.
Axiom proof_of_gmp_cmp_safety_wit_3 : gmp_cmp_safety_wit_3.
Axiom proof_of_gmp_cmp_safety_wit_4 : gmp_cmp_safety_wit_4.
Axiom proof_of_gmp_cmp_return_wit_1_1 : gmp_cmp_return_wit_1_1.
Axiom proof_of_gmp_cmp_return_wit_1_2 : gmp_cmp_return_wit_1_2.
Axiom proof_of_gmp_cmp_return_wit_1_3 : gmp_cmp_return_wit_1_3.
Axiom proof_of_mpn_copyi_safety_wit_1 : mpn_copyi_safety_wit_1.
Axiom proof_of_mpn_copyi_safety_wit_2 : mpn_copyi_safety_wit_2.
Axiom proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Axiom proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Axiom proof_of_mpn_copyi_return_wit_1 : mpn_copyi_return_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_1 : mpn_copyi_partial_solve_wit_1.
Axiom proof_of_mpn_copyi_partial_solve_wit_2_pure : mpn_copyi_partial_solve_wit_2_pure.
Axiom proof_of_mpn_copyi_partial_solve_wit_2 : mpn_copyi_partial_solve_wit_2.
Axiom proof_of_mpn_copyi_partial_solve_wit_3_pure : mpn_copyi_partial_solve_wit_3_pure.
Axiom proof_of_mpn_copyi_partial_solve_wit_3 : mpn_copyi_partial_solve_wit_3.
Axiom proof_of_mpn_copyi_partial_solve_wit_4 : mpn_copyi_partial_solve_wit_4.
Axiom proof_of_mpn_copyi_partial_solve_wit_5 : mpn_copyi_partial_solve_wit_5.
Axiom proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Axiom proof_of_mpn_copyi_which_implies_wit_2 : mpn_copyi_which_implies_wit_2.
Axiom proof_of_mpn_copyi_which_implies_wit_3 : mpn_copyi_which_implies_wit_3.

End VC_Correct.
