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
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import GmpLib.GmpNumber. Import Internal.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope sac.

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
  [| (b_pre = (Z.max (a_pre) (b_pre))) |]
  &&  emp
.

Definition gmp_max_return_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (a_pre > b_pre) |]
  &&  emp
|--
  [| (a_pre = (Z.max (a_pre) (b_pre))) |]
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
  **  (store_undef_uint_array_rec s_pre n_pre cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s_pre n_pre cap1 )
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
  **  (store_undef_uint_array_rec s_pre n_pre cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s_pre n_pre cap1 )
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
  **  (store_undef_uint_array_rec s_pre n_pre cap1 )
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
  **  (store_undef_uint_array_rec s_pre n_pre cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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
  **  (store_undef_uint_array_rec s n cap1 )
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

(*----- Function mpn_cmp -----*)

Definition mpn_cmp_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition mpn_cmp_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_cmp_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) <= (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array bp_pre n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  [| (1 <> (INT_MIN)) |]
.

Definition mpn_cmp_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) <= (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array bp_pre n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) > (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array bp_pre n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) = (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array bp_pre n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  [| ((n - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n - 1 )) |]
.

Definition mpn_cmp_safety_wit_7 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| (n < 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_cmp_entail_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
|--
  [| ((-1) <= (n_pre - 1 )) |] 
  &&  [| ((n_pre - 1 ) < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist (((n_pre - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n_pre - 1 ) + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
.

Definition mpn_cmp_entail_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) = (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array bp_pre n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
|--
  [| ((-1) <= (n - 1 )) |] 
  &&  [| ((n - 1 ) < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist (((n - 1 ) + 1 )) (n_pre) (l1)) = (sublist (((n - 1 ) + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
.

Definition mpn_cmp_return_wit_1_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) <= (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array bp_pre n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| ((-1) = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| ((-1) = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| ((-1) = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
.

Definition mpn_cmp_return_wit_1_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| ((Znth n l1 0) > (Znth n l2 0)) |] 
  &&  [| ((Znth n l1 0) <> (Znth n l2 0)) |] 
  &&  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array bp_pre n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| (1 = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (1 = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (1 = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
.

Definition mpn_cmp_return_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| (n < 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| (0 = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (0 = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (0 = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 ))
.

Definition mpn_cmp_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 )
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 )
.

Definition mpn_cmp_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
|--
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (((ap_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l1 0))
  **  (store_uint_array_missing_i_rec ap_pre n 0 n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
.

Definition mpn_cmp_partial_solve_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (l1: (@list Z)) (n: Z) ,
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
|--
  [| (n >= 0) |] 
  &&  [| ((-1) <= n) |] 
  &&  [| (n < n_pre) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| ((sublist ((n + 1 )) (n_pre) (l1)) = (sublist ((n + 1 )) (n_pre) (l2))) |] 
  &&  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (((bp_pre + (n * sizeof(UINT) ) )) # UInt  |-> (Znth n l2 0))
  **  (store_uint_array_missing_i_rec bp_pre n 0 n_pre l2 )
  **  (store_uint_array ap_pre n_pre l1 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
.

Definition mpn_cmp_which_implies_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  (mpd_store_Z_compact ap_pre val1 n_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 n_pre cap2 )
|--
  EX (l2: (@list Z))  (l1: (@list Z)) ,
  [| (list_store_Z_compact l1 val1 ) |] 
  &&  [| (list_store_Z_compact l2 val2 ) |] 
  &&  [| (n_pre = (Zlength (l1))) |] 
  &&  [| (n_pre = (Zlength (l2))) |]
  &&  (store_uint_array ap_pre n_pre l1 )
  **  (store_uint_array bp_pre n_pre l2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap2 )
.

(*----- Function mpn_cmp4 -----*)

Definition mpn_cmp4_safety_wit_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp4_safety_wit_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre < bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  [| (1 <> (INT_MIN)) |]
.

Definition mpn_cmp4_safety_wit_3 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre < bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_cmp4_return_wit_1_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre >= bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| (1 = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (1 = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (1 = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
.

Definition mpn_cmp4_return_wit_1_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre < bn_pre) |] 
  &&  [| (an_pre <> bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| ((-1) = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| ((-1) = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| ((-1) = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
.

Definition mpn_cmp4_return_wit_2_1 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (retval: Z) ,
  [| (val1 > val2) |] 
  &&  [| (retval = 1) |] 
  &&  [| (an_pre <= cap2) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 an_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| (retval = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (retval = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (retval = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
.

Definition mpn_cmp4_return_wit_2_2 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (retval: Z) ,
  [| (val1 = val2) |] 
  &&  [| (retval = 0) |] 
  &&  [| (an_pre <= cap2) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 an_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| (retval = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (retval = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (retval = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
.

Definition mpn_cmp4_return_wit_2_3 := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) (retval: Z) ,
  [| (val1 < val2) |] 
  &&  [| (retval = (-1)) |] 
  &&  [| (an_pre <= cap2) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 an_pre cap2 )
|--
  ([| (val1 < val2) |] 
  &&  [| (retval = (-1)) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 = val2) |] 
  &&  [| (retval = 0) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
  ||
  ([| (val1 > val2) |] 
  &&  [| (retval = 1) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 ))
.

Definition mpn_cmp4_partial_solve_wit_1_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  [| (an_pre = bn_pre) |] 
  &&  [| (bn_pre <= cap2) |]
.

Definition mpn_cmp4_partial_solve_wit_1_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  [| (an_pre = bn_pre) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
.

Definition mpn_cmp4_partial_solve_wit_1 := mpn_cmp4_partial_solve_wit_1_pure -> mpn_cmp4_partial_solve_wit_1_aux.

Definition mpn_cmp4_partial_solve_wit_2_pure := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre <= cap2) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  ((( &( "bn" ) )) # Int  |-> bn_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "an" ) )) # Int  |-> an_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  [| (0 <= an_pre) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (an_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
.

Definition mpn_cmp4_partial_solve_wit_2_aux := 
forall (bn_pre: Z) (bp_pre: Z) (an_pre: Z) (ap_pre: Z) (val2: Z) (val1: Z) (cap2: Z) (cap1: Z) ,
  [| (an_pre <= cap2) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 bn_pre cap2 )
|--
  [| (0 <= an_pre) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (an_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (an_pre <= cap2) |] 
  &&  [| (an_pre = bn_pre) |] 
  &&  [| (an_pre >= 0) |] 
  &&  [| (bn_pre >= 0) |] 
  &&  [| (an_pre <= cap1) |] 
  &&  [| (bn_pre <= cap2) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |]
  &&  (mpd_store_Z_compact ap_pre val1 an_pre cap1 )
  **  (mpd_store_Z_compact bp_pre val2 an_pre cap2 )
.

Definition mpn_cmp4_partial_solve_wit_2 := mpn_cmp4_partial_solve_wit_2_pure -> mpn_cmp4_partial_solve_wit_2_aux.

Definition mpn_cmp4_which_implies_wit_1 := 
forall (bn_pre: Z) (an_pre: Z) (cap2: Z) ,
  [| (an_pre = bn_pre) |] 
  &&  [| (bn_pre <= cap2) |]
  &&  emp
|--
  [| (an_pre <= cap2) |]
  &&  emp
.

(*----- Function mpn_normalized_size -----*)

Definition mpn_normalized_size_safety_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_normalized_size_safety_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| ((n - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n - 1 )) |]
.

Definition mpn_normalized_size_safety_wit_3 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpn_normalized_size_safety_wit_4 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (store_undef_uint_array_rec xp_pre n cap )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_normalized_size_safety_wit_5 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (store_undef_uint_array_rec xp_pre n cap )
  **  ((( &( "xp" ) )) # Ptr  |-> xp_pre)
|--
  [| ((n - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n - 1 )) |]
.

Definition mpn_normalized_size_entail_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) ,
  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n_pre (sublist (0) (n_pre) (l)) )
  **  (store_undef_uint_array_rec xp_pre n_pre cap )
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n_pre (sublist (0) (n_pre) (l)) )
  **  (store_undef_uint_array_rec xp_pre n_pre cap )
.

Definition mpn_normalized_size_entail_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) = 0) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
|--
  [| ((n - 1 ) >= 0) |] 
  &&  [| ((n - 1 ) <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) ((n - 1 )) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre (n - 1 ) (sublist (0) ((n - 1 )) (l)) )
  **  (store_undef_uint_array_rec xp_pre (n - 1 ) cap )
.

Definition mpn_normalized_size_return_wit_1_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| (n <= 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
|--
  [| (0 <= n) |] 
  &&  [| (n <= cap) |]
  &&  (mpd_store_Z_compact xp_pre val n cap )
.

Definition mpn_normalized_size_return_wit_1_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| ((Znth (n - 1 ) (sublist (0) (n) (l)) 0) <> 0) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
|--
  [| (0 <= n) |] 
  &&  [| (n <= cap) |]
  &&  (mpd_store_Z_compact xp_pre val n cap )
.

Definition mpn_normalized_size_partial_solve_wit_1 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (mpd_store_Z xp_pre val n_pre cap )
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (mpd_store_Z xp_pre val n_pre cap )
.

Definition mpn_normalized_size_partial_solve_wit_2 := 
forall (n_pre: Z) (xp_pre: Z) (val: Z) (cap: Z) (l: (@list Z)) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
|--
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (n <= n_pre) |] 
  &&  [| (n_pre >= 0) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| (list_store_Z (sublist (0) (n_pre) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap) |] 
  &&  [| (cap <= 100000000) |]
  &&  (((xp_pre + ((n - 1 ) * sizeof(UINT) ) )) # UInt  |-> (Znth (n - 1 ) (sublist (0) (n) (l)) 0))
  **  (store_uint_array_missing_i_rec xp_pre (n - 1 ) 0 n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
.

Definition mpn_normalized_size_which_implies_wit_1 := 
forall (xp_pre: Z) (val: Z) (cap: Z) (n: Z) ,
  (mpd_store_Z xp_pre val n cap )
|--
  EX (l: (@list Z)) ,
  [| (list_store_Z (sublist (0) (n) (l)) val ) |] 
  &&  [| ((Zlength (l)) = n) |]
  &&  (store_uint_array xp_pre n (sublist (0) (n) (l)) )
  **  (store_undef_uint_array_rec xp_pre n cap )
.

(*----- Function mpn_add_1 -----*)

Definition mpn_add_1_safety_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) ,
  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (store_uint_array rp_pre cap2 l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_add_1_safety_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) (a: Z) (l''': (@list Z)) ,
  [| (l'' = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) >= b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32))) ((app (l') ((cons (a) (nil)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  (store_uint_array ap_pre n_pre l_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l_2 0) + b )) (32)))
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_1_safety_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) (a: Z) (l''': (@list Z)) ,
  [| (l'' = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) < b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32))) ((app (l') ((cons (a) (nil)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  (store_uint_array ap_pre n_pre l_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l_2 0) + b )) (32)))
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_1_entail_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) ,
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array_rec rp_pre 0 cap2 l2 )
  **  (store_uint_array rp_pre 0 nil )
  **  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
|--
  EX (l'': (@list Z))  (l': (@list Z))  (val2: Z)  (val1: Z)  (l: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (0) (l)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b_pre * (Z.pow (UINT_MOD) (0)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = 0) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre 0 l' )
  **  (store_uint_array_rec rp_pre 0 cap2 l'' )
.

Definition mpn_add_1_entail_wit_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l_2 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
  **  ((( &( "b" ) )) # UInt  |-> b)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  ((( &( "b" ) )) # UInt  |-> b)
  **  (store_uint_array ap_pre n_pre l_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l_2 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
.

Definition mpn_add_1_entail_wit_3_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) (b: Z) (l''_2: (@list Z)) (l'_2: (@list Z)) (val2_2: Z) (val1_2: Z) (l_3: (@list Z)) (i: Z) (a: Z) (l''': (@list Z)) ,
  [| (l''_2 = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_3 0) + b )) (32)) < b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_3 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_3)) val1_2 ) |] 
  &&  [| (list_store_Z l'_2 val2_2 ) |] 
  &&  [| ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre )) |] 
  &&  [| ((Zlength (l'_2)) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((Znth i l_3 0) + b )) (32))) ((app (l'_2) ((cons (a) (nil)))))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  (store_uint_array ap_pre n_pre l_3 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
|--
  EX (l'': (@list Z))  (l': (@list Z))  (val2: Z)  (val1: Z)  (l: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre (i + 1 ) l' )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l'' )
.

Definition mpn_add_1_entail_wit_3_2 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) (b: Z) (l''_2: (@list Z)) (l'_2: (@list Z)) (val2_2: Z) (val1_2: Z) (l_3: (@list Z)) (i: Z) (a: Z) (l''': (@list Z)) ,
  [| (l''_2 = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_3 0) + b )) (32)) >= b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_3 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_3)) val1_2 ) |] 
  &&  [| (list_store_Z l'_2 val2_2 ) |] 
  &&  [| ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b_pre )) |] 
  &&  [| ((Zlength (l'_2)) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((Znth i l_3 0) + b )) (32))) ((app (l'_2) ((cons (a) (nil)))))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  (store_uint_array ap_pre n_pre l_3 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
|--
  EX (l'': (@list Z))  (l': (@list Z))  (val2: Z)  (val1: Z)  (l: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = (i + 1 )) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre (i + 1 ) l' )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l'' )
.

Definition mpn_add_1_return_wit_1 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l_2: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l_2)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
|--
  EX (val': Z) ,
  [| ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val + b_pre )) |]
  &&  (mpd_store_Z_compact ap_pre val n_pre cap1 )
  **  (mpd_store_Z rp_pre val' n_pre cap2 )
.

Definition mpn_add_1_partial_solve_wit_1 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) ,
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (mpd_store_Z_compact ap_pre val n_pre cap1 )
  **  (store_uint_array rp_pre cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (mpd_store_Z_compact ap_pre val n_pre cap1 )
  **  (store_uint_array rp_pre cap2 l2 )
.

Definition mpn_add_1_partial_solve_wit_2_pure := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) ,
  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (store_uint_array rp_pre cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |]
.

Definition mpn_add_1_partial_solve_wit_2_aux := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) ,
  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array rp_pre cap2 l2 )
  **  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
.

Definition mpn_add_1_partial_solve_wit_2 := mpn_add_1_partial_solve_wit_2_pure -> mpn_add_1_partial_solve_wit_2_aux.

Definition mpn_add_1_partial_solve_wit_3 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_2 0))
  **  (store_uint_array_missing_i_rec ap_pre i 0 n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
.

Definition mpn_add_1_partial_solve_wit_4_pure := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) >= b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  ((( &( "b" ) )) # UInt  |-> 0)
  **  (store_uint_array ap_pre n_pre l_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l_2 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |]
.

Definition mpn_add_1_partial_solve_wit_4_aux := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) >= b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) >= b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
  **  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
.

Definition mpn_add_1_partial_solve_wit_4 := mpn_add_1_partial_solve_wit_4_pure -> mpn_add_1_partial_solve_wit_4_aux.

Definition mpn_add_1_partial_solve_wit_5_pure := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) < b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  ((( &( "b" ) )) # UInt  |-> 1)
  **  (store_uint_array ap_pre n_pre l_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l_2 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |]
.

Definition mpn_add_1_partial_solve_wit_5_aux := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) < b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
  **  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) < b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
  **  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
.

Definition mpn_add_1_partial_solve_wit_5 := mpn_add_1_partial_solve_wit_5_pure -> mpn_add_1_partial_solve_wit_5_aux.

Definition mpn_add_1_partial_solve_wit_6 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) (a: Z) (l''': (@list Z)) ,
  [| (l'' = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) < b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l') ((cons (a) (nil)))) )
  **  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
|--
  [| (l'' = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) < b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (store_uint_array_missing_i_rec rp_pre i 0 (i + 1 ) (app (l') ((cons (a) (nil)))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
.

Definition mpn_add_1_partial_solve_wit_7 := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (cap2: Z) (cap1: Z) (l2: (@list Z)) (val: Z) (l: (@list Z)) (b: Z) (l'': (@list Z)) (l': (@list Z)) (val2: Z) (val1: Z) (l_2: (@list Z)) (i: Z) (a: Z) (l''': (@list Z)) ,
  [| (l'' = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) >= b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l') ((cons (a) (nil)))) )
  **  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
|--
  [| (l'' = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_2 0) + b )) (32)) >= b) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (list_store_Z_compact l_2 val ) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_2)) val1 ) |] 
  &&  [| (list_store_Z l' val2 ) |] 
  &&  [| ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b_pre )) |] 
  &&  [| ((Zlength (l')) = i) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |] 
  &&  [| ((Zlength (l2)) = cap2) |] 
  &&  [| (cap2 >= n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (cap2 <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap1) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (store_uint_array_missing_i_rec rp_pre i 0 (i + 1 ) (app (l') ((cons (a) (nil)))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  (store_uint_array ap_pre n_pre l_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
.

Definition mpn_add_1_which_implies_wit_1 := 
forall (n_pre: Z) (ap_pre: Z) (cap1: Z) (val: Z) ,
  (mpd_store_Z_compact ap_pre val n_pre cap1 )
|--
  EX (l: (@list Z)) ,
  [| (n_pre <= cap1) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| (cap1 <= 100000000) |] 
  &&  [| (list_store_Z_compact l val ) |]
  &&  (store_uint_array ap_pre n_pre l )
  **  (store_undef_uint_array_rec ap_pre n_pre cap1 )
.

Definition mpn_add_1_which_implies_wit_2 := 
forall (rp_pre: Z) (cap2: Z) (l2: (@list Z)) ,
  [| ((Zlength (l2)) = cap2) |]
  &&  (store_uint_array rp_pre cap2 l2 )
|--
  [| ((Zlength (l2)) = cap2) |]
  &&  (store_uint_array_rec rp_pre 0 cap2 l2 )
  **  (store_uint_array rp_pre 0 nil )
.

Definition mpn_add_1_which_implies_wit_3 := 
forall (n_pre: Z) (rp_pre: Z) (cap2: Z) (l'': (@list Z)) (l': (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |]
  &&  (store_uint_array rp_pre i l' )
  **  (store_uint_array_rec rp_pre i cap2 l'' )
|--
  EX (a: Z)  (l''': (@list Z)) ,
  [| (l'' = (cons (a) (l'''))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap2) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap2 l''' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l') ((cons (a) (nil)))) )
.

(*----- Function mpn_add_n -----*)

Definition mpn_add_n_safety_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre 0 cap_r l_r )
  **  (store_uint_array rp_pre 0 nil )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_add_n_safety_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre 0 cap_r l_r )
  **  (store_uint_array rp_pre 0 nil )
  **  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpn_add_n_safety_wit_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32))) ((app (l_r_prefix) ((cons (a) (nil)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_safety_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32))) ((app (l_r_prefix) ((cons (a) (nil)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_safety_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32))) ((app (l_r_prefix) ((cons (a) (nil)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_safety_wit_6 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32))) ((app (l_r_prefix) ((cons (a) (nil)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition mpn_add_n_entail_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a_2: (@list Z)) (l_b_2: (@list Z)) ,
  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre 0 cap_r l_r )
  **  (store_uint_array rp_pre 0 nil )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
|--
  EX (l_r_suffix: (@list Z))  (l_r_prefix: (@list Z))  (val_r_prefix: Z)  (val_b_prefix: Z)  (val_a_prefix: Z)  (l_b: (@list Z))  (l_a: (@list Z)) ,
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (0) (l_a)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (0) (l_b)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = 0) |] 
  &&  [| ((val_r_prefix + (0 * (Z.pow (UINT_MOD) (0)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre 0 l_r_prefix )
  **  (store_uint_array_rec rp_pre 0 cap_r l_r_suffix )
.

Definition mpn_add_n_entail_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  ((( &( "cy" ) )) # UInt  |-> cy)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
.

Definition mpn_add_n_entail_wit_3_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a_2: (@list Z)) (l_b_2: (@list Z)) (l_r_suffix_2: (@list Z)) (cy: Z) (l_r_prefix_2: (@list Z)) (val_r_prefix_2: Z) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (l_b_3: (@list Z)) (l_a_3: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix_2 = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32)) >= (Znth i l_b_3 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_3 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_3 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_3)) val_a_prefix_2 ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_3)) val_b_prefix_2 ) |] 
  &&  [| (list_store_Z l_r_prefix_2 val_r_prefix_2 ) |] 
  &&  [| ((Zlength (l_r_prefix_2)) = i) |] 
  &&  [| ((val_r_prefix_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32))) ((app (l_r_prefix_2) ((cons (a) (nil)))))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_3 )
  **  (store_uint_array ap_pre n_pre l_a_3 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  EX (l_r_suffix: (@list Z))  (l_r_prefix: (@list Z))  (val_r_prefix: Z)  (val_b_prefix: Z)  (val_a_prefix: Z)  (l_b: (@list Z))  (l_a: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_a)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_b)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = (i + 1 )) |] 
  &&  [| ((val_r_prefix + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre (i + 1 ) l_r_prefix )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix )
.

Definition mpn_add_n_entail_wit_3_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a_2: (@list Z)) (l_b_2: (@list Z)) (l_r_suffix_2: (@list Z)) (cy: Z) (l_r_prefix_2: (@list Z)) (val_r_prefix_2: Z) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (l_b_3: (@list Z)) (l_a_3: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix_2 = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32)) < (Znth i l_b_3 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_3 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_3 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_3)) val_a_prefix_2 ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_3)) val_b_prefix_2 ) |] 
  &&  [| (list_store_Z l_r_prefix_2 val_r_prefix_2 ) |] 
  &&  [| ((Zlength (l_r_prefix_2)) = i) |] 
  &&  [| ((val_r_prefix_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32))) ((app (l_r_prefix_2) ((cons (a) (nil)))))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_3 )
  **  (store_uint_array ap_pre n_pre l_a_3 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  EX (l_r_suffix: (@list Z))  (l_r_prefix: (@list Z))  (val_r_prefix: Z)  (val_b_prefix: Z)  (val_a_prefix: Z)  (l_b: (@list Z))  (l_a: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_a)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_b)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = (i + 1 )) |] 
  &&  [| ((val_r_prefix + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre (i + 1 ) l_r_prefix )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix )
.

Definition mpn_add_n_entail_wit_3_3 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a_2: (@list Z)) (l_b_2: (@list Z)) (l_r_suffix_2: (@list Z)) (cy: Z) (l_r_prefix_2: (@list Z)) (val_r_prefix_2: Z) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (l_b_3: (@list Z)) (l_a_3: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix_2 = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32)) >= (Znth i l_b_3 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_3 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_3 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_3)) val_a_prefix_2 ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_3)) val_b_prefix_2 ) |] 
  &&  [| (list_store_Z l_r_prefix_2 val_r_prefix_2 ) |] 
  &&  [| ((Zlength (l_r_prefix_2)) = i) |] 
  &&  [| ((val_r_prefix_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32))) ((app (l_r_prefix_2) ((cons (a) (nil)))))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_3 )
  **  (store_uint_array ap_pre n_pre l_a_3 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  EX (l_r_suffix: (@list Z))  (l_r_prefix: (@list Z))  (val_r_prefix: Z)  (val_b_prefix: Z)  (val_a_prefix: Z)  (l_b: (@list Z))  (l_a: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_a)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_b)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = (i + 1 )) |] 
  &&  [| ((val_r_prefix + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre (i + 1 ) l_r_prefix )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix )
.

Definition mpn_add_n_entail_wit_3_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a_2: (@list Z)) (l_b_2: (@list Z)) (l_r_suffix_2: (@list Z)) (cy: Z) (l_r_prefix_2: (@list Z)) (val_r_prefix_2: Z) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (l_b_3: (@list Z)) (l_a_3: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix_2 = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32)) < (Znth i l_b_3 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_3 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_3 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_3)) val_a_prefix_2 ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_3)) val_b_prefix_2 ) |] 
  &&  [| (list_store_Z l_r_prefix_2 val_r_prefix_2 ) |] 
  &&  [| ((Zlength (l_r_prefix_2)) = i) |] 
  &&  [| ((val_r_prefix_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre (i + 1 ) (replace_Znth (i) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_3 0) + cy )) (32)) + (Znth i l_b_3 0) )) (32))) ((app (l_r_prefix_2) ((cons (a) (nil)))))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_3 )
  **  (store_uint_array ap_pre n_pre l_a_3 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  EX (l_r_suffix: (@list Z))  (l_r_prefix: (@list Z))  (val_r_prefix: Z)  (val_b_prefix: Z)  (val_a_prefix: Z)  (l_b: (@list Z))  (l_a: (@list Z)) ,
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_a)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) ((i + 1 )) (l_b)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = (i + 1 )) |] 
  &&  [| ((val_r_prefix + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre (i + 1 ) l_r_prefix )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix )
.

Definition mpn_add_n_return_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a_2: (@list Z)) (l_b_2: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b: (@list Z)) (l_a: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b_2)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a_2)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  EX (val_r_out: Z) ,
  [| ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a + val_b )) |]
  &&  (mpd_store_Z_compact ap_pre val_a n_pre cap_a )
  **  (mpd_store_Z_compact bp_pre val_b n_pre cap_b )
  **  (mpd_store_Z rp_pre val_r_out n_pre cap_r )
.

Definition mpn_add_n_partial_solve_wit_1 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) ,
  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (mpd_store_Z_compact ap_pre val_a n_pre cap_a )
  **  (mpd_store_Z_compact bp_pre val_b n_pre cap_b )
  **  (store_uint_array rp_pre cap_r l_r )
|--
  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (mpd_store_Z_compact ap_pre val_a n_pre cap_a )
  **  (mpd_store_Z_compact bp_pre val_b n_pre cap_b )
  **  (store_uint_array rp_pre cap_r l_r )
.

Definition mpn_add_n_partial_solve_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) ,
  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (mpd_store_Z_compact bp_pre val_b n_pre cap_b )
  **  (store_uint_array rp_pre cap_r l_r )
|--
  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (mpd_store_Z_compact bp_pre val_b n_pre cap_b )
  **  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array rp_pre cap_r l_r )
.

Definition mpn_add_n_partial_solve_wit_3_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (store_uint_array rp_pre cap_r l_r )
|--
  [| ((Zlength (l_r)) = cap_r) |]
.

Definition mpn_add_n_partial_solve_wit_3_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) ,
  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array rp_pre cap_r l_r )
|--
  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre cap_r l_r )
  **  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
.

Definition mpn_add_n_partial_solve_wit_3 := mpn_add_n_partial_solve_wit_3_pure -> mpn_add_n_partial_solve_wit_3_aux.

Definition mpn_add_n_partial_solve_wit_4 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (((ap_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_a_2 0))
  **  (store_uint_array_missing_i_rec ap_pre i 0 n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
.

Definition mpn_add_n_partial_solve_wit_5 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (((bp_pre + (i * sizeof(UINT) ) )) # UInt  |-> (Znth i l_b_2 0))
  **  (store_uint_array_missing_i_rec bp_pre i 0 n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
.

Definition mpn_add_n_partial_solve_wit_6_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |]
.

Definition mpn_add_n_partial_solve_wit_6_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_partial_solve_wit_6 := mpn_add_n_partial_solve_wit_6_pure -> mpn_add_n_partial_solve_wit_6_aux.

Definition mpn_add_n_partial_solve_wit_7_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |]
.

Definition mpn_add_n_partial_solve_wit_7_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_partial_solve_wit_7 := mpn_add_n_partial_solve_wit_7_pure -> mpn_add_n_partial_solve_wit_7_aux.

Definition mpn_add_n_partial_solve_wit_8_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |]
.

Definition mpn_add_n_partial_solve_wit_8_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_partial_solve_wit_8 := mpn_add_n_partial_solve_wit_8_pure -> mpn_add_n_partial_solve_wit_8_aux.

Definition mpn_add_n_partial_solve_wit_9_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b_2 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a_2 0))
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |]
.

Definition mpn_add_n_partial_solve_wit_9_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) ,
  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
  **  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_partial_solve_wit_9 := mpn_add_n_partial_solve_wit_9_pure -> mpn_add_n_partial_solve_wit_9_aux.

Definition mpn_add_n_partial_solve_wit_10 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (store_uint_array_missing_i_rec rp_pre i 0 (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_partial_solve_wit_11 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) < cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (store_uint_array_missing_i_rec rp_pre i 0 (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_partial_solve_wit_12 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) >= (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (store_uint_array_missing_i_rec rp_pre i 0 (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_partial_solve_wit_13 := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (l_r: (@list Z)) (val_b: Z) (val_a: Z) (cap_r: Z) (cap_b: Z) (cap_a: Z) (l_a: (@list Z)) (l_b: (@list Z)) (l_r_suffix: (@list Z)) (cy: Z) (l_r_prefix: (@list Z)) (val_r_prefix: Z) (val_b_prefix: Z) (val_a_prefix: Z) (l_b_2: (@list Z)) (l_a_2: (@list Z)) (i: Z) (a: Z) (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
|--
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) + (Znth i l_b_2 0) )) (32)) < (Znth i l_b_2 0)) |] 
  &&  [| ((unsigned_last_nbits (((Znth i l_a_2 0) + cy )) (32)) >= cy) |] 
  &&  [| (0 <= cy) |] 
  &&  [| (cy <= UINT_MAX) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |] 
  &&  [| (list_store_Z_compact l_a_2 val_a ) |] 
  &&  [| (list_store_Z_compact l_b_2 val_b ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_a_2)) val_a_prefix ) |] 
  &&  [| (list_store_Z (sublist (0) (i) (l_b_2)) val_b_prefix ) |] 
  &&  [| (list_store_Z l_r_prefix val_r_prefix ) |] 
  &&  [| ((Zlength (l_r_prefix)) = i) |] 
  &&  [| ((val_r_prefix + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |] 
  &&  [| ((Zlength (l_r)) = cap_r) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (cap_r <= 100000000) |] 
  &&  [| (n_pre > 0) |] 
  &&  [| (n_pre <= cap_a) |] 
  &&  [| (n_pre <= cap_b) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (((rp_pre + (i * sizeof(UINT) ) )) # UInt  |->_)
  **  (store_uint_array_missing_i_rec rp_pre i 0 (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
  **  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array bp_pre n_pre l_b_2 )
  **  (store_uint_array ap_pre n_pre l_a_2 )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_which_implies_wit_1 := 
forall (n_pre: Z) (ap_pre: Z) (val_a: Z) (cap_a: Z) ,
  (mpd_store_Z_compact ap_pre val_a n_pre cap_a )
|--
  EX (l_a: (@list Z)) ,
  [| (n_pre <= cap_a) |] 
  &&  [| ((Zlength (l_a)) = n_pre) |] 
  &&  [| (cap_a <= 100000000) |] 
  &&  [| (list_store_Z_compact l_a val_a ) |]
  &&  (store_uint_array ap_pre n_pre l_a )
  **  (store_undef_uint_array_rec ap_pre n_pre cap_a )
.

Definition mpn_add_n_which_implies_wit_2 := 
forall (n_pre: Z) (bp_pre: Z) (val_b: Z) (cap_b: Z) ,
  (mpd_store_Z_compact bp_pre val_b n_pre cap_b )
|--
  EX (l_b: (@list Z)) ,
  [| (n_pre <= cap_b) |] 
  &&  [| ((Zlength (l_b)) = n_pre) |] 
  &&  [| (cap_b <= 100000000) |] 
  &&  [| (list_store_Z_compact l_b val_b ) |]
  &&  (store_uint_array bp_pre n_pre l_b )
  **  (store_undef_uint_array_rec bp_pre n_pre cap_b )
.

Definition mpn_add_n_which_implies_wit_3 := 
forall (rp_pre: Z) (l_r: (@list Z)) (cap_r: Z) ,
  [| ((Zlength (l_r)) = cap_r) |]
  &&  (store_uint_array rp_pre cap_r l_r )
|--
  [| ((Zlength (l_r)) = cap_r) |]
  &&  (store_uint_array_rec rp_pre 0 cap_r l_r )
  **  (store_uint_array rp_pre 0 nil )
.

Definition mpn_add_n_which_implies_wit_4 := 
forall (n_pre: Z) (rp_pre: Z) (cap_r: Z) (l_r_suffix: (@list Z)) (l_r_prefix: (@list Z)) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array rp_pre i l_r_prefix )
  **  (store_uint_array_rec rp_pre i cap_r l_r_suffix )
|--
  EX (a: Z)  (l_r_suffix': (@list Z)) ,
  [| (l_r_suffix = (cons (a) (l_r_suffix'))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre <= cap_r) |]
  &&  (store_uint_array_rec rp_pre (i + 1 ) cap_r l_r_suffix' )
  **  (store_uint_array rp_pre (i + 1 ) (app (l_r_prefix) ((cons (a) (nil)))) )
.

(*----- Function mpz_clear -----*)

Definition mpz_clear_return_wit_1_1 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 = 0) |] 
  &&  [| (size_2 < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_2 (-n) (-size_2) cap_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_1_2 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 = 0) |] 
  &&  [| (size_2 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_2 n size_2 cap_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_1_3 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 <> 0) |] 
  &&  [| (size_2 >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_return_wit_1_4 := 
forall (r_pre: Z) (n: Z) (ptr_2: Z) (cap_2: Z) (size_2: Z) ,
  [| (cap_2 <> 0) |] 
  &&  [| (size_2 < 0) |] 
  &&  [| (n < 0) |]
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_partial_solve_wit_1 := 
forall (r_pre: Z) (n: Z) ,
  (store_Z r_pre n )
|--
  (store_Z r_pre n )
.

Definition mpz_clear_partial_solve_wit_2 := 
forall (r_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| (cap <> 0) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n size cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap <> 0) |] 
  &&  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n size cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_partial_solve_wit_3 := 
forall (r_pre: Z) (n: Z) (ptr: Z) (cap: Z) (size: Z) ,
  [| (cap <> 0) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-size) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap <> 0) |] 
  &&  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-size) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_clear_which_implies_wit_1 := 
forall (r_pre: Z) (n: Z) ,
  (store_Z r_pre n )
|--
  (EX (ptr: Z)  (cap: Z)  (size: Z) ,
  [| (size >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n size cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr))
  ||
  (EX (ptr: Z)  (cap: Z)  (size: Z) ,
  [| (size < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-size) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr))
.

(*----- Function mpz_realloc -----*)

Definition mpz_realloc_safety_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpz_realloc_safety_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition mpz_realloc_safety_wit_3 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (store_undef_uint_array retval_3 retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_safety_wit_4 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (store_undef_uint_array retval_3 retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_safety_wit_5 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact retval_3 (-n) (-old) retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_safety_wit_6 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact retval_3 n old retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition mpz_realloc_return_wit_1_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval <= retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact retval_3 n old retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_return_wit_1_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval <= retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact retval_3 (-n) (-old) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_return_wit_1_3 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval <= retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (store_undef_uint_array retval_3 retval_2 )
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_return_wit_1_4 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval <= retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (store_undef_uint_array retval_3 retval_2 )
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_return_wit_1_5 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (store_undef_uint_array retval_3 retval_2 )
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_return_wit_1_6 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (store_undef_uint_array retval_3 retval_2 )
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_return_wit_1_7 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact retval_3 (-n) (-old) retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_return_wit_1_8 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval_3: Z) (retval: Z) ,
  [| (retval > retval_2) |] 
  &&  [| (retval = (Zabs (old))) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact retval_3 n old retval_2 )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_3)
|--
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr_new (-n) (-old) c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
  ||
  (EX (ptr_new: Z)  (c: Z) ,
  [| (c >= size_pre) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr_new n old c )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> c)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_new))
.

Definition mpz_realloc_partial_solve_wit_1 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_2 := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) ,
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_3_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |]
.

Definition mpz_realloc_partial_solve_wit_3_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_3 := mpz_realloc_partial_solve_wit_3_pure -> mpz_realloc_partial_solve_wit_3_aux.

Definition mpz_realloc_partial_solve_wit_4_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |]
.

Definition mpz_realloc_partial_solve_wit_4_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (cap >= 0) |] 
  &&  [| (retval >= cap) |] 
  &&  [| ((Z.max (size_pre) (1)) >= cap) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_4 := mpz_realloc_partial_solve_wit_4_pure -> mpz_realloc_partial_solve_wit_4_aux.

Definition mpz_realloc_partial_solve_wit_5_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |]
.

Definition mpz_realloc_partial_solve_wit_5_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_5 := mpz_realloc_partial_solve_wit_5_pure -> mpz_realloc_partial_solve_wit_5_aux.

Definition mpz_realloc_partial_solve_wit_6_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  ((( &( "size" ) )) # Int  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |]
.

Definition mpz_realloc_partial_solve_wit_6_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
|--
  [| (retval >= 0) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_realloc_partial_solve_wit_6 := mpz_realloc_partial_solve_wit_6_pure -> mpz_realloc_partial_solve_wit_6_aux.

Definition mpz_realloc_partial_solve_wit_7_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (store_undef_uint_array retval retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |]
.

Definition mpz_realloc_partial_solve_wit_7_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (store_undef_uint_array retval_2 retval )
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (store_undef_uint_array retval_2 retval )
  **  (mpd_store_Z_compact ptr (-n) (-old) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_7 := mpz_realloc_partial_solve_wit_7_pure -> mpz_realloc_partial_solve_wit_7_aux.

Definition mpz_realloc_partial_solve_wit_8_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval_2: Z) (retval: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (store_undef_uint_array retval retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |]
.

Definition mpz_realloc_partial_solve_wit_8_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (ptr: Z) (retval: Z) (retval_2: Z) ,
  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (store_undef_uint_array retval_2 retval )
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |] 
  &&  [| (cap = 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (store_undef_uint_array retval_2 retval )
  **  (mpd_store_Z_compact ptr n old cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_8 := mpz_realloc_partial_solve_wit_8_pure -> mpz_realloc_partial_solve_wit_8_aux.

Definition mpz_realloc_partial_solve_wit_9_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact retval (-n) (-old) retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |]
.

Definition mpz_realloc_partial_solve_wit_9_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact retval_2 (-n) (-old) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (old <= INT_MAX) |] 
  &&  [| (INT_MIN < old) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old < 0) |] 
  &&  [| (n < 0) |]
  &&  (mpd_store_Z_compact retval_2 (-n) (-old) retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_9 := mpz_realloc_partial_solve_wit_9_pure -> mpz_realloc_partial_solve_wit_9_aux.

Definition mpz_realloc_partial_solve_wit_10_pure := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval_2: Z) (retval: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval_2 = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact retval n old retval_2 )
  **  ((( &( "size" ) )) # Int  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |]
.

Definition mpz_realloc_partial_solve_wit_10_aux := 
forall (size_pre: Z) (r_pre: Z) (n: Z) (cap: Z) (old: Z) (retval: Z) (retval_2: Z) ,
  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact retval_2 n old retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  [| (INT_MIN < old) |] 
  &&  [| (old <= INT_MAX) |] 
  &&  [| (cap <> 0) |] 
  &&  [| (retval = (Z.max (size_pre) (1))) |] 
  &&  [| (size_pre >= cap) |] 
  &&  [| (size_pre <= 100000000) |] 
  &&  [| (cap >= 0) |] 
  &&  [| (cap <= 100000000) |] 
  &&  [| (old >= 0) |] 
  &&  [| (n >= 0) |]
  &&  (mpd_store_Z_compact retval_2 n old retval )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> old)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> retval)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
.

Definition mpz_realloc_partial_solve_wit_10 := mpz_realloc_partial_solve_wit_10_pure -> mpz_realloc_partial_solve_wit_10_aux.

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
Axiom proof_of_mpn_cmp_safety_wit_1 : mpn_cmp_safety_wit_1.
Axiom proof_of_mpn_cmp_safety_wit_2 : mpn_cmp_safety_wit_2.
Axiom proof_of_mpn_cmp_safety_wit_3 : mpn_cmp_safety_wit_3.
Axiom proof_of_mpn_cmp_safety_wit_4 : mpn_cmp_safety_wit_4.
Axiom proof_of_mpn_cmp_safety_wit_5 : mpn_cmp_safety_wit_5.
Axiom proof_of_mpn_cmp_safety_wit_6 : mpn_cmp_safety_wit_6.
Axiom proof_of_mpn_cmp_safety_wit_7 : mpn_cmp_safety_wit_7.
Axiom proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Axiom proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Axiom proof_of_mpn_cmp_return_wit_1_1 : mpn_cmp_return_wit_1_1.
Axiom proof_of_mpn_cmp_return_wit_1_2 : mpn_cmp_return_wit_1_2.
Axiom proof_of_mpn_cmp_return_wit_2 : mpn_cmp_return_wit_2.
Axiom proof_of_mpn_cmp_partial_solve_wit_1 : mpn_cmp_partial_solve_wit_1.
Axiom proof_of_mpn_cmp_partial_solve_wit_2 : mpn_cmp_partial_solve_wit_2.
Axiom proof_of_mpn_cmp_partial_solve_wit_3 : mpn_cmp_partial_solve_wit_3.
Axiom proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_1 : mpn_cmp4_safety_wit_1.
Axiom proof_of_mpn_cmp4_safety_wit_2 : mpn_cmp4_safety_wit_2.
Axiom proof_of_mpn_cmp4_safety_wit_3 : mpn_cmp4_safety_wit_3.
Axiom proof_of_mpn_cmp4_return_wit_1_1 : mpn_cmp4_return_wit_1_1.
Axiom proof_of_mpn_cmp4_return_wit_1_2 : mpn_cmp4_return_wit_1_2.
Axiom proof_of_mpn_cmp4_return_wit_2_1 : mpn_cmp4_return_wit_2_1.
Axiom proof_of_mpn_cmp4_return_wit_2_2 : mpn_cmp4_return_wit_2_2.
Axiom proof_of_mpn_cmp4_return_wit_2_3 : mpn_cmp4_return_wit_2_3.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1_pure : mpn_cmp4_partial_solve_wit_1_pure.
Axiom proof_of_mpn_cmp4_partial_solve_wit_1 : mpn_cmp4_partial_solve_wit_1.
Axiom proof_of_mpn_cmp4_partial_solve_wit_2_pure : mpn_cmp4_partial_solve_wit_2_pure.
Axiom proof_of_mpn_cmp4_partial_solve_wit_2 : mpn_cmp4_partial_solve_wit_2.
Axiom proof_of_mpn_cmp4_which_implies_wit_1 : mpn_cmp4_which_implies_wit_1.
Axiom proof_of_mpn_normalized_size_safety_wit_1 : mpn_normalized_size_safety_wit_1.
Axiom proof_of_mpn_normalized_size_safety_wit_2 : mpn_normalized_size_safety_wit_2.
Axiom proof_of_mpn_normalized_size_safety_wit_3 : mpn_normalized_size_safety_wit_3.
Axiom proof_of_mpn_normalized_size_safety_wit_4 : mpn_normalized_size_safety_wit_4.
Axiom proof_of_mpn_normalized_size_safety_wit_5 : mpn_normalized_size_safety_wit_5.
Axiom proof_of_mpn_normalized_size_entail_wit_1 : mpn_normalized_size_entail_wit_1.
Axiom proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Axiom proof_of_mpn_normalized_size_return_wit_1_1 : mpn_normalized_size_return_wit_1_1.
Axiom proof_of_mpn_normalized_size_return_wit_1_2 : mpn_normalized_size_return_wit_1_2.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_1 : mpn_normalized_size_partial_solve_wit_1.
Axiom proof_of_mpn_normalized_size_partial_solve_wit_2 : mpn_normalized_size_partial_solve_wit_2.
Axiom proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_1 : mpn_add_1_safety_wit_1.
Axiom proof_of_mpn_add_1_safety_wit_2 : mpn_add_1_safety_wit_2.
Axiom proof_of_mpn_add_1_safety_wit_3 : mpn_add_1_safety_wit_3.
Axiom proof_of_mpn_add_1_entail_wit_1 : mpn_add_1_entail_wit_1.
Axiom proof_of_mpn_add_1_entail_wit_2 : mpn_add_1_entail_wit_2.
Axiom proof_of_mpn_add_1_entail_wit_3_1 : mpn_add_1_entail_wit_3_1.
Axiom proof_of_mpn_add_1_entail_wit_3_2 : mpn_add_1_entail_wit_3_2.
Axiom proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_1 : mpn_add_1_partial_solve_wit_1.
Axiom proof_of_mpn_add_1_partial_solve_wit_2_pure : mpn_add_1_partial_solve_wit_2_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_2 : mpn_add_1_partial_solve_wit_2.
Axiom proof_of_mpn_add_1_partial_solve_wit_3 : mpn_add_1_partial_solve_wit_3.
Axiom proof_of_mpn_add_1_partial_solve_wit_4_pure : mpn_add_1_partial_solve_wit_4_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_4 : mpn_add_1_partial_solve_wit_4.
Axiom proof_of_mpn_add_1_partial_solve_wit_5_pure : mpn_add_1_partial_solve_wit_5_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_5 : mpn_add_1_partial_solve_wit_5.
Axiom proof_of_mpn_add_1_partial_solve_wit_6 : mpn_add_1_partial_solve_wit_6.
Axiom proof_of_mpn_add_1_partial_solve_wit_7 : mpn_add_1_partial_solve_wit_7.
Axiom proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Axiom proof_of_mpn_add_1_which_implies_wit_2 : mpn_add_1_which_implies_wit_2.
Axiom proof_of_mpn_add_1_which_implies_wit_3 : mpn_add_1_which_implies_wit_3.
Axiom proof_of_mpn_add_n_safety_wit_1 : mpn_add_n_safety_wit_1.
Axiom proof_of_mpn_add_n_safety_wit_2 : mpn_add_n_safety_wit_2.
Axiom proof_of_mpn_add_n_safety_wit_3 : mpn_add_n_safety_wit_3.
Axiom proof_of_mpn_add_n_safety_wit_4 : mpn_add_n_safety_wit_4.
Axiom proof_of_mpn_add_n_safety_wit_5 : mpn_add_n_safety_wit_5.
Axiom proof_of_mpn_add_n_safety_wit_6 : mpn_add_n_safety_wit_6.
Axiom proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Axiom proof_of_mpn_add_n_entail_wit_2 : mpn_add_n_entail_wit_2.
Axiom proof_of_mpn_add_n_entail_wit_3_1 : mpn_add_n_entail_wit_3_1.
Axiom proof_of_mpn_add_n_entail_wit_3_2 : mpn_add_n_entail_wit_3_2.
Axiom proof_of_mpn_add_n_entail_wit_3_3 : mpn_add_n_entail_wit_3_3.
Axiom proof_of_mpn_add_n_entail_wit_3_4 : mpn_add_n_entail_wit_3_4.
Axiom proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_1 : mpn_add_n_partial_solve_wit_1.
Axiom proof_of_mpn_add_n_partial_solve_wit_2 : mpn_add_n_partial_solve_wit_2.
Axiom proof_of_mpn_add_n_partial_solve_wit_3_pure : mpn_add_n_partial_solve_wit_3_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_3 : mpn_add_n_partial_solve_wit_3.
Axiom proof_of_mpn_add_n_partial_solve_wit_4 : mpn_add_n_partial_solve_wit_4.
Axiom proof_of_mpn_add_n_partial_solve_wit_5 : mpn_add_n_partial_solve_wit_5.
Axiom proof_of_mpn_add_n_partial_solve_wit_6_pure : mpn_add_n_partial_solve_wit_6_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_6 : mpn_add_n_partial_solve_wit_6.
Axiom proof_of_mpn_add_n_partial_solve_wit_7_pure : mpn_add_n_partial_solve_wit_7_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_7 : mpn_add_n_partial_solve_wit_7.
Axiom proof_of_mpn_add_n_partial_solve_wit_8_pure : mpn_add_n_partial_solve_wit_8_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_8 : mpn_add_n_partial_solve_wit_8.
Axiom proof_of_mpn_add_n_partial_solve_wit_9_pure : mpn_add_n_partial_solve_wit_9_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_9 : mpn_add_n_partial_solve_wit_9.
Axiom proof_of_mpn_add_n_partial_solve_wit_10 : mpn_add_n_partial_solve_wit_10.
Axiom proof_of_mpn_add_n_partial_solve_wit_11 : mpn_add_n_partial_solve_wit_11.
Axiom proof_of_mpn_add_n_partial_solve_wit_12 : mpn_add_n_partial_solve_wit_12.
Axiom proof_of_mpn_add_n_partial_solve_wit_13 : mpn_add_n_partial_solve_wit_13.
Axiom proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Axiom proof_of_mpn_add_n_which_implies_wit_2 : mpn_add_n_which_implies_wit_2.
Axiom proof_of_mpn_add_n_which_implies_wit_3 : mpn_add_n_which_implies_wit_3.
Axiom proof_of_mpn_add_n_which_implies_wit_4 : mpn_add_n_which_implies_wit_4.
Axiom proof_of_mpz_clear_return_wit_1_1 : mpz_clear_return_wit_1_1.
Axiom proof_of_mpz_clear_return_wit_1_2 : mpz_clear_return_wit_1_2.
Axiom proof_of_mpz_clear_return_wit_1_3 : mpz_clear_return_wit_1_3.
Axiom proof_of_mpz_clear_return_wit_1_4 : mpz_clear_return_wit_1_4.
Axiom proof_of_mpz_clear_partial_solve_wit_1 : mpz_clear_partial_solve_wit_1.
Axiom proof_of_mpz_clear_partial_solve_wit_2 : mpz_clear_partial_solve_wit_2.
Axiom proof_of_mpz_clear_partial_solve_wit_3 : mpz_clear_partial_solve_wit_3.
Axiom proof_of_mpz_clear_which_implies_wit_1 : mpz_clear_which_implies_wit_1.
Axiom proof_of_mpz_realloc_safety_wit_1 : mpz_realloc_safety_wit_1.
Axiom proof_of_mpz_realloc_safety_wit_2 : mpz_realloc_safety_wit_2.
Axiom proof_of_mpz_realloc_safety_wit_3 : mpz_realloc_safety_wit_3.
Axiom proof_of_mpz_realloc_safety_wit_4 : mpz_realloc_safety_wit_4.
Axiom proof_of_mpz_realloc_safety_wit_5 : mpz_realloc_safety_wit_5.
Axiom proof_of_mpz_realloc_safety_wit_6 : mpz_realloc_safety_wit_6.
Axiom proof_of_mpz_realloc_return_wit_1_1 : mpz_realloc_return_wit_1_1.
Axiom proof_of_mpz_realloc_return_wit_1_2 : mpz_realloc_return_wit_1_2.
Axiom proof_of_mpz_realloc_return_wit_1_3 : mpz_realloc_return_wit_1_3.
Axiom proof_of_mpz_realloc_return_wit_1_4 : mpz_realloc_return_wit_1_4.
Axiom proof_of_mpz_realloc_return_wit_1_5 : mpz_realloc_return_wit_1_5.
Axiom proof_of_mpz_realloc_return_wit_1_6 : mpz_realloc_return_wit_1_6.
Axiom proof_of_mpz_realloc_return_wit_1_7 : mpz_realloc_return_wit_1_7.
Axiom proof_of_mpz_realloc_return_wit_1_8 : mpz_realloc_return_wit_1_8.
Axiom proof_of_mpz_realloc_partial_solve_wit_1 : mpz_realloc_partial_solve_wit_1.
Axiom proof_of_mpz_realloc_partial_solve_wit_2 : mpz_realloc_partial_solve_wit_2.
Axiom proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_3 : mpz_realloc_partial_solve_wit_3.
Axiom proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_4 : mpz_realloc_partial_solve_wit_4.
Axiom proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_5 : mpz_realloc_partial_solve_wit_5.
Axiom proof_of_mpz_realloc_partial_solve_wit_6_pure : mpz_realloc_partial_solve_wit_6_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_6 : mpz_realloc_partial_solve_wit_6.
Axiom proof_of_mpz_realloc_partial_solve_wit_7_pure : mpz_realloc_partial_solve_wit_7_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_7 : mpz_realloc_partial_solve_wit_7.
Axiom proof_of_mpz_realloc_partial_solve_wit_8_pure : mpz_realloc_partial_solve_wit_8_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_8 : mpz_realloc_partial_solve_wit_8.
Axiom proof_of_mpz_realloc_partial_solve_wit_9_pure : mpz_realloc_partial_solve_wit_9_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_9 : mpz_realloc_partial_solve_wit_9.
Axiom proof_of_mpz_realloc_partial_solve_wit_10_pure : mpz_realloc_partial_solve_wit_10_pure.
Axiom proof_of_mpz_realloc_partial_solve_wit_10 : mpz_realloc_partial_solve_wit_10.

End VC_Correct.
