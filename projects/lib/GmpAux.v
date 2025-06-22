Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import CommonAssertion Mem SeparationLogic IntLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
Import naive_C_Rules.
Local Open Scope sac.

Module Aux.

Lemma Z_mod_add_carry: forall (a b m: Z),
   m > 0 -> 0 <= a < m -> 0 <= b < m ->
   (a + b) mod m < b ->
   a + b = (a + b) mod m + m.
Proof.
  intros.
  pose proof (Z_div_mod_eq_full (a + b) m).
  assert (m <= a + b < 2 * m). {
    assert (a + b >= m \/ b <= a + b < m). { lia. }
    destruct H4.
    + lia.
    + assert ((a + b) mod m = a + b). { 
        apply Z.mod_small.
        lia.
      }
      lia.
  }
  assert ((a + b) / m = 1). {
    pose proof (Zdiv_le_lower_bound (a + b) m 1 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (a + b) m 2 ltac:(lia) ltac:(lia)).
    lia.
  }
  rewrite H5 in H3.
  nia.
Qed.

Lemma Z_mod_add_uncarry: forall (a b m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m ->
  (a + b) mod m >= b ->
  a + b = (a + b) mod m.
Proof.
  intros.
  assert (b <= a + b < m). {
    assert (a + b < m \/ m <= a + b < m + b). { lia. }
    destruct H3.
    + lia.
    + assert ((a + b) / m = 1). { 
        pose proof (Zdiv_le_lower_bound (a + b) m 1 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_lt_upper_bound (a + b) m 2 ltac:(lia) ltac:(lia)).
        lia.
      }
      pose proof (Z_div_mod_eq_full (a + b) m).
      rewrite H4 in H5.
      lia.
  }
  rewrite Z.mod_small; lia.
Qed.

Lemma Z_mod_3add_carry10: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m < c ->
  ((a + c) mod m + b) mod m >= b ->
  a + b + c = ((a + c) mod m + b) mod m + m.
Proof. Admitted.

Lemma Z_mod_3add_carry01: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m >= c ->
  ((a + c) mod m + b) mod m < b ->
  a + b + c = ((a + c) mod m + b) mod m + m.
Proof. Admitted.

Lemma Z_mod_3add_carry11: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m < c ->
  ((a + c) mod m + b) mod m < b ->
  a + b + c = ((a + c) mod m + b) mod m + m * 2.
Proof. Admitted.

Lemma Z_mod_3add_carry00: forall (a b c m: Z),
  m > 0 -> 0 <= a < m -> 0 <= b < m -> 0 <= c < m ->
  (a + c) mod m >= c ->
  ((a + c) mod m + b) mod m >= b ->
  a + b + c = ((a + c) mod m + b) mod m.
Proof. Admitted.

Lemma Z_of_nat_succ: forall (n: nat),
  Z.of_nat (S n) = Z.of_nat n + 1.
Proof. lia. Qed.

Lemma Zpow_add_1: forall (a b: Z),
  a >= 0 -> b >= 0 ->
  a ^ (b + 1) = a ^ b * a.
Proof.
  intros.
  rewrite (Z.pow_add_r a b 1); lia.
Qed.

Lemma Zmul_mod_cancel: forall (n a b: Z),
  n >= 0 -> a > 0 -> b >= 0 ->
  (n * a) mod (a ^ (b + 1)) = a * (n mod (a ^ b)).
Proof.
  intros.
  pose proof (Z_div_mod_eq_full n (a ^ b)).
  pose proof (Z.mod_bound_pos n (a ^ b) ltac:(lia) ltac:(nia)).
  remember (n / a ^ b) as q eqn:Hq.
  remember (n mod a ^ b) as rem eqn:Hrem.
  rewrite H2.
  rewrite Z.mul_add_distr_r.
  rewrite (Z.mul_comm (a ^ b) q); rewrite <-Z.mul_assoc.
  rewrite <-Zpow_add_1; try lia.
  assert (0 <= rem * a < a ^ (b + 1)). { 
    rewrite Zpow_add_1; try lia.
    nia.
  }
  rewrite <-(Zmod_unique_full (q * a ^ (b + 1) + rem * a) (a ^ (b + 1)) q (rem * a)).
  + lia.
  + unfold Remainder.
    lia.
  + lia.
Qed.

Lemma Zdiv_mod_pow: forall (n a b: Z),
  a > 0 -> b >= 0 -> n >= 0 ->
  (n / a) mod (a ^ b) = (n mod (a ^ (b + 1))) / a.
Proof.
  intros.
  pose proof (Z_div_mod_eq_full n (a ^ (b + 1))).
  remember (n / (a ^ (b + 1))) as q eqn:Hq.
  remember (n mod a ^ (b + 1)) as rem eqn:Hrem.
  assert (n / a = a ^ b * q + rem / a). {
    rewrite H2.
    rewrite Zpow_add_1; try lia.
    pose proof (Z_div_plus_full_l (a ^ b * q) a rem ltac:(lia)).
    assert (a ^ b * q * a + rem = a ^ b * a * q + rem). { lia. }
    rewrite H4 in H3.
    tauto.
  }
  apply Znumtheory.Zdivide_mod_minus.
  + pose proof (Z.mod_bound_pos n (a ^ (b + 1)) ltac:(lia) (Z.pow_pos_nonneg a (b + 1) ltac:(lia) ltac:(lia))).
    rewrite <-Hrem in H4.
    rewrite Zpow_add_1 in H4; try lia.
    pose proof (Z.div_lt_upper_bound rem a (a ^ b) ltac:(lia) ltac:(lia)).
    split; try lia.
    apply (Z_div_pos rem a ltac:(lia) ltac:(lia)).
  + unfold Z.divide.
    exists q.
    lia.
Qed.

Lemma list_app_cons: forall (l1 l2: list Z) (a: Z),
  app l1 (a :: l2) = app (app l1 (a :: nil)) l2.
Proof.
  intros.
  revert a l2.
  induction l1.
  + intros.
    rewrite app_nil_l.
    reflexivity.
  + intros.
    simpl in *.
    specialize (IHl1 a0 l2).
    rewrite IHl1.
    reflexivity.
Qed.

Lemma list_app_single_l: forall (l: list Z) (a: Z),
  ([a] ++ l)%list = a :: l.
Proof.
  intros.
  induction l.
  + simpl; reflexivity.
  + rewrite list_app_cons.
    simpl.
    reflexivity.
Qed.

Lemma list_last_cons: forall (a: Z) (l: list Z),
  l <> nil ->
  last (a :: l) 1 = last l 1.
Proof.
  intros.
  destruct l.
  + contradiction.
  + simpl.
    reflexivity.
Qed.

Lemma list_last_to_Znth: forall (l: list Z),
  l <> nil ->
  last l 1 = Znth ((Zlength l) - 1) l 0.
Proof.
  intros.
  induction l.
  + contradiction.
  + destruct l.
    - simpl.
      rewrite Znth0_cons.
      lia.
    - pose proof (@nil_cons Z z l).
      specialize (IHl ltac:(auto)); clear H0.
      rewrite list_last_cons; [ | pose proof (@nil_cons Z z l); auto ].
      rewrite IHl.
      pose proof (Zlength_cons a (z :: l)).
      unfold Z.succ in H0; rewrite H0; clear H0.
      pose proof (Zlength_nonneg l).
      pose proof (Zlength_cons z l); unfold Z.succ in H1.
      pose proof (Znth_cons (Zlength (z :: l)) a (z :: l) 0 ltac:(lia)).
      assert (Zlength (z :: l) + 1 - 1 = Zlength (z :: l)). { lia. }
      rewrite H3; clear H3.
      rewrite H2.
      reflexivity.
Qed.

Lemma Zlength_removelast: forall (l: list Z),
  l <> [] ->
  Zlength (removelast l) = Zlength l - 1.
Proof.
  intros.
  induction l.
  + contradiction.
  + destruct l.
    - simpl.
      rewrite Zlength_nil.
      lia.
    - pose proof (@nil_cons Z z l).
      specialize (IHl ltac:(auto)).
      assert (removelast (a :: z :: l) = a :: removelast(z :: l)). {
        simpl.
        reflexivity.
      }
      rewrite H1; clear H1.
      repeat rewrite Zlength_cons; unfold Z.succ.
      rewrite IHl.
      rewrite Zlength_cons; unfold Z.succ.
      lia.
Qed.

Lemma store_array_rec_false: forall x storeA lo hi (l: list Z),
  lo > hi ->
  store_array_rec storeA x lo hi l |-- [| False |].
Proof.
  intros.
  revert x storeA lo hi H.
  induction l; intros.
  + simpl.
    entailer!.
  + simpl.
    specialize (IHl x storeA (lo + 1) hi ltac:(lia)).
    sep_apply IHl.
    entailer!.
Qed.

Lemma store_array_rec_empty: forall x storeA lo (l: list Z),
  store_array_rec storeA x lo lo l |-- emp && [| l = nil |].
Proof.
  intros.
  destruct l.
  + simpl.
    entailer!.
  + simpl.
    sep_apply store_array_rec_false; [ entailer! | lia ].
Qed.

Lemma store_uint_array_rec_false: forall x lo hi l,
  lo > hi ->
  store_uint_array_rec x lo hi l |-- [| False |].
Proof.
  intros.
  unfold store_uint_array_rec.
  sep_apply store_array_rec_false; [ entailer! | lia ].
Qed.

Lemma store_uint_array_rec_empty: forall x lo l,
  store_uint_array_rec x lo lo l |-- emp && [| l = nil |].
Proof.
  induction l.
  + unfold store_uint_array_rec.
    simpl.
    entailer!.
  + pose proof (store_uint_array_rec_false x (lo + 1) lo l ltac:(lia)).
    unfold store_uint_array_rec in *.
    simpl in *.
    sep_apply H.
    entailer!.
Qed.

Lemma store_uint_array_empty: forall x l,
  store_uint_array x 0 l |-- emp && [| l = nil |].
Proof.
  intros x l.
  revert x.
  induction l; intros.
  + unfold store_uint_array, store_array.
    simpl.
    entailer!.
  + unfold store_uint_array, store_array.
    simpl.
    sep_apply store_array_rec_false; [ entailer! | lia ].
Qed.

Lemma uint_array_rec_to_uint_array: forall x lo hi l,
  lo <= hi ->
  store_uint_array_rec x lo hi l --||--
    store_uint_array (x + sizeof(UINT) * lo) (hi - lo) l.
Proof.
  intros.
  unfold store_uint_array_rec, store_uint_array, store_array.
  pose proof (store_array_rec_base x 0 lo hi l (sizeof(UINT))
    store_uint
    (fun (x: addr) (lo a: Z) => 
      (x + lo * sizeof(UINT)) # UInt |-> a) ltac:(reflexivity)).
  assert (x + sizeof(UINT) * lo = x + lo * sizeof(UINT)). { lia. }
  rewrite H1; clear H1.
  assert (0 + lo = lo). { lia. }
  repeat rewrite H1 in H0; clear H1.
  destruct H0.
  split.
  + sep_apply H0.
    entailer!.
  + sep_apply H1.
    entailer!.
Qed.

Lemma store_uint_array_single: forall x n a,
  store_uint_array_rec x n (n + 1) [a] --||--
    (x + n * sizeof(UINT)) # UInt |-> a.
Proof.
  intros.
  unfold store_uint_array_rec.
  simpl.
  split; entailer!.
Qed.

Lemma store_undef_uint_array_single: forall x n a,
  (x + n * sizeof(UINT)) # UInt |-> a |--
    store_undef_uint_array_rec x n (n + 1).
Proof.
  intros.
  unfold store_undef_uint_array_rec.
  assert (Z.to_nat (n + 1 - n) = S O). { lia. }
  rewrite H; clear H.
  simpl.
  entailer!.
  sep_apply store_uint_undef_store_uint.
  entailer!.
Qed.

Lemma store_uint_array_single_to_undef: forall x n a,
  store_uint_array_rec x n (n + 1) [a] |--
    store_undef_uint_array_rec x n (n + 1).
Proof.
  intros.
  pose proof (store_uint_array_single x n a).
  destruct H as [H _].
  sep_apply H.
  sep_apply store_undef_uint_array_single.
  entailer!.
Qed.

Lemma store_uint_array_divide_rec: forall x n l m,
  0 <= m <= n ->
  Zlength l = n ->
  store_uint_array x n l --||--
    store_uint_array x m (sublist 0 m l) **
    store_uint_array_rec x m n (sublist m n l).
Proof.
  intros.
  pose proof (store_uint_array_divide x n l m H H0).
  pose proof (uint_array_rec_to_uint_array x m n (sublist m n l) ltac:(lia)).
  destruct H2 .
  destruct H1.
  rewrite Z.mul_comm in H2, H3.
  rewrite H3 in H1.
  rewrite <-H2 in H4.
  clear H2 H3.
  split; tauto.
Qed.

Lemma store_undef_uint_array_rec_divide: forall x l mid r,
  0 <= l <= r ->
  l <= mid <= r ->
  store_undef_uint_array_rec x l r --||--
  store_undef_uint_array_rec x l mid ** store_undef_uint_array_rec x mid r.
Proof.
  intros.
  unfold store_undef_uint_array_rec.
  pose proof (store_undef_array_divide (x + l * sizeof(UINT)) (r - l) (mid - l) (sizeof(UINT))
    (fun x => x # UInt |->_)
    (fun x0 lo => (x0 + lo * sizeof(UINT)) # UInt |->_) ltac:(lia) ltac:(reflexivity)).
  unfold store_undef_array in H1.
  pose (fun (l: Z) (n: Z) (len: nat) => store_undef_array_rec_base x 0 l n len (sizeof(UINT))
    (fun x => x # UInt |->_)
    (fun x0 lo => (x0 + lo * sizeof(UINT)) # UInt |->_) ltac:(reflexivity)).
  rewrite <-(l0 l r (Z.to_nat (r - l))) in H1.
  rewrite <-(l0 l mid (Z.to_nat (mid - l))) in H1.
  assert (r - l - (mid - l) = r - mid). { lia. }
  rewrite H2 in H1; clear H2.
  rewrite <-Z.add_assoc, <-Z.mul_add_distr_r in H1.
  assert (l + (mid - l) = mid). { lia. }
  rewrite H2 in H1; clear H2.
  rewrite <-(l0 mid r (Z.to_nat (r - mid))) in H1.
  repeat rewrite Z.add_0_l in H1.
  clear l0.
  rewrite H1.
  split; entailer!.
Qed.

Lemma store_uint_array_rec_def2undef: forall x a b l,
  0 <= a <= b ->
  store_uint_array_rec x a b l |--
  store_undef_uint_array_rec x a b.
Proof.
  intros.
  revert x a b H.
  induction l; intros.
  + unfold store_uint_array_rec.
    simpl.
    entailer!.
    subst.
    unfold store_undef_uint_array_rec.
    assert (b - b = 0). { lia. }
    rewrite H0; clear H0.
    simpl.
    entailer!.
  + assert (a0 = b \/ a0 < b). { lia. }
    destruct H0.
    - unfold store_uint_array_rec.
      simpl.
      sep_apply store_array_rec_false; try lia.
      entailer!.
    - sep_apply store_uint_array_rec_cons; try lia.
      pose proof (store_undef_uint_array_rec_divide x a0 (a0 + 1) b ltac:(lia) ltac:(lia)).
      destruct H2 as [_ H2].
      rewrite <-H2; clear H2.
      specialize (IHl x (a0 + 1) b ltac:(lia)).
      sep_apply IHl; entailer!.
      assert ((x + a0 * sizeof ( UINT )) # UInt |-> a |-- 
                store_uint_array_rec x a0 (a0 + 1) [a]). {
        unfold store_uint_array_rec.
        simpl.
        entailer!.
      }
      sep_apply H2; clear H2.
      sep_apply store_uint_array_single_to_undef.
      entailer!.
Qed.

End Aux.