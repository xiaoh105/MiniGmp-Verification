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

Lemma store_uarray_rec_equals_store_uarray: forall x lo hi l,
  lo < hi ->
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
      
End Aux.