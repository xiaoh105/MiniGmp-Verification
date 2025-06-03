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

Notation "'UINT_MOD'" := (4294967296).

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
      
End Aux.

Module Internal.

Definition mpd_store_list (ptr: addr) (data: list Z) (cap: Z): Assertion :=
  [| Zlength data <= cap |] &&
  store_uint_array ptr (Zlength data) data &&
  store_undef_uint_array_rec ptr ((Zlength data) + 1) cap.

Fixpoint list_to_Z (data: list Z): Z :=
  match data with
    | nil => 0
    | a :: l0 => (list_to_Z l0) * UINT_MOD + a
  end.

Fixpoint list_within_bound (data: list Z): Prop :=
  match data with
   | nil => True
   | a :: l0 => 0 <= a < UINT_MOD /\ (list_within_bound l0)
  end.

Definition list_store_Z (data: list Z) (n: Z): Prop := 
  list_to_Z data = n /\ list_within_bound data.

Definition mpd_store_Z (ptr: addr) (n: Z) (size: Z) (cap: Z): Assertion :=
  EX data,
    mpd_store_list ptr data cap && [| list_store_Z data n|] && [| size = Zlength data |].

Lemma __list_within_bound_concat_r: forall (l1: list Z) (a: Z),
  list_within_bound l1 ->
  0 <= a < UINT_MOD ->
  list_within_bound (l1 ++ [a]).
Proof.
  intros.
  induction l1.
  + rewrite app_nil_l.
    simpl.
    lia.
  + simpl in *; repeat split; try tauto.
Qed.

Lemma list_within_bound_concat: forall (l1 l2: list Z),
  list_within_bound l1 ->
  list_within_bound l2 ->
  list_within_bound (l1 ++ l2).
Proof.
  intros.
  revert l1 H.
  induction l2.
  + intros.
    rewrite app_nil_r.
    tauto.
  + intros.
    simpl in H0.
    destruct H0.
    rewrite Aux.list_app_cons.
    pose proof (__list_within_bound_concat_r l1 a H H0).
    specialize (IHl2 H1 (app l1 [a]) H2).
    tauto.
Qed.

Lemma __list_within_bound_split_r: forall (l1: list Z) (a: Z),
  list_within_bound (l1 ++ [a]) ->
  list_within_bound l1 /\ 0 <= a < UINT_MOD.
Proof.
  intros.
  induction l1.
  + rewrite app_nil_l in H.
    simpl in *.
    tauto.
  + simpl in *.
    destruct H.
    specialize (IHl1 H0).
    tauto.
Qed.

Lemma list_within_bound_split: forall (l1 l2: list Z),
  list_within_bound (l1 ++ l2) ->
  list_within_bound l1 /\ list_within_bound l2.
Proof.
  intros.
  revert l1 H.
  induction l2.
  + intros.
    simpl.
    rewrite app_nil_r in H.
    tauto.
  + intros.
    simpl.
    rewrite Aux.list_app_cons in H.
    specialize (IHl2 (app l1 [a]) H).
    destruct IHl2.
    apply __list_within_bound_split_r in H0.
    tauto.
Qed.

Lemma __list_store_Z_concat_r: forall (l1: list Z) (n1 a: Z),
  list_store_Z l1 n1 ->
  0 <= a < UINT_MOD ->
  list_store_Z (l1 ++ [a]) (a * (UINT_MOD ^ (Zlength l1)) + n1).
Proof.
  induction l1; intros.
  + rewrite app_nil_l.
    unfold Zlength, Zlength_aux.
    rewrite Z.pow_0_r.
    unfold list_store_Z in H; destruct H.
    simpl in H.
    subst.
    simpl.
    unfold list_store_Z; simpl.
    lia.
  + unfold list_store_Z in H; destruct H.
    simpl in H.
    simpl in H1.
    assert (list_store_Z l1 ((n1 - a) / UINT_MOD)). { 
       unfold list_store_Z; split; try simpl; try tauto.
       apply Z.div_unique_exact; lia.
    }
    specialize (IHl1 ((n1 - a) / UINT_MOD) a0 H2 ltac:(lia)).
    unfold list_store_Z; split.
    - simpl.
      unfold list_store_Z in IHl1; destruct IHl1.
      rewrite Zlength_cons; unfold Z.succ.
      rewrite H3.
      assert ((n1 - a) / UINT_MOD * UINT_MOD = n1 - a). { 
        rewrite <-(Z.div_unique_exact (n1 - a) UINT_MOD (list_to_Z l1)); lia.
      }
      rewrite Z.mul_add_distr_r.
      rewrite H5.
      rewrite Aux.Zpow_add_1; try lia.
      pose proof (Zlength_nonneg l1).
      lia.
    - apply list_within_bound_concat; try simpl; try lia; try tauto.
Qed.

Lemma list_store_Z_concat: forall (l1 l2: list Z) (n1 n2: Z),
  list_store_Z l1 n1 ->
  list_store_Z l2 n2 ->
  list_store_Z (l1 ++ l2) (n1 + n2 * (UINT_MOD ^ (Zlength l1))).
Proof.
  unfold list_store_Z.
  intros.
  split; [ | apply list_within_bound_concat; tauto].
  revert n1 l1 n2 H H0.
  induction l2.
  + intros.
    simpl in *.
    subst.
    rewrite app_nil_r.
    nia.
  + intros.
    destruct H0.
    destruct H.
    simpl in H0.
    rewrite Aux.list_app_cons.
    specialize (IHl2 (n1 + a * UINT_MOD ^ (Zlength l1)) (app l1 [a]) ((n2 - a) / UINT_MOD)).
    rewrite IHl2.
    - rewrite Zlength_app; rewrite Zlength_cons; simpl.
      assert ((n2 - a) / UINT_MOD * UINT_MOD = n2 - a). {
        rewrite <-(Z.div_unique_exact (n2 - a) UINT_MOD (list_to_Z l2)); try lia.
      }
      rewrite Aux.Zpow_add_1; try lia.
      pose proof (Zlength_nonneg l1); lia.
    - pose proof (__list_store_Z_concat_r l1 n1 a).
      assert (list_store_Z l1 n1). { unfold list_store_Z; tauto. }
      simpl in H1.
      specialize (H3 H4 ltac:(lia)).
      unfold list_store_Z in H3.
      destruct H3.
      split; [ lia | tauto].
    - simpl in H1.
      split; [ | tauto].
      apply Z.div_unique_exact; lia.
Qed.

Lemma list_store_Z_bound: forall (l1: list Z) (n: Z),
  list_store_Z l1 n -> 0 <= n < UINT_MOD ^ (Zlength l1).
Proof.
  induction l1; intros.
  + rewrite Zlength_nil; rewrite Z.pow_0_r.
    unfold list_store_Z in H; destruct H; simpl in *.
    lia.
  + rewrite Zlength_cons; unfold Z.succ.
    unfold list_store_Z in *; destruct H; simpl in *.
    assert (list_to_Z l1 = (n - a) / UINT_MOD /\ list_within_bound l1). {
      rewrite (Z.div_unique_exact (n - a) UINT_MOD (list_to_Z l1)); try lia; try tauto.
    }
    specialize (IHl1 ((n - a) / UINT_MOD) H1).
    rewrite Aux.Zpow_add_1; try lia.
    pose proof (Zlength_nonneg l1); lia.
Qed.

Lemma list_store_Z_split: forall (l1 l2: list Z) (n: Z),
  list_store_Z (l1 ++ l2) n ->
  list_store_Z l1 (n mod UINT_MOD ^ (Zlength l1)) /\
    list_store_Z l2 (n / UINT_MOD ^ (Zlength l1)).
Proof.
  intros.
  revert n H.
  induction l1; split.
  + intros.
    rewrite app_nil_l in H.
    rewrite Zlength_nil; rewrite Z.pow_0_r; rewrite Z.mod_1_r.
    unfold list_store_Z; simpl; lia.
  + rewrite app_nil_l in H.
    unfold list_store_Z; simpl.
    rewrite Z.div_1_r.
    tauto.
  + rewrite Zlength_cons; unfold Z.succ.
    unfold list_store_Z in H; simpl in H; destruct H.
    unfold list_store_Z in IHl1.
    assert (list_to_Z (l1 ++ l2) = (n - a) / UINT_MOD /\ list_within_bound (l1 ++ l2)). {
      rewrite (Z.div_unique_exact (n - a) UINT_MOD (list_to_Z (app l1 l2))); try lia; try tauto.
    }
    specialize (IHl1 ((n - a) / UINT_MOD) H1).
    unfold list_store_Z; simpl; split.
    - destruct IHl1; destruct H2, H3.
      rewrite H2.
      destruct H1.
      rewrite <-H1, <-H.
      remember (list_to_Z (l1 ++ l2)) as n' eqn:Hn'.
      rewrite Zplus_mod.
      rewrite Aux.Zmul_mod_cancel; try lia.
      * assert (UINT_MOD ^ (Zlength l1 + 1) >= UINT_MOD). {
          pose proof (Zlength_nonneg l1).
          rewrite Aux.Zpow_add_1; try tauto; try lia.
        }
        rewrite (Z.mod_small a (UINT_MOD ^ (Zlength l1 + 1)) ltac:(lia)).
        assert (list_store_Z (l1 ++ l2) n'). { unfold list_store_Z; split; [ lia | tauto]. }
        pose proof (list_store_Z_bound (l1 ++ l2) n' H8).
        pose proof (Zlength_nonneg l1).
        pose proof (Z.mod_bound_pos n' (UINT_MOD ^ (Zlength l1)) ltac:(lia) ltac:(lia)).
        assert (UINT_MOD * (n' mod UINT_MOD ^ (Zlength l1)) + a < UINT_MOD ^ (Zlength l1 + 1)). {
          rewrite Aux.Zpow_add_1; lia.
        }
        rewrite (Z.mod_small (UINT_MOD * (n' mod UINT_MOD ^ (Zlength l1)) + a) (UINT_MOD ^ (Zlength l1 + 1)) ltac:(lia)).
        lia.
      * assert (list_store_Z (l1 ++ l2) n'). { unfold list_store_Z; split; [ lia | tauto]. }
        pose proof (list_store_Z_bound (l1 ++ l2) n' H7).
        lia.
      * pose proof (Zlength_nonneg l1); lia.
    - split; [ lia | tauto].
  + unfold list_store_Z in *.
    simpl in *.
    pose proof (list_within_bound_split l1 l2 ltac:(tauto)).
    split; [ | tauto].
    rewrite Zlength_cons; unfold Z.succ.
    destruct H as [H [H1 H2]].
    assert (list_to_Z (l1 ++ l2) = (n - a) / UINT_MOD /\ list_within_bound (l1 ++ l2)). { 
      rewrite (Z.div_unique_exact (n - a) UINT_MOD (list_to_Z (l1 ++ l2))); try lia; try tauto.
    }
    specialize (IHl1 ((n - a) / UINT_MOD) H3).
    destruct IHl1 as [[H4 H5] [H6 H7]].
    rewrite H6.
    rewrite Aux.Zpow_add_1; try lia.
    - rewrite Z.mul_comm.
      rewrite <-Zdiv_Zdiv; try lia.
      destruct H3.
      assert ((n - a) / UINT_MOD = n / UINT_MOD). {
        apply (Zdiv_unique_full n UINT_MOD ((n - a) / UINT_MOD) a).
        + unfold Remainder; lia.
        + lia.
      }
      rewrite H9.
      reflexivity.
    - pose proof (Zlength_nonneg l1); lia.
Qed.

Lemma list_store_Z_nth: forall (l: list Z) (n: Z) (i: Z),
  0 <= i < Zlength l ->
  list_store_Z l n ->
  Znth i l 0 = (n / (UINT_MOD ^ i)) mod UINT_MOD.
Proof.
  intros.
  revert n i H H0.
  induction l; intros.
  + rewrite Zlength_nil in H.
    lia.
  + rewrite Zlength_cons in H; unfold Z.succ in H.
    assert (i = 0 \/ i > 0). { lia. }
    destruct H1.
    - pose proof (list_store_Z_split [a] l n).
      assert (a :: l = app [a] l). { auto. }
      rewrite <-H3 in H2; clear H3.
      specialize (H2 H0); destruct H2.
      unfold list_store_Z, list_to_Z in H2.
      unfold Zlength, Zlength_aux, Z.succ in H2.
      destruct H2.
      rewrite (Aux.Zpow_add_1 UINT_MOD 0) in H2; try lia.
      rewrite Z.pow_0_r, Z.mul_1_l in H2.
      simpl in H2.
      rewrite H1; rewrite Znth0_cons.
      rewrite Z.pow_0_r, Z.div_1_r.
      lia.
    - rewrite Znth_cons; [ | lia ].
      unfold list_store_Z in H0; destruct H0.
      simpl in H0.
      simpl in H2.
      unfold list_store_Z in IHl.
      assert (list_to_Z l = (n - a) / UINT_MOD /\ list_within_bound l). {
        rewrite (Z.div_unique_exact (n - a) UINT_MOD (list_to_Z l)); try lia; try tauto.
      }
      specialize (IHl ((n - a) / UINT_MOD) (i - 1) ltac:(lia) H3).
      rewrite IHl.
      assert ((n - a) / UINT_MOD / (UINT_MOD ^ (i - 1)) = (n - a) / (UINT_MOD ^ 1 * UINT_MOD ^ (i - 1))). {
        rewrite Zdiv_Zdiv; try lia.
        rewrite Z.pow_1_r.
        reflexivity.
      }
      rewrite H4.
      rewrite <-Z.pow_add_r; try lia.
      assert (n / UINT_MOD ^ i = (n - a) / UINT_MOD ^ i). {
        assert (i = 1 + (i - 1)). { lia. }
        rewrite H5.
        rewrite (Z.pow_add_r UINT_MOD 1 (i - 1)); try lia.
        repeat rewrite <-Zdiv_Zdiv; try lia.
        repeat rewrite Z.pow_1_r.
        rewrite <-(Zdiv_unique_full n UINT_MOD (list_to_Z l) a); try lia.
        + destruct H3.
          rewrite <-H3.
          reflexivity.
        + unfold Remainder; lia.
      }
      rewrite H5.
      assert (1 + (i - 1) = i). { lia. }
      rewrite H6.
      reflexivity.
Qed.

End Internal.

Record bigint_ent: Type := {
    cap: Z;
    data: list Z;
    sign: Prop;
}.

Definition store_bigint_ent (x: addr) (n: bigint_ent): Asrtion :=
    EX size, 
      &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size &&
      ([| size < 0 |] && [| sign n |] && [| size = -Zlength (data n) |] ||
        [| size >= 0 |] && [| ~(sign n) |] && [| size = Zlength (data n) |]) **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap n **
    EX p, 
      &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> p **
    Internal.mpd_store_list p (data n) (cap n).

Definition bigint_ent_store_Z (n: bigint_ent) (x: Z): Assertion :=
  [| sign n |] && [| Internal.list_store_Z (data n) (-x) |] ||
    [| ~(sign n) |] && [| Internal.list_store_Z (data n) x |].

Definition store_Z (x: addr) (n: Z): Assertion :=
  EX ent,
    store_bigint_ent x ent && bigint_ent_store_Z ent n.