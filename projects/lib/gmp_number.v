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
      
End Aux.

Module Internal.

Definition mpd_store_list (ptr: addr) (data: list Z) (cap: Z): Assertion :=
  [| Zlength data <= cap |] &&
  store_uint_array ptr (Zlength data) data &&
  store_undef_uint_array_rec ptr ((Zlength data) + 1) cap.

Fixpoint list_store_Z (data: list Z) (n: Z): Assertion :=
  match data with
    | nil => [| n = 0 |]
    | a :: l0 => [| (n mod UINT_MOD) = a |] && list_store_Z l0 (n / UINT_MOD)
  end.

Definition mpd_store_Z (ptr: addr) (n: Z) (size: Z) (cap: Z): Assertion :=
  EX data,
    mpd_store_list ptr data cap && list_store_Z data n && [| size = Zlength data |].

Fixpoint list_store_Z_pref (data: list Z) (n: Z) (len: nat): Assertion :=
  match len with
    | O => [| n = 0 |]
    | S len' => 
      EX a l0,
        [| data = a :: l0 |] && [| (n mod UINT_MOD) = a |] && list_store_Z_pref l0 (n / UINT_MOD) len'
  end.

Definition mpd_store_Z_pref (ptr: addr) (n: Z) (size: Z) (cap: Z) (len: nat): Assertion :=
  EX data,
    mpd_store_list ptr data cap && list_store_Z_pref data n len && [| size = Zlength data |].

Lemma list_store_Z_split: forall (data: list Z) (n: Z) (len: nat),
  n >= 0 ->
  Z.of_nat len < Zlength data ->
  list_store_Z data n |--
    list_store_Z_pref data (n mod (UINT_MOD ^ Z.of_nat len)) len.
Proof.
  intros.
  revert n H data H0.
  induction len.
  + intros.
    simpl.
    entailer!.
    apply Z.mod_1_r.
  + intros.
    assert (Zlength data >= 1); [ lia | ].
    destruct data; [ unfold Zlength, Zlength_aux in H1; lia | ].
    simpl.
    Exists z data.
    entailer!.
    sep_apply IHlen; try tauto.
    - pose proof (Aux.Zdiv_mod_pow n UINT_MOD (Z.of_nat len) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite H5.
      pose proof (Aux.Z_of_nat_succ len).
      rewrite <-H6.
      reflexivity.
    - pose proof (Aux.Z_of_nat_succ len).
      pose proof (Zlength_cons z data).
      lia.
    - pose proof (Z.div_pos n UINT_MOD ltac:(lia) ltac:(lia)).
      lia.
    - rewrite <-H2.
      pose proof (Znumtheory.Zmod_div_mod UINT_MOD (Z.pow_pos UINT_MOD (Pos.of_succ_nat len)) n ltac:(lia) ltac:(lia)).
      rewrite H3; try tauto.
      unfold Z.divide.
      destruct len.
      * exists 1.
        simpl.
        lia.
      * exists (Z.pow_pos UINT_MOD (Pos.of_succ_nat len)).
        assert (Pos.of_succ_nat (S len) = Pos.add (Pos.of_succ_nat len) xH). { lia. }
        rewrite H4.
        apply Zpower_pos_is_exp.
Qed.

Lemma list_store_Z_pref_full: forall (data: list Z) (n: Z),
  list_store_Z_pref data n (Z.to_nat (Zlength data)) --||-- list_store_Z data n.
Proof.
  intros.
  revert n.
  induction data.
  + intros.
    simpl.
    split; entailer!.
  + intros.
    pose proof (Zlength_cons a data).
    rewrite H.
    pose proof (Z2Nat.inj_succ (Zlength data) (Zlength_nonneg data)).
    rewrite H0.
    simpl.
    split.
    - Intros a0 l0.
      injection H1; intros.
      subst.
      specialize (IHdata (n / UINT_MOD)).
      destruct IHdata.
      sep_apply H2.
      entailer!.
    - Exists a data.
      entailer!.
      specialize (IHdata (n / UINT_MOD)).
      destruct IHdata.
      sep_apply H3.
      entailer!.
Qed.

Lemma list_store_Z_pref_extend_data: forall (data: list Z) (a: Z) (n: Z) (len: nat),
  list_store_Z_pref data n len |--
    list_store_Z_pref (data ++ (a :: nil)) n len.
Proof.
  intros.
  revert data n.
  induction len.
  + intros.
    simpl.
    entailer!.
  + intros.
    simpl.
    Intros a0 l0.
    Exists a0 (app l0 (cons a nil)).
    entailer!.
    subst.
    reflexivity.
Qed.

Search list.

Lemma list_store_Z_pref_extend: forall (data: list Z) (a: Z) (n: Z) (len: nat),
  n >= 0 ->
  Zlength data = Z.of_nat len ->
  list_store_Z_pref data (n mod (UINT_MOD ^ Z.of_nat len)) len && 
    [| a = (n / (UINT_MOD ^ Z.of_nat len)) mod UINT_MOD |] |--
    list_store_Z_pref (data ++ (cons a nil)) (n mod (UINT_MOD ^ (Z.of_nat len + 1))) (S len).
Proof.
  intros.
  entailer!.
  simpl.
  revert a data H0 H1.
  induction len.
  + intros.
    Exists a nil.
    simpl.
    entailer!.
    - intros.
      unfold Z.pow_pos, Pos.iter; simpl.
      apply Z.mod_div; lia.
    - unfold Z.pow_pos, Pos.iter; simpl.
      simpl in H1; rewrite Z.div_1_r in H1.
      rewrite Z.mod_mod; lia.
    - pose proof (Zlength_nil_inv data H0).
      rewrite H2.
      reflexivity.
  + intros.
    simpl.
    Intros a0 l0.
    Exists a0 (app l0 [a]).
    assert (Zlength l0 = Z.of_nat len). {
      rewrite H2 in H0.
      rewrite Zlength_cons in H0.
      lia.
    }
    specialize (IHlen ((n / UINT_MOD ^ (Z.of_nat len)) mod UINT_MOD) l0 H4 ltac:(lia)).
    sep_apply IHlen.
    Admitted. (* Unfinished. *)

Lemma mpd_store_Z_split: forall (ptr: addr) (n: Z) (size: Z) (cap: Z) (len: nat),
  n >= 0 ->
  Z.of_nat len < size ->
    mpd_store_Z ptr n size cap |--
      mpd_store_Z_pref ptr (n mod (UINT_MOD ^ Z.of_nat len)) size cap len.
Proof.
  intros.
  unfold mpd_store_Z, mpd_store_Z_pref.
  Intros data.
  Exists data.
  unfold mpd_store_list.
  Intros.
  entailer!.
  sep_apply (list_store_Z_split data n len).
  + entailer!.
  + lia.
  + lia.
Qed.

Lemma mpd_store_Z_pref_full: forall (ptr: addr) (n: Z) (size: Z) (cap: Z),
  mpd_store_Z ptr n size cap --||-- mpd_store_Z_pref ptr n size cap (Z.to_nat size).
Proof.
  intros.
  unfold mpd_store_Z, mpd_store_Z_pref.
  pose proof list_store_Z_pref_full.
  split; Intros data; Exists data; entailer!; specialize (H data n); destruct H.
  + sep_apply H1.
    subst.
    entailer!.
  + subst.
    sep_apply H.
    entailer!.
Qed.

End Internal.

Record bigint_ent: Type := {
    cap: Z;
    data: list Z;
    sign: Prop;
}.

Definition store_bigint_ent (x: addr) (n: bigint_ent): Assertion :=
    EX size, 
      &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size &&
      ([| size < 0 |] && [| sign n |] && [| size = -Zlength (data n) |] ||
        [| size >= 0 |] && [| ~(sign n) |] && [| size = Zlength (data n) |]) **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap n **
    EX p, 
      &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> p **
    Internal.mpd_store_list p (data n) (cap n).

Definition bigint_ent_store_Z (n: bigint_ent) (x: Z): Assertion :=
  [| sign n |] && Internal.list_store_Z (data n) (-x) ||
    [| ~(sign n) |] && Internal.list_store_Z (data n) x.

Definition store_Z (x: addr) (n: Z): Assertion :=
  EX ent,
    store_bigint_ent x ent && bigint_ent_store_Z ent n.