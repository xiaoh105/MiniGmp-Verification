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
Require Import GmpLib.GmpAux.
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
Notation "'LENGTH_MAX'" := (100000000).

Module Internal.

Definition mpd_store_list (ptr: addr) (data: list Z) (cap: Z): Assertion :=
  [| Zlength data <= cap |] && [| cap <= LENGTH_MAX |] && 
  store_uint_array ptr (Zlength data) data **
  store_undef_uint_array_rec ptr (Zlength data) cap.

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
    [| list_store_Z data n |] && [| size = Zlength data |] && mpd_store_list ptr data cap.

Definition list_store_Z_compact (data: list Z) (n: Z): Prop :=
  list_to_Z data = n /\ last data 1 >= 1 /\ list_within_bound data.

Definition mpd_store_Z_compact (ptr: addr) (n size cap: Z): Assertion :=
  EX data,
    [| list_store_Z_compact data n |] && [| size = Zlength data |] && mpd_store_list ptr data cap.

Lemma list_store_Z_normal_to_compact: forall (data: list Z) (n: Z),
  list_store_Z data n -> 
  last data 1 >= 1 ->
  list_store_Z_compact data n.
Proof.
  unfold list_store_Z_compact, list_store_Z.
  intros.
  tauto.
Qed.

Lemma list_store_Z_compact_to_normal: forall data n,
  list_store_Z_compact data n ->
  list_store_Z data n.
Proof.
  intros.
  unfold list_store_Z_compact in H.
  unfold list_store_Z.
  tauto.
Qed.

Lemma list_store_Z_injection: forall l1 l2 n1 n2,
  list_store_Z l1 n1 ->
  list_store_Z l2 n2 ->
  l1 = l2 -> n1 = n2.
Proof.
  intros.
  unfold list_store_Z in *.
  destruct H, H0.
  rewrite <-H, <-H0.
  rewrite <-H1.
  reflexivity.
Qed.

Lemma list_store_Z_reverse_injection: forall l1 l2 n1 n2,
  list_store_Z l1 n1 ->
  list_store_Z l2 n2 ->
  n1 = n2 -> l1 = l2.
Proof. Admitted.

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

Lemma list_within_bound_Znth: forall (l: list Z) (i: Z),
  0 <= i < Zlength l ->
  list_within_bound l ->
  0 <= Znth i l 0 < UINT_MOD.
Proof.
  intros.
  revert i H.
  induction l; intros.
  + rewrite Zlength_nil in H.
    lia.
  + assert (i = 0 \/ i > 0). { lia. }
    destruct H1.
    - rewrite H1.
      rewrite (Znth0_cons a l 0).
      simpl in H0.
      lia.
    - rewrite Znth_cons; try lia.
      simpl in H0; destruct H0.
      rewrite Zlength_cons in H; unfold Z.succ in H.
      specialize (IHl H2 (i - 1) ltac:(lia)).
      lia.
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

Lemma list_store_Z_list_append: forall (l: list Z) (i: Z) (val_prefix: Z) (val_full: Z),
  0 <= i < Zlength l ->
  list_store_Z l val_full ->
  list_store_Z (sublist 0 i l) val_prefix ->
  list_store_Z (sublist 0 (i+1) l) (val_prefix + Znth i l 0 * UINT_MOD ^ i).
Proof.
  intros.
  assert ((sublist 0 (i + 1) l) = ((sublist 0 i l) ++ ((Znth i l 0) :: nil)))%list. {
    pose proof (sublist_split 0 (i+1) i l).
    pose proof (sublist_single i l 0).
    rewrite <-H3; try rewrite <- Zlength_correct.
    apply H2; try rewrite <- Zlength_correct.
    lia. lia. lia.
  }
  rewrite H2.
  pose proof (list_store_Z_concat (sublist 0 i l) (Znth i l 0 :: nil) (val_prefix) (Znth i l 0)).
  assert (Zlength (sublist 0 i l) = i). {
    rewrite Zlength_sublist0.
    lia.
    lia.
  }
  rewrite H4 in H3.
  apply H3.
  tauto.
  unfold list_store_Z.
  simpl.
  split.
  reflexivity.
  split; try tauto.
  apply list_within_bound_Znth.
  lia.
  unfold list_store_Z in H0.
  tauto.
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

Lemma list_store_Z_compact_bound: forall (l1: list Z) (n: Z),
  list_store_Z_compact l1 n ->
  UINT_MOD ^ ((Zlength l1) - 1) <= n < UINT_MOD ^ (Zlength l1).
Proof.
  intros.
  destruct l1.
  + rewrite Zlength_nil.
    simpl.
    unfold list_store_Z_compact; destruct H.
    simpl in H.
    lia.
  + remember (z :: l1) as l eqn: Hl.
    unfold list_store_Z_compact in H.
    destruct H, H0.
    assert (list_store_Z l n). {
      unfold list_store_Z.
      tauto.
    }
    clear H1 H.
    split.
    - pose proof (@nil_cons Z z l1); rewrite <-Hl in H.
      pose proof (@app_removelast_last Z l 1 ltac:(auto)).
      clear H.
      rewrite H1 in H2.
      apply list_store_Z_split in H2; destruct H2.
      remember (Zlength (removelast l)) as len_lo eqn:Hlen_lo.
      remember (n mod UINT_MOD ^ len_lo) as n_lo eqn:Hnlo.
      remember (n / UINT_MOD ^ len_lo) as n_hi eqn:Hnhi.
      assert (n = n_lo + n_hi * UINT_MOD ^ len_lo). {
        pose proof (Z_div_mod_eq_full n (UINT_MOD ^ len_lo)).
        lia.
      }
      unfold list_store_Z in H2; destruct H2.
      simpl in H2.
      apply list_store_Z_bound in H.
      pose proof (@nil_cons Z z l1); rewrite <-Hl in H5.
      pose proof (Aux.Zlength_removelast l ltac:(auto)).
      clear H5.
      rewrite H6 in *.
      rewrite H2 in H0.
      rewrite Hlen_lo in *.
      nia.
    - apply list_store_Z_bound in H2.
      lia.
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

Lemma list_store_Z_cmp: forall l1 l2 n1 n2 i,
  0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
  list_store_Z l1 n1 ->
  list_store_Z l2 n2 ->
  sublist (i + 1) (Zlength l1) l1 = sublist (i + 1) (Zlength l2) l2 ->
  Znth i l1 0 < Znth i l2 0 ->
  n1 < n2.
Proof.
  intros.
  assert (Zlength l1 = Z.of_nat (Datatypes.length l1)). { apply Zlength_correct. }
  pose proof (sublist_split 0 (Zlength l1) i l1 ltac:(lia) ltac:(lia)).
  assert (Zlength l2 = Z.of_nat (Datatypes.length l2)). { apply Zlength_correct. }
  pose proof (sublist_split 0 (Zlength l2) i l2 ltac:(lia) ltac:(lia)).
  clear H5 H7.
  rewrite (sublist_self l1 (Zlength l1) ltac:(lia)) in H6.
  rewrite (sublist_self l2 (Zlength l2) ltac:(lia)) in H8.
  rewrite H6 in H1.
  rewrite H8 in H2.
  apply list_store_Z_split in H1, H2.
  remember (Zlength l1) as n eqn:Hn.
  assert (Zlength l2 = n). { lia. }
  rewrite H5 in *.
  rewrite Zlength_sublist0 in H1, H2; try lia.
  destruct H1, H2.
  remember (n1 mod UINT_MOD ^ i) as n1_lo eqn:Hn1_lo.
  remember (n1 / UINT_MOD ^ i) as n1_hi eqn:Hn1_hi.
  remember (n2 mod UINT_MOD ^ i) as n2_lo eqn:Hn2_lo.
  remember (n2 / UINT_MOD ^ i) as n2_hi eqn:Hn2_hi.
  remember (sublist 0 i l1) as l1_lo eqn:Hl1_lo.
  remember (sublist i n l1) as l1_hi eqn:Hl1_hi.
  remember (sublist 0 i l2) as l2_lo eqn:Hl2_lo.
  remember (sublist i n l2) as l2_hi eqn:Hl2_hi.
  assert (n1_lo - n2_lo < UINT_MOD ^ i). {
    pose proof (list_store_Z_bound l1_lo n1_lo H1).
    pose proof (list_store_Z_bound l2_lo n2_lo H2).
    rewrite Hl1_lo, Zlength_sublist0 in H10; lia.
  }
  assert (n2_hi - n1_hi >= 1). {
    assert (Zlength l1_hi >= 1 /\ Zlength l2_hi >= 1). {
      pose proof (Zlength_sublist i n l1 ltac:(lia)).
      pose proof (Zlength_sublist i n l2 ltac:(lia)).
      rewrite <-Hl1_hi in H11.
      rewrite <-Hl2_hi in H12.
      lia.
    }
    destruct H11.
    destruct l1_hi, l2_hi; try rewrite Zlength_nil in *; try lia.
    unfold list_store_Z in H7, H9.
    destruct H7, H9.
    simpl in H7, H9.
    assert (forall a (l0 l: list Z), 
      a :: l0 = sublist i n l -> 
      Zlength l = n -> 
      l0 = sublist (i + 1) n l /\ a = Znth i l 0
      ). {
      intros.
      assert (n = Z.of_nat(Datatypes.length l)). { rewrite <-Zlength_correct. lia. }
      pose proof (sublist_split i n (i + 1) l ltac:(lia) ltac:(lia)).
      rewrite (sublist_single i l 0) in H18; try lia.
      rewrite <-H15 in H18.
      rewrite Aux.list_app_single_l in H18.
      injection H18; intros.
      rewrite H19, H20.
      split; reflexivity.
    }
    pose proof (H15 z0 l2_hi l2 Hl2_hi ltac:(lia)).
    specialize (H15 z l1_hi l1 Hl1_hi ltac:(lia)).
    destruct H15, H16.
    rewrite H15, H17 in H7.
    rewrite H16, H18 in H9.
    rewrite <-H3 in H9.
    lia.
  }
  pose proof (Zmod_eq_full n1 (UINT_MOD ^ i) ltac:(lia)).
  pose proof (Zmod_eq_full n2 (UINT_MOD ^ i) ltac:(lia)).
  rewrite <-Hn1_lo, <-Hn1_hi in H12.
  rewrite <-Hn2_lo, <-Hn2_hi in H13.
  assert (n2_hi * UINT_MOD ^ i - n1_hi * UINT_MOD ^ i >= UINT_MOD ^ i). {
    rewrite <-Z.mul_sub_distr_r.
    pose proof (Zmult_ge_compat_r (n2_hi - n1_hi) 1 (UINT_MOD ^ i) ltac:(lia) ltac:(lia)).
    rewrite Z.mul_1_l in H14.
    lia.
  }
  lia.
Qed.

Lemma list_store_Z_compact_cmp: forall l1 l2 n1 n2 i,
  0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
  list_store_Z_compact l1 n1 ->
  list_store_Z_compact l2 n2 ->
  sublist (i + 1) (Zlength l1) l1 = sublist (i + 1) (Zlength l2) l2 ->
  Znth i l1 0 < Znth i l2 0 ->
  n1 < n2.
Proof.
  intros.
  apply list_store_Z_compact_to_normal in H1, H2.
  apply (list_store_Z_cmp l1 l2 n1 n2 i); tauto.
Qed.

Lemma list_store_Z_cmp_length: forall l1 l2 n1 n2,
  Zlength l1 < Zlength l2 ->
  list_store_Z_compact l1 n1 ->
  list_store_Z_compact l2 n2 ->
  n1 < n2.
Proof.
  intros.
  unfold list_store_Z_compact in *.
  destruct H0, H1, H2, H3.
  assert (list_store_Z l1 n1 /\ list_store_Z l2 n2). {
    unfold list_store_Z.
    tauto.
  }
  clear H0 H1 H4 H5.
  destruct H6.
  assert (l2 <> []). {
    pose proof (Zlength_nonneg l1).
    assert (Zlength l2 >= 1). { lia. }
    destruct l2.
    + rewrite Zlength_nil in H5.
      lia.
    + pose proof (@nil_cons Z z l2).
      auto.
  }
  pose proof (list_store_Z_bound l2 n2 H1) as Hn2.
  pose proof (@app_removelast_last Z l2 1 H4).
  rewrite H5 in H1.
  apply list_store_Z_split in H1; destruct H1.
  rewrite (Aux.Zlength_removelast l2) in H1, H6; try auto.
  remember (Zlength l2 - 1) as n eqn:Hn.
  unfold list_store_Z in H6; destruct H6.
  simpl in H6.
  assert (n2 >= UINT_MOD ^ n). {
    assert (n2 / UINT_MOD ^ n >= 1). { lia. }
    pose proof (Zmult_ge_compat_r (n2 / UINT_MOD ^ n) 1 (UINT_MOD ^ n) ltac:(lia) ltac:(lia)).
    rewrite Z.mul_1_l in H9.
    assert (n2 >= n2 / UINT_MOD ^ n * UINT_MOD ^ n). {
      assert (n >= 0). { 
        destruct l2.
        + contradiction.
        + rewrite Zlength_cons in Hn; unfold Z.succ in Hn.
          pose proof (Zlength_nonneg l2).
          lia.
      }
      pose proof (Zmod_eq n2 (UINT_MOD ^ n) ltac:(lia)).
      assert (n2 mod UINT_MOD ^ n >= 0). {
        pose proof (Z.mod_bound_pos n2 (UINT_MOD ^ n) ltac:(lia) ltac:(lia)).
        lia.
      }
      lia.
    }
    lia.
  }
  assert (Zlength l1 <= n). { lia. }
  pose proof (list_store_Z_bound l1 n1 H0).
  assert (UINT_MOD ^ n >= UINT_MOD ^ (Zlength l1)). {
    assert (Zlength l1 = n \/ Zlength l1 < n). { lia. }
    destruct H11.
    + rewrite H11.
      lia.
    + assert (n >= 0). { 
        destruct l2.
        + contradiction.
        + rewrite Zlength_cons in Hn; unfold Z.succ in Hn.
          pose proof (Zlength_nonneg l2).
          lia.
      }
      pose proof (Z.pow_lt_mono_r_iff UINT_MOD (Zlength l1) n ltac:(lia) ltac:(lia)).
      destruct H13 as [H13 _].
      specialize (H13 H11).
      lia.
  }
  lia.
Qed.

End Internal.

Record bigint_ent: Type := {
    cap: Z;
    data: list Z;
    sign: Prop;
}.

Definition store_Z (x: addr) (n: Z): Assertion :=
  EX (ptr: addr) (cap size: Z),
    (([| size < 0 |] && [| n < 0 |] && Internal.mpd_store_Z_compact ptr (-n) (-size) cap) ||
      ([| size >= 0 |] && [| n >= 0 |] && Internal.mpd_store_Z_compact ptr n size cap)) **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.