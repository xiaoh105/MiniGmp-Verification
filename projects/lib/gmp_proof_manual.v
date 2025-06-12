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
From GmpLib Require Import gmp_goal.
Require Import GmpLib.GmpNumber. Import Internal.
Require Import GmpLib.GmpAux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_gmp_abs_return_wit_1_1 : gmp_abs_return_wit_1_1.
Proof. pre_process. Qed.


Lemma proof_of_gmp_abs_return_wit_1_2 : gmp_abs_return_wit_1_2.
Proof. pre_process. Qed.

Lemma proof_of_gmp_max_return_wit_1_1 : gmp_max_return_wit_1_1.
Proof. 
  pre_process.
  entailer!.
  unfold Zmax.
  rewrite Z.max_r; lia.
Qed.

Lemma proof_of_gmp_max_return_wit_1_2 : gmp_max_return_wit_1_2.
Proof.
  pre_process.
  entailer!.
  unfold Zmax.
  rewrite Z.max_l; lia.
Qed.

Lemma proof_of_gmp_cmp_return_wit_1_2 : gmp_cmp_return_wit_1_2.
Proof.
  pre_process.
  repeat rewrite <-derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_1 : mpn_copyi_entail_wit_1.
Proof.
  pre_process.
  Exists l2 l_2.
  entailer!.
  pose proof (Zlength_nonneg l_2).
  lia.
Qed.

Lemma proof_of_mpn_copyi_entail_wit_2 : mpn_copyi_entail_wit_2.
Proof.
  pre_process.
  Exists l2' l_3.
  entailer!.
  rewrite replace_Znth_app_r.
  + rewrite Zlength_sublist0; [ | lia ].
    assert (i - i = 0). { lia. }
    rewrite H15; clear H15.
    assert (replace_Znth 0 (Znth i l_3 0) (a :: nil) = sublist i (i + 1) l_3). {
      unfold replace_Znth, Z.to_nat, replace_nth.
      rewrite (sublist_single i l_3 0); [ reflexivity | ].
      rewrite <-Zlength_correct; lia.
    }
    rewrite H15; clear H15.
    rewrite replace_Znth_nothing.
    - rewrite <-sublist_split; try lia; try reflexivity.
      rewrite <-Zlength_correct; lia.
    - pose proof (Zlength_sublist0 i l_3 ltac:(lia)).
      lia.
  + pose proof (Zlength_sublist0 i l_3); lia.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z.
  Intros l.
  Exists l.
  unfold mpd_store_list.
  entailer!.
  subst.
  entailer!.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_2 : mpn_copyi_which_implies_wit_2.
Proof.
  pre_process.
  pose proof (store_uint_array_divide d cap2 l2 0).
  pose proof (Zlength_nonneg l2).
  specialize (H0 ltac:(lia) ltac:(lia)).
  destruct H0 as [H0 _].
  simpl in H0.
  entailer!.
  rewrite (sublist_nil l2 0 0) in H0; [ | lia].
  sep_apply H0.
  entailer!.
  unfold store_uint_array, store_uint_array_rec.
  unfold store_array.
  rewrite (sublist_self l2 cap2); [ | lia ].
  assert (d + 0 = d). { lia. }
  rewrite H2; clear H2.
  assert (cap2 - 0 = cap2). { lia. }
  rewrite H2; clear H2.
  reflexivity.
Qed.

Lemma proof_of_mpn_copyi_which_implies_wit_3 : mpn_copyi_which_implies_wit_3.
Proof.
  pre_process.
  destruct l'. {
    unfold store_uint_array_rec.
    simpl.
    entailer!.
  }
  pose proof (store_uint_array_rec_cons d i cap2  z l' ltac:(lia)).
  sep_apply H2.
  Exists z l'.
  entailer!.
  assert (i = 0 \/ i > 0). { lia. }
  destruct H3.
  + subst.
    unfold store_uint_array, store_array.
    simpl.
    entailer!.
  + pose proof (Aux.store_uarray_rec_equals_store_uarray d 0 i (sublist 0 i l) ltac:(lia)).
    destruct H4 as [_ H4].
    assert (d + sizeof(UINT) * 0 = d). { lia. }
    rewrite H5 in H4; clear H5.
    assert (i - 0 = i). { lia. }
    rewrite H5 in H4; clear H5.
    sep_apply H4; clear H4.
    pose proof (Aux.store_uarray_rec_equals_store_uarray d 0 (i + 1) (sublist 0 i l ++ z :: nil) ltac:(lia)).
    destruct H4 as [H4 _].
    assert (i + 1 - 0 = i + 1). { lia. }
    rewrite H5 in H4; clear H5.
    assert (d + sizeof(UINT) * 0 = d). { lia. }
    rewrite H5 in H4; clear H5.
    rewrite <-H4.
    sep_apply store_uint_array_rec_tail_merge; [ reflexivity | lia ].
Qed.

Lemma proof_of_mpn_cmp_safety_wit_1 : mpn_cmp_safety_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_1 : mpn_cmp_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (n_pre - 1 + 1 = n_pre). { lia. }
  rewrite H8; clear H8.
  pose proof (Zlength_sublist n_pre n_pre l1 ltac:(lia)).
  pose proof (Zlength_nil_inv (sublist n_pre n_pre l1) ltac:(lia)).
  rewrite H9.
  pose proof (Zlength_sublist n_pre n_pre l2 ltac:(lia)).
  pose proof (Zlength_nil_inv (sublist n_pre n_pre l2) ltac:(lia)).
  rewrite H11.
  reflexivity.
Qed.

Lemma proof_of_mpn_cmp_entail_wit_2 : mpn_cmp_entail_wit_2.
Proof.
  pre_process.
  entailer!; try lia.
  assert (n - 1 + 1 = n). { lia. }
  rewrite H17; clear H17.
  assert (n_pre <= Z.of_nat (Datatypes.length l1)). {
    rewrite <-Zlength_correct.
    lia.
  }
  assert (n_pre <= Z.of_nat (Datatypes.length l2)). {
    rewrite <-Zlength_correct.
    lia.
  }
  rewrite (sublist_split n n_pre (n + 1) l1 ltac:(lia) ltac:(lia)).
  rewrite (sublist_split n n_pre (n + 1) l2 ltac:(lia) ltac:(lia)).
  rewrite (sublist_single n l1 0 ltac:(lia)).
  rewrite (sublist_single n l2 0 ltac:(lia)).
  rewrite H.
  rewrite H7.
  reflexivity.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1_1 : mpn_cmp_return_wit_1_1.
Proof.
  pre_process.
  entailer!.
  Left; Left.
  entailer!.
  + unfold mpd_store_Z_compact.
    Exists l1 l2.
    unfold mpd_store_list.
    entailer!.
    rewrite <-H6, <-H7.
    entailer!.
  + assert (Znth n l1 0 < Znth n l2 0). { lia. }
    clear H H0.
    apply (list_store_Z_compact_cmp l1 l2 val1 val2 n ltac:(lia) ltac:(lia) H4 H5).
    - rewrite <-H6, <-H7.
      tauto.
    - lia.
Qed.

Lemma proof_of_mpn_cmp_return_wit_1_2 : mpn_cmp_return_wit_1_2.
Proof.
  pre_process.
  Right.
  entailer!.
  + unfold mpd_store_Z_compact, mpd_store_list.
    Exists l1 l2.
    rewrite <-H6, <-H7.
    entailer!.
  + pose proof (list_store_Z_compact_cmp l2 l1 val2 val1 n ltac:(lia) ltac:(lia) H5 H4).
    rewrite <-H6, <-H7 in H18.
    rewrite H8 in H18.
    specialize (H18 ltac:(reflexivity) ltac:(lia)).
    lia.
Qed.

Lemma proof_of_mpn_cmp_which_implies_wit_1 : mpn_cmp_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l2 l1.
  unfold mpd_store_list.
  entailer!.
  rewrite <-H0, <-H2.
  entailer!.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1_1 : mpn_cmp4_return_wit_1_1.
Proof.
  pre_process.
  Right.
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  entailer!.
  pose proof (list_store_Z_cmp_length l2 l1 val2 val1 ltac:(lia) H9 H7).
  lia.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_1_2 : mpn_cmp4_return_wit_1_2.
Proof.
  pre_process.
  Left; Left.
  unfold mpd_store_Z_compact.
  entailer!.
  Intros l1 l2.
  Exists l1 l2.
  entailer!.
  pose proof (list_store_Z_cmp_length l1 l2 val1 val2 ltac:(lia) H7 H9).
  lia.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2_1 : mpn_cmp4_return_wit_2_1.
Proof.
  pre_process.
  Right.
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  entailer!.
Qed.
    

Lemma proof_of_mpn_cmp4_return_wit_2_2 : mpn_cmp4_return_wit_2_2.
Proof.
  pre_process.
  Left; Right.
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  entailer!.
Qed.

Lemma proof_of_mpn_cmp4_return_wit_2_3 : mpn_cmp4_return_wit_2_3.
Proof.
  pre_process.
  Left; Left.
  unfold mpd_store_Z_compact.
  Intros l1 l2.
  Exists l1 l2.
  entailer!.
Qed.