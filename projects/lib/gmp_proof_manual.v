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