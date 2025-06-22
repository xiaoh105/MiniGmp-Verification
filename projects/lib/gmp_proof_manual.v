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
Require Import GmpLib.GmpAux. Import Aux.
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
Qed.

Lemma proof_of_gmp_max_return_wit_1_2 : gmp_max_return_wit_1_2.
Proof.
  pre_process.
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
  + pose proof (Aux.uint_array_rec_to_uint_array d 0 i (sublist 0 i l) ltac:(lia)).
    destruct H4 as [_ H4].
    assert (d + sizeof(UINT) * 0 = d). { lia. }
    rewrite H5 in H4; clear H5.
    assert (i - 0 = i). { lia. }
    rewrite H5 in H4; clear H5.
    sep_apply H4; clear H4.
    pose proof (Aux.uint_array_rec_to_uint_array d 0 (i + 1) (sublist 0 i l ++ z :: nil) ltac:(lia)).
    destruct H4 as [H4 _].
    assert (i + 1 - 0 = i + 1). { lia. }
    rewrite H5 in H4; clear H5.
    assert (d + sizeof(UINT) * 0 = d). { lia. }
    rewrite H5 in H4; clear H5.
    rewrite <-H4.
    sep_apply store_uint_array_rec_tail_merge; [ reflexivity | lia ].
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

Lemma proof_of_mpn_normalized_size_entail_wit_2 : mpn_normalized_size_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  + pose proof (store_uint_array_divide_rec 
      xp_pre n (sublist 0 n l) (n - 1) ltac:(lia)).
    rewrite (Zlength_sublist0 n l ltac:(lia)) in H12.
    specialize (H12 ltac:(lia)).
    destruct H12 as [H12 _].
    rewrite H12; clear H12.
    rewrite (sublist_sublist00 (n - 1) n l ltac:(lia)).
    rewrite (sublist_sublist0 n n (n - 1) l ltac:(lia) ltac:(lia)).
    pose proof (Aux.uint_array_rec_to_uint_array xp_pre 0 (n - 1) (sublist 0 (n - 1) l) ltac:(lia)).
    destruct H12 as [H12 _].
    rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r in H12.
    rewrite H12; clear H12.
    entailer!.
    assert (n - 1 < Z.of_nat (Datatypes.length l)). {
      rewrite <-Zlength_correct.
      lia.
    }
    pose proof (sublist_single (n - 1) l 0 ltac:(lia)).
    clear H12.
    pose proof (Aux.store_uint_array_single_to_undef xp_pre (n - 1) (Znth (n - 1) l 0)).
    assert (n - 1 + 1 = n). { lia. }
    rewrite H14 in H12, H13; clear H14.
    rewrite H13, H12; clear H13 H12.
    pose proof (Aux.store_undef_uint_array_rec_divide xp_pre (n - 1) n cap ltac:(lia) ltac:(lia)).
    rewrite <-H12.
    entailer!.
  + assert (n <= Z.of_nat (Datatypes.length l)). {
      rewrite <-Zlength_correct.
      lia.
    }
    pose proof (sublist_split 0 n (n - 1) l ltac:(lia) ltac:(lia)).
    clear H12.
    rewrite H13 in H6.
    apply (list_store_Z_split) in H6; destruct H6.
    assert (Z.of_nat (Datatypes.length l) = Zlength l). {
      rewrite (Zlength_correct l); reflexivity.
    }
    pose proof (sublist_single (n - 1) l 0 ltac:(lia)).
    assert (n - 1 + 1 = n). { lia. }
    rewrite H16 in H15; clear H16.
    rewrite H15 in H12.
    unfold list_store_Z in H12; destruct H12.
    simpl in H12.
    rewrite Znth_sublist0 in H; try lia.
    rewrite H in H12.
    rewrite (Zlength_sublist0 (n - 1) l) in *; try lia.
    pose proof (Z_div_mod_eq_full val (UINT_MOD ^ (n - 1))).
    rewrite <-H12, Z.mul_0_r, Z.add_0_l in H17.
    rewrite <-H17 in H6.
    tauto.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1_1 : mpn_normalized_size_return_wit_1_1.
Proof.
  pre_process.
  assert (n = 0). { lia. }
  clear H H0.
  rewrite H11 in *.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists nil.
  entailer!.
  + rewrite Zlength_nil.
    lia.
  + unfold list_store_Z_compact.
    simpl.
    rewrite sublist_nil in H5; try lia.
    unfold list_store_Z in H5; simpl in H5.
    destruct H5.
    lia.
Qed.

Lemma proof_of_mpn_normalized_size_return_wit_1_2 : mpn_normalized_size_return_wit_1_2.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (sublist 0 n l).
  entailer!.
  + rewrite Zlength_sublist0; try lia.
    entailer!.
  + rewrite Zlength_sublist0; lia.
  + rewrite Zlength_sublist0; lia.
  + unfold list_store_Z_compact.
    unfold list_store_Z in H6.
    destruct H6.
    rewrite Aux.list_last_to_Znth.
    - rewrite Zlength_sublist0; try lia.
      repeat split; try tauto.
      pose proof (list_within_bound_Znth (sublist 0 n l) (n - 1)).
      rewrite Zlength_sublist0 in H13; try lia.
      specialize (H13 ltac:(lia) H12).
      lia.
    - assert (sublist 0 n l = nil \/ sublist 0 n l <> nil). { tauto. }
      destruct H13.
      * pose proof (Zlength_sublist0 n l ltac:(lia)).
        rewrite H13 in H14.
        rewrite Zlength_nil in H14.
        lia.
      * tauto.
Qed.

Lemma proof_of_mpn_normalized_size_which_implies_wit_1 : mpn_normalized_size_which_implies_wit_1.
Proof. 
  pre_process.
  unfold mpd_store_Z.
  Intros l.
  Exists l.
  unfold mpd_store_list.
  entailer!.
  + rewrite H0.
    rewrite sublist_self; try lia.
    entailer!.
  + rewrite sublist_self; try lia.
    tauto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_1 : mpn_add_1_entail_wit_1.
Proof.
  pre_process.
  Exists l2 nil 0 0 l_2.
  entailer!.
  - unfold list_store_Z.
    split.
    + simpl. tauto.
    + simpl. tauto.
  - rewrite (sublist_nil l_2 0 0); try lia.
    unfold list_store_Z.
    split.
    + simpl. tauto.
    + simpl. tauto.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_2 : mpn_add_1_entail_wit_2.
Proof.
  pre_process.
  prop_apply (store_uint_range &("b") b).
  entailer!.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_3_1 : mpn_add_1_entail_wit_3_1.
Proof.
  pre_process.
  rewrite replace_Znth_app_r.
  - Exists l'''.
    rewrite H14.
    assert (i - i = 0) by lia.
    rewrite H26.
    set (new_b := (unsigned_last_nbits (Znth i l_3 0 + b) 32)).
    rewrite replace_Znth_nothing; try lia.
    assert (replace_Znth 0 new_b (a :: nil) = new_b :: nil). {
      unfold replace_Znth.
      unfold Z.to_nat.
      unfold replace_nth.
      reflexivity.
    }
    rewrite H27.
    Exists (l'_2 ++ new_b :: nil).
    Exists (val2_2 + new_b * (UINT_MOD^ i)).
    Exists (val1_2 + (Znth i l_3 0) * (UINT_MOD^ i)).
    Exists l_3.
    entailer!.
    + rewrite Zlength_app.
      rewrite H14.
      unfold Zlength.
      unfold Zlength_aux.
      lia.
    + assert (val1_2 + Znth i l_3 0 * 4294967296 ^ i + b_pre = (val1_2 + b_pre) + Znth i l_3 0 * 4294967296 ^ i) by lia.
      rewrite H28.
      rewrite <- H13.
      assert (Znth i l_3 0 + b = new_b + UINT_MOD).
      {
        subst new_b.
        unfold unsigned_last_nbits.
        unfold unsigned_last_nbits in H3.
        assert (2^32 = 4294967296). { nia. }
        rewrite H29 in *.
        assert (0 <= Znth i l_3 0 < 4294967296). {
          assert (l_2=l_3).
          {
            pose proof (list_store_Z_compact_reverse_injection l_2 l_3 val val).
            apply H30 in H9; try tauto.
          }
          assert (i < Zlength l_3). {
            subst l_3.
            rewrite H17.
            tauto.
          }
          unfold list_store_Z_compact in H9.
          apply list_within_bound_Znth.
          lia.
          tauto.
        }
        apply Z_mod_add_carry; try lia; try tauto.
      }
      assert (b * 4294967296 ^ i + Znth i l_3 0 * 4294967296 ^ i = new_b * 4294967296 ^ i + 1 * 4294967296 ^ (i + 1)).
      {
        subst new_b.
        rewrite <- Z.mul_add_distr_r.
        rewrite (Zpow_add_1 4294967296 i); try lia.
      }
      lia.
    + pose proof (__list_store_Z_concat_r l'_2 val2_2 new_b).
      apply H28 in H12.
      rewrite H14 in H12.
      assert (new_b * 4294967296 ^ i + val2_2 = (val2_2 + new_b * 4294967296 ^ i)) by lia.
      rewrite H29 in H12.
      tauto.
      subst new_b.
      unfold unsigned_last_nbits.
      assert (2 ^ 32 = 4294967296). { nia. }
      rewrite H29.
      apply Z.mod_pos_bound.
      lia.
      + assert (l_2=l_3).
        {
          pose proof (list_store_Z_compact_reverse_injection l_2 l_3 val val).
          apply H28 in H9; try tauto.
        }

        assert (i < Zlength l_3). {
          subst l_3.
          rewrite H17.
          tauto.
        }

        assert((sublist 0 (i + 1) l_3) = (sublist 0 i l_3) ++ (Znth i l_3 0)  :: nil). {
          pose proof (sublist_split 0 (i+1) i l_3).
          pose proof (sublist_single i l_3 0).
          rewrite <-H31.
          apply H30.
          lia.
          subst l_3.
          rewrite Zlength_correct in H29.
          lia.
          rewrite Zlength_correct in H29.
          lia.
        }
        rewrite H30.
        pose proof (__list_store_Z_concat_r (sublist 0 i l_3) val1_2 (Znth i l_3 0)).
        apply H31 in H11.
        rewrite Zlength_sublist0 in H11.
        assert (val1_2 + Znth i l_3 0 * 4294967296 ^ i = Znth i l_3 0 * 4294967296 ^ i + val1_2) by lia.
        rewrite H32.
        tauto.
        subst l_3.
        rewrite H17.
        lia.
        apply list_within_bound_Znth.
        lia.
        unfold list_store_Z_compact in H9.
        tauto.
  - pose proof (Zlength_sublist0 i l'_2).
    lia.
Qed.

Lemma proof_of_mpn_add_1_entail_wit_3_2 : mpn_add_1_entail_wit_3_2.
Proof.
  pre_process.
  rewrite replace_Znth_app_r.
  - Exists l'''.
    rewrite H14.
    assert (i - i = 0) by lia.
    rewrite H26.
    set (new_b := (unsigned_last_nbits (Znth i l_3 0 + b) 32)).
    rewrite replace_Znth_nothing; try lia.
    assert (replace_Znth 0 new_b (a :: nil) = new_b :: nil). {
      unfold replace_Znth.
      unfold Z.to_nat.
      unfold replace_nth.
      reflexivity.
    }
    rewrite H27.
    Exists (l'_2 ++ new_b :: nil).
    Exists (val2_2 + new_b * (UINT_MOD^ i)).
    Exists (val1_2 + (Znth i l_3 0) * (UINT_MOD^ i)).
    Exists l_3.
    entailer!.
    + rewrite Zlength_app.
      rewrite H14.
      unfold Zlength.
      unfold Zlength_aux.
      lia.
    + assert (val1_2 + Znth i l_3 0 * 4294967296 ^ i + b_pre = (val1_2 + b_pre) + Znth i l_3 0 * 4294967296 ^ i) by lia.
      rewrite H28.
      rewrite <- H13.
      assert (Znth i l_3 0 + b = new_b).
      {
        subst new_b.
        unfold unsigned_last_nbits.
        unfold unsigned_last_nbits in H3.
        assert (2^32 = 4294967296). { nia. }
        rewrite H29 in *.
        assert (0 <= Znth i l_3 0 < 4294967296). {
          assert (l_2=l_3).
          {
            pose proof (list_store_Z_compact_reverse_injection l_2 l_3 val val).
            apply H30 in H9; try tauto.
          }
          assert (i < Zlength l_3). {
            subst l_3.
            rewrite H17.
            tauto.
          }
          unfold list_store_Z_compact in H9.
          apply list_within_bound_Znth.
          lia.
          tauto.
        }
        apply Z_mod_add_uncarry; try lia; try tauto.
      }
      assert (b * 4294967296 ^ i + Znth i l_3 0 * 4294967296 ^ i = new_b * 4294967296 ^ i + 0 * 4294967296 ^ (i + 1)).
      {
        subst new_b.
        rewrite <- Z.mul_add_distr_r.
        rewrite (Zpow_add_1 4294967296 i); try lia.
      }
      lia.
    + pose proof (__list_store_Z_concat_r l'_2 val2_2 new_b).
      apply H28 in H12.
      rewrite H14 in H12.
      assert (new_b * 4294967296 ^ i + val2_2 = (val2_2 + new_b * 4294967296 ^ i)) by lia.
      rewrite H29 in H12.
      tauto.
      subst new_b.
      unfold unsigned_last_nbits.
      assert (2 ^ 32 = 4294967296). { nia. }
      rewrite H29.
      apply Z.mod_pos_bound.
      lia.
      + assert (l_2=l_3).
        {
          pose proof (list_store_Z_compact_reverse_injection l_2 l_3 val val).
          apply H28 in H9; try tauto.
        }

        assert (i < Zlength l_3). {
          subst l_3.
          rewrite H17.
          tauto.
        }

        assert((sublist 0 (i + 1) l_3) = (sublist 0 i l_3) ++ (Znth i l_3 0)  :: nil). {
          pose proof (sublist_split 0 (i+1) i l_3).
          pose proof (sublist_single i l_3 0).
          rewrite <-H31.
          apply H30.
          lia.
          subst l_3.
          rewrite Zlength_correct in H29.
          lia.
          rewrite Zlength_correct in H29.
          lia.
        }
        rewrite H30.
        pose proof (__list_store_Z_concat_r (sublist 0 i l_3) val1_2 (Znth i l_3 0)).
        apply H31 in H11.
        rewrite Zlength_sublist0 in H11.
        assert (val1_2 + Znth i l_3 0 * 4294967296 ^ i = Znth i l_3 0 * 4294967296 ^ i + val1_2) by lia.
        rewrite H32.
        tauto.
        subst l_3.
        rewrite H17.
        lia.
        apply list_within_bound_Znth.
        lia.
        unfold list_store_Z_compact in H9.
        tauto.
  - pose proof (Zlength_sublist0 i l'_2).
    lia.
Qed.

Lemma proof_of_mpn_add_1_return_wit_1 : mpn_add_1_return_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z_compact.
  unfold mpd_store_list.
  Exists val2.
  pose proof (list_store_Z_compact_reverse_injection l l_2 val val).
  apply H19 in H2; try tauto.
  rewrite <-H2 in H10.
  assert (i = n_pre) by lia.
  rewrite H20 in H4.
  rewrite <- H10 in H4.
  rewrite (sublist_self l (Zlength l)) in H4; try tauto.
  rewrite <-H2 in H12.
  assert (list_store_Z l val). { apply list_store_Z_compact_to_normal. tauto. }
  pose proof (list_store_Z_injection l l val1 val).
  apply H22 in H4; try tauto.
  rewrite H4 in H6.
  entailer!.
  Exists l.
  entailer!.
  entailer!; try rewrite H20; try tauto.
  - rewrite H10.
    entailer!.
    unfold mpd_store_Z.
    unfold mpd_store_list.
    Exists l'.
    rewrite H7.
    subst i.
    entailer!.
    rewrite H20.
    entailer!.
    apply store_uint_array_rec_def2undef.
  - rewrite <- H20. tauto.
Qed.

Lemma proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Proof.
  pre_process.
  unfold mpd_store_Z_compact.
  Intros l.
  Exists l.
  unfold mpd_store_list.
  entailer!.
  subst n_pre.
  entailer!.
Qed.

Lemma proof_of_mpn_add_1_which_implies_wit_2 : mpn_add_1_which_implies_wit_2.
Proof.
  pre_process.
  pose proof (store_uint_array_divide rp_pre cap2 l2 0).
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
  assert (rp_pre + 0 = rp_pre). { lia. }
  rewrite H2; clear H2.
  assert (cap2 - 0 = cap2). { lia. }
  rewrite H2; clear H2.
  reflexivity.
Qed.

Lemma proof_of_mpn_add_1_which_implies_wit_3 : mpn_add_1_which_implies_wit_3.
Proof.
  pre_process.
  destruct l''. {
    unfold store_uint_array_rec.
    simpl.
    entailer!.
  }
  pose proof (store_uint_array_rec_cons rp_pre i cap2  z l'' ltac:(lia)).
  sep_apply H2.
  Exists z l''.
  entailer!.
  assert (i = 0 \/ i > 0). { lia. }
  destruct H3.
  + subst.
    simpl.
    entailer!.
    simpl in H2.
    assert (rp_pre + 0 = rp_pre). { lia. }
    rewrite H3.
    rewrite H3 in H2.
    clear H3.
    pose proof (store_uint_array_empty rp_pre l').
    sep_apply H3.
    rewrite logic_equiv_andp_comm.
    rewrite logic_equiv_coq_prop_andp_sepcon.
    Intros.
    subst l'.
    rewrite app_nil_l.
    unfold store_uint_array.
    unfold store_array.
    unfold store_array_rec.
    simpl.
    assert (rp_pre + 0 = rp_pre). { lia. }
    rewrite H4; clear H4.
    entailer!.
  + pose proof (Aux.uint_array_rec_to_uint_array rp_pre 0 i (sublist 0 i l') ltac:(lia)).
    destruct H4 as [_ H4].
    assert (rp_pre + sizeof(UINT) * 0 = rp_pre). { lia. }
    rewrite H5 in H4; clear H5.
    assert (i - 0 = i). { lia. }
    rewrite H5 in H4; clear H5.
    pose proof (Aux.uint_array_rec_to_uint_array rp_pre 0 (i + 1) (sublist 0 i l' ++ z :: nil) ltac:(lia)).
    destruct H5 as [H5 _].
    assert (i + 1 - 0 = i + 1). { lia. }
    rewrite H6 in H5; clear H6.
    assert (rp_pre + sizeof(UINT) * 0 = rp_pre). { lia. }
    rewrite H6 in H5; clear H6.
    pose proof (uint_array_rec_to_uint_array rp_pre 0 i l').
    specialize (H6 H).
    assert ((rp_pre + sizeof ( UINT ) * 0) = rp_pre) by lia.
    rewrite H7 in H6; clear H7.
    assert ((i-0) = i) by lia.
    rewrite H7 in H6; clear H7.
    destruct H6 as [_ H6].
    sep_apply H6.
    (* pose proof (uint_array_rec_to_uint_array rp_pre 0 (i+1) (l' ++ z :: nil)).
    assert (H_i_plus_1 : 0 <= i + 1) by lia.
    specialize (H7 H_i_plus_1); clear H_i_plus_1.
    destruct H7 as [H7 _].
    assert (i + 1 - 0 = i + 1) by lia.
    rewrite H8 in H7; clear H8.
    assert ((rp_pre + sizeof ( UINT ) * 0) = rp_pre) by lia.
    rewrite H8 in H7; clear H8.
    rewrite <-H7.
    clear H6.
    clear H7. *)
    pose proof (store_uint_array_divide_rec rp_pre (i+1) (l' ++ z :: nil) i).
    assert (H_tmp: 0 <= i <= i+1) by lia.
    specialize (H7 H_tmp); clear H_tmp.
    rewrite <- store_uint_array_single.
    sep_apply store_uint_array_rec_divide_rev.
    entailer!.
    lia.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_1 : mpn_add_n_entail_wit_1.
Proof.
  pre_process.
  Exists l_r nil 0 0 0.
  Exists l_b_2 l_a_2.
  entailer!.
  - unfold list_store_Z.
    simpl.
    tauto.
  - rewrite sublist_nil; try lia; try tauto.
    unfold list_store_Z.
    simpl.
    tauto.
  - rewrite sublist_nil; try lia; try tauto.
    unfold list_store_Z.
    simpl.
    tauto.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_2 : mpn_add_n_entail_wit_2.
Proof.
  pre_process.
  prop_apply (store_uint_range &("cy") cy).
  entailer!.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_3_1 : mpn_add_n_entail_wit_3_1.
Proof.
  pre_process.
  rewrite replace_Znth_app_r.
  assert (l_a_3 = l_a_2). {
    pose proof (list_store_Z_compact_reverse_injection l_a_3 l_a_2 val_a val_a).
    specialize (H37 H13 H28).
    apply H37.
    reflexivity.
  }
  subst l_a_3.
  assert (l_b_3 = l_b_2). {
    pose proof (list_store_Z_compact_reverse_injection l_b_3 l_b_2 val_b val_b).
    specialize (H37 H14 H24).
    apply H37.
    reflexivity.
  }
  subst l_b_3.
  - Exists l_r_suffix'.
    rewrite H29.
    rewrite H18.
    assert (i - i = 0) by lia.
    rewrite H37; clear H37.
    set (partial_result_1 := (unsigned_last_nbits (Znth i l_a_2 0 + cy) 32)).
    set (partial_result_2 := (unsigned_last_nbits (partial_result_1 + Znth i l_b_2 0) 32)).
    rewrite replace_Znth_nothing; try lia.
    assert ((replace_Znth 0 partial_result_2 (a :: nil)) = partial_result_2 :: nil). {
      unfold replace_Znth.
      simpl.
      reflexivity.
    }
    rewrite H37; clear H37.
    Exists (l_r_prefix_2 ++ partial_result_2 :: nil).
    Exists (val_r_prefix_2 + partial_result_2 * (UINT_MOD ^ i)).
    Exists (val_b_prefix_2 + (Znth i l_b_2 0) * (UINT_MOD ^ i)).
    Exists (val_a_prefix_2 + (Znth i l_a_2 0) * (UINT_MOD ^ i)).
    Exists l_b_2 l_a_2.
    entailer!.
    + assert ( (val_a_prefix_2 + Znth i l_a_2 0 * 4294967296 ^ i +(val_b_prefix_2 + Znth i l_b_2 0 * 4294967296 ^ i)) = (val_a_prefix_2 + val_b_prefix_2) + Znth i l_a_2 0 * 4294967296 ^ i + Znth i l_b_2 0 * 4294967296 ^ i).
      {
        lia.
      }
      rewrite H37; clear H37.
      rewrite <- H19.
      assert ( (Znth i l_a_2 0) + (Znth i l_b_2 0) + cy = partial_result_2 + UINT_MOD). {
        unfold unsigned_last_nbits in H4, H3.
        assert (2 ^ 32 = 4294967296). { nia. }
        rewrite H37 in H4, H3; clear H37.
        apply Z_mod_3add_carry10; try lia; try tauto;
        try unfold list_store_Z_compact in H13, H14;
        try apply list_within_bound_Znth;
        try lia;
        try tauto.
      }
      assert ( partial_result_2 * 4294967296 ^ i + (1 + 0) * 4294967296 ^ (i + 1) = cy * 4294967296 ^ i + Znth i l_a_2 0 * 4294967296 ^ i + Znth i l_b_2 0 * 4294967296 ^ i). {
        rewrite <- Z.mul_add_distr_r.
        rewrite (Zpow_add_1 4294967296 i); try lia.
      }
      lia.
    + pose proof (Zlength_app l_r_prefix_2 (partial_result_2 :: nil)).
      assert (Zlength (partial_result_2 :: nil) = 1). {
        unfold Zlength.
        simpl.
        reflexivity.
      }
      rewrite H38 in H37; clear H38.
      rewrite H18 in H37.
      apply H37.
    + pose proof (list_store_Z_concat l_r_prefix_2 (partial_result_2 :: nil) val_r_prefix_2 partial_result_2).
      rewrite H18 in H37.
      apply H37.
      tauto.
      unfold list_store_Z.
      simpl.
      split.
      reflexivity.
      split.
      unfold partial_result_2.
      unfold unsigned_last_nbits.
      assert (2 ^ 32 = 4294967296). { nia. }
      rewrite H38; clear H38.
      apply Z.mod_pos_bound.
      lia.
      tauto.
    + pose proof (list_store_Z_list_append l_b_2 i val_b_prefix_2 val_b).
      apply H37.
      lia.
      tauto.
      tauto.
    + pose proof (list_store_Z_list_append l_a_2 i val_a_prefix_2 val_a).
      apply H37.
      lia.
      tauto.
      tauto.
  - pose proof (Zlength_sublist0 i l_r_prefix_2).
    lia.
Qed.

Lemma proof_of_mpn_add_n_entail_wit_3_2 : mpn_add_n_entail_wit_3_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_entail_wit_3_3 : mpn_add_n_entail_wit_3_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_entail_wit_3_4 : mpn_add_n_entail_wit_3_4.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_return_wit_1 : mpn_add_n_return_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_which_implies_wit_2 : mpn_add_n_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_which_implies_wit_3 : mpn_add_n_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_mpn_add_n_which_implies_wit_4 : mpn_add_n_which_implies_wit_4.
Proof. Admitted. 

Lemma proof_of_mpz_clear_return_wit_1_1 : mpz_clear_return_wit_1_1.
Proof.
  pre_process.
  Exists ptr_2 cap_2 size_2.
  entailer!.
  unfold mpd_store_Z_compact.
  Intros data.
  unfold mpd_store_list.
  subst.
  entailer!.
Qed.

Lemma proof_of_mpz_clear_return_wit_1_2 : mpz_clear_return_wit_1_2.
Proof.
  pre_process.
  Exists ptr_2 cap_2 size_2.
  entailer!.
  unfold mpd_store_Z_compact.
  Intros data.
  unfold mpd_store_list.
  entailer!.
  assert (size_2 = 0). {
    pose proof (Zlength_nonneg data).
    lia.
  }
  rewrite H6 in *.
  rewrite <-H3 in *.
  unfold store_uint_array, store_undef_uint_array_rec.
  unfold store_array.
  assert (cap_2 - 0 = 0). { lia. }
  rewrite H7; clear H7.
  pose proof (Zlength_nil_inv data ltac:(lia)).
  rewrite H7 in *; clear H7.
  simpl.
  entailer!.
Qed.

Lemma proof_of_mpz_clear_return_wit_1_3 : mpz_clear_return_wit_1_3.
Proof.
  pre_process.
  Exists ptr_2 cap_2 size_2.
  entailer!.
Qed.


Lemma proof_of_mpz_clear_return_wit_1_4 : mpz_clear_return_wit_1_4.
Proof.
  pre_process.
  Exists ptr_2 cap_2 size_2.
  entailer!.
Qed.

Lemma proof_of_mpz_clear_which_implies_wit_1 : mpz_clear_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_Z.
  Intros ptr cap size.
  entailer!.
  rewrite orp_sepcon_left.
  Split.
  + Right.
    Exists ptr cap size.
    entailer!.
  + Left.
    Exists ptr cap size.
    entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_1 : mpz_realloc_return_wit_1_1.
Proof.
  pre_process.
  Right.
  Exists retval_3 retval_2.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_2 : mpz_realloc_return_wit_1_2.
Proof.
  pre_process.
  Left.
  Exists retval_3 retval_2.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_3 : mpz_realloc_return_wit_1_3.
Proof.
  pre_process.
  Right.
  Exists retval_3 retval_2.
  entailer!.
  subst.
  unfold mpd_store_Z_compact.
  Intros data.
  Exists data.
  unfold mpd_store_list, store_undef_uint_array_rec.
  entailer!.
  assert (Zlength data = 0). {
    pose proof (Zlength_nonneg data).
    lia.
  }
  rewrite H10 in *.
  simpl.
  entailer!.
  pose proof (Zlength_nil_inv data H10).
  repeat subst.
  unfold store_uint_array, store_array; simpl; entailer!.
  unfold store_undef_uint_array, store_undef_array.
  rewrite Z.sub_0_r.
  reflexivity.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_4 : mpz_realloc_return_wit_1_4.
Proof.
  pre_process.
  Left.
  Exists retval_3 retval_2.
  entailer!.
  subst.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  Exists data.
  assert (Zlength data = 0). {
    pose proof (Zlength_nonneg data).
    lia.
  }
  rewrite H10 in *; clear H2.
  pose proof (Zlength_nil_inv data H10).
  rewrite H2 in *; clear H2 H10.
  unfold store_uint_array, store_array.
  simpl.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_5 : mpz_realloc_return_wit_1_5.
Proof.
  pre_process.
  Left.
  Exists retval_3 retval_2.
  entailer!.
  subst.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  Exists data.
  unfold store_uint_array, store_array.
  simpl.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_6 : mpz_realloc_return_wit_1_6.
Proof.
  pre_process.
  Right.
  Exists retval_3 retval_2.
  subst.
  entailer!.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data; Exists data.
  unfold store_uint_array, store_array.
  assert (Zlength data = 0). {
    pose proof (Zlength_nonneg data).
    lia.
  }
  rewrite H10 in *; clear H2.
  pose proof (Zlength_nil_inv data H10).
  rewrite H2 in *; clear H2 H10.
  unfold store_undef_uint_array, store_undef_uint_array_rec, store_undef_array.
  subst.
  simpl.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_7 : mpz_realloc_return_wit_1_7.
Proof.
  pre_process.
  Left.
  Exists retval_3 retval_2.
  subst.
  rewrite (Z.abs_neq old ltac:(lia)) in H.
  pose proof (Z.le_max_l size_pre 1).
  unfold mpd_store_Z_compact.
  Intros data; entailer!.
  unfold mpd_store_list.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_8 : mpz_realloc_return_wit_1_8.
Proof.
  pre_process.
  Right.
  Exists retval_3 retval_2.
  subst.
  rewrite (Z.abs_eq old ltac:(lia)) in H.
  pose proof (Z.le_max_l size_pre 1).
  unfold mpd_store_Z_compact.
  Intros data; entailer!.
  unfold mpd_store_list.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_6_pure : mpz_realloc_partial_solve_wit_6_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_7_pure : mpz_realloc_partial_solve_wit_7_pure.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_8_pure : mpz_realloc_partial_solve_wit_8_pure.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_9_pure : mpz_realloc_partial_solve_wit_9_pure.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  entailer!.
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_10_pure : mpz_realloc_partial_solve_wit_10_pure.
Proof.
  pre_process.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  entailer!.
Qed.
