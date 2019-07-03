Require Import VST.floyd.proofauto.
Require Import qsort3.
Require Import spec_qsort3.
Require Import float_lemmas.
Require Import Permutation.
Require Import qsort3_aux.
Require Import verif_qsort3_part1.

Lemma justify_quicksort_call1:
 forall (lo hi : Z)
  (H2 : 0 <= lo)
  (bl : list val),
  let N := Zlength bl in 
  forall (H3 : hi < N)
  (left mid right : Z)
  (H4 : lo < left <= hi)
  (H5 : lo <= right < hi)
  (H6 : lo <= mid < hi)
  (H7 : left = right + 1 \/ left = right + 2)
  (H8 : Forall (f_cmp Cge (Znth mid bl)) (sublist lo left bl))
  (H9 : Forall (f_cmp Cle (Znth mid bl)) (sublist (right + 1) (hi + 1) bl))
  (H12 : sorted (f_cmp Cle) (sublist 0 lo bl))
  (H14 : sorted (f_cmp Cle) (sublist (hi + 1) N bl))
  (H15 : 0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl))
  (H16 : hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl)) (sublist 0 (hi + 1) bl))
  (Hdef_bl : Forall def_float bl) 
  (bl' : list val) 
  (H17 : Permutation (sublist left (hi + 1) bl) bl')
  (H18 : sorted (f_cmp Cle) bl')
  (Hlen_bl' : hi + 1 - left = Zlength bl'),
sorted (f_cmp Cle)
  (sublist 0 lo (sublist 0 left bl ++ bl' ++ sublist (hi + 1) N bl)) /\
sorted (f_cmp Cle)
  (sublist (right + 1) N (sublist 0 left bl ++ bl' ++ sublist (hi + 1) N bl)) /\
(0 < lo ->
 Forall
   (f_cmp Cle (Znth (lo - 1) (sublist 0 left bl ++ bl' ++ sublist (hi + 1) N bl)))
   (sublist lo N (sublist 0 left bl ++ bl' ++ sublist (hi + 1) N bl))) /\
(right + 1 < N ->
 Forall
   (f_cmp Cge
      (Znth (right + 1) (sublist 0 left bl ++ bl' ++ sublist (hi + 1) N bl)))
   (sublist 0 (right + 1) (sublist 0 left bl ++ bl' ++ sublist (hi + 1) N bl))).
Proof.
intros.
split3.
rewrite sublist_app by list_solve.
autorewrite with sublist.
auto.
rewrite sublist_app; try list_solve.
autorewrite with sublist.
rewrite sublist_app by list_solve.
change (@reptype CompSpecs tdouble) with val in *.
autorewrite with sublist.
rewrite <- Hlen_bl'.
replace (N - left - (hi+1-left) + (hi + 1)) with N by omega.
rewrite (sublist_same _ _ bl') by omega.
apply sorted_app with (Znth mid bl).
*
apply f_cmp_le_trans.
*
destruct H7.
subst.
autorewrite with sublist. constructor.
rewrite sublist_one; try rep_omega.
constructor.
*
destruct (zlt (hi+1) N).
--
specialize (H16 l).
apply sorted_app with (Znth (hi+1) bl).
++
apply f_cmp_le_trans.
++
auto.
++
assumption.
++
eapply Forall_perm; try apply H17.
rewrite (sublist_split 0 left) in H16 by omega.
rewrite Forall_app in H16. destruct H16.
eapply Forall_impl; try eassumption.
intros.
eapply (f_cmp_swap Cge); auto.
++ 
apply sorted_ge_first; auto; omega.
--
autorewrite with sublist.
auto.
*
rewrite (sublist_split lo (right+1)) in H8 by omega.
rewrite Forall_app in H8; destruct H8.
eapply Forall_impl; try eassumption.
intros.
eapply (f_cmp_swap Cge); auto.
*
apply Forall_app; split.
eapply Forall_perm; try apply H17.
rewrite (sublist_split (right+1) left) in H9 by omega.
rewrite Forall_app in H9; destruct H9; auto.
destruct (zlt (hi+1) N).
2: autorewrite with sublist; constructor.
specialize (H16 l).
replace (Znth mid bl) with
  (Znth mid (sublist 0 (hi+1) bl)) by (autorewrite with sublist; auto).
apply Forall_Znth with (i:=mid) in H16; try (autorewrite with sublist; omega).
apply f_cmp_swap in H16.
simpl in H16.
apply Forall_impl with (f_cmp Cle (Znth (hi+1) bl)).
intros. eapply f_cmp_le_trans; eassumption.
apply sorted_ge_first; auto; try omega.
*
split; intros; autorewrite with sublist.
--
specialize (H15 H).
eapply Forall_perm; try apply H15.
rewrite sublist_app; autorewrite with sublist; try omega.
rewrite sublist_app; autorewrite with sublist; try omega.
rewrite (sublist_split lo left N) by omega.
rewrite (sublist_split left (hi+1)) by omega.
apply Permutation_app_head.
apply Permutation_app.
rewrite (sublist_same 0) by omega.
auto.
replace (N - left - Zlength bl' + (hi+1)) with N by omega.
apply Permutation_refl.
--
destruct H7; subst left; autorewrite with sublist.
++
rewrite (sublist_split 0 lo) by omega.
rewrite Forall_app; split.
**
destruct (zlt 0 lo).
---
apply (@Forall_impl _ (f_cmp Cge (Znth mid bl))).
intros. apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
assert (Forall (f_cmp Cle (Znth mid bl)) bl')
  by (eapply Forall_perm; try apply H17; eauto).
apply (Forall_Znth (f_cmp Cle (Znth mid bl))); auto; omega.
apply (@Forall_impl _ (f_cmp Cge (Znth (lo-1) bl))).


intros. apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
replace (Znth mid bl) with (Znth (mid-lo) (sublist lo N bl))
  by (autorewrite with sublist; auto).
apply (Forall_Znth (f_cmp _ _)); auto.
autorewrite with sublist; omega.
apply sorted_le_last; auto; omega.
---
autorewrite with sublist. constructor.
**
eapply Forall_impl; [ | apply H8].
intros. apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
assert (Forall (f_cmp Cle (Znth mid bl)) bl')
  by (eapply Forall_perm; try apply H17; eauto).
apply (Forall_Znth (f_cmp Cle (Znth mid bl))); auto; omega.
++
rewrite (sublist_split 0 lo) by omega.
rewrite Forall_app; split.
rewrite (sublist_split _ (right+2)) in H9 by omega.
rewrite Forall_app in H9; destruct H9 as [H9 _].
rewrite sublist_one in H9 by omega.
inv H9. 
apply Forall_impl with (f_cmp Cge (Znth mid bl)).
intros.
intros. apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
auto.
destruct (zlt 0 lo); [ | autorewrite with sublist; constructor].
apply sorted_le_last in H12; auto; try omega.
eapply Forall_impl; try apply H12.
simpl; intros.  
intros. apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
replace (Znth mid bl) with (Znth (mid-lo) (sublist lo N bl))
  by (autorewrite with sublist; auto).
eapply (Forall_Znth (f_cmp Cle _)); try apply  H15; auto; try omega.
autorewrite with sublist; omega.
rewrite (sublist_split lo (right+1)) in H8 by omega.
rewrite Forall_app in H8; destruct H8 as [H8 _].
eapply Forall_impl; try apply H8.
intros.
intros. apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
rewrite (sublist_split _ (right+2)) in H9 by omega.
rewrite Forall_app in H9; destruct H9 as [H9 _].
rewrite sublist_one in H9 by omega. inv H9; auto.
Qed.

Lemma justify_quicksort_call2:
  forall (lo hi : Z)
  (H2 : 0 <= lo)
  (bl : list val),
  let N := Zlength bl in
  forall (H3 : hi < N)
     (left mid right : Z)
    (H4 : lo < left <= hi)
  (H5 : lo <= right < hi)
  (H6 : lo <= mid < hi)
  (H7 : left = right + 1 \/ left = right + 2)
  (H8 : Forall (f_cmp Cge (Znth mid bl)) (sublist lo left bl))
  (H9 : Forall (f_cmp Cle (Znth mid bl)) (sublist (right + 1) (hi + 1) bl))
  (H12 : sorted (f_cmp Cle) (sublist 0 lo bl))
  (H14 : sorted (f_cmp Cle) (sublist (hi + 1) N bl))
  (H15 : 0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl))
  (H16 : hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl)) (sublist 0 (hi + 1) bl))
  (Hdef_bl : Forall def_float bl)
  (bl' : list val)
  (H17 : Permutation (sublist lo (right + 1) bl) bl')
  (H18 : sorted (f_cmp Cle) bl') 
  (Hlen_bl' : right + 1 - lo = Zlength bl'),
sorted (f_cmp Cle)
  (sublist 0 left (sublist 0 lo bl ++ bl' ++ sublist (right + 1) N bl)) /\
sorted (f_cmp Cle)
  (sublist (hi + 1) N (sublist 0 lo bl ++ bl' ++ sublist (right + 1) N bl)) /\
(0 < left ->
 Forall
   (f_cmp Cle
      (Znth (left - 1) (sublist 0 lo bl ++ bl' ++ sublist (right + 1) N bl)))
   (sublist left N (sublist 0 lo bl ++ bl' ++ sublist (right + 1) N bl))) /\
(hi + 1 < N ->
 Forall
   (f_cmp Cge
      (Znth (hi + 1) (sublist 0 lo bl ++ bl' ++ sublist (right + 1) N bl)))
   (sublist 0 (hi + 1) (sublist 0 lo bl ++ bl' ++ sublist (right + 1) N bl))).
Proof.
intros.
split3.
rewrite sublist_app by list_solve.
autorewrite with sublist.
rewrite sublist_app by list_solve.
change (@reptype CompSpecs tdouble) with val in *.
autorewrite with sublist.
rewrite (sublist_same 0 (Zlength bl')) by auto.
rewrite <- Hlen_bl'.
replace (left - lo - (right + 1 - lo) + (right + 1)) with left by omega.
destruct (zlt 0 lo).
*
specialize (H15 l).
apply sorted_app with (Znth (lo-1) bl).
--
apply f_cmp_le_trans.
--
auto.
--
destruct H7; [autorewrite with sublist; auto |].
rewrite sublist_one; try rep_omega.
subst left.
apply sorted_app with (Znth mid bl).
++
apply f_cmp_le_trans.
++
auto.
++
constructor.
++
eapply Forall_perm; try apply H17.
rewrite (sublist_split lo (right+1)) in H8 by omega.
rewrite Forall_app in H8. destruct H8 as [H8 _].
eapply Forall_impl; try apply H8.
intros.
apply f_cmp_swap in H. simpl in H.
auto.
++
repeat constructor.
rewrite (sublist_split _ (right+2)) in H9 by omega.
rewrite Forall_app in H9. destruct H9 as [H9 _].
rewrite sublist_one in H9 by omega.
inv H9; auto.
--
apply sorted_le_last in H12; auto; try omega.
eapply Forall_impl; try apply H12.
intros.
apply f_cmp_swap in H.
eapply f_cmp_le_trans; try apply H.
apply f_le_refl.
apply Forall_Znth; auto. omega.
--
rewrite Forall_app; split.
eapply Forall_perm; try apply H17.
rewrite (sublist_split _ (right+1)) in H15 by omega.
rewrite Forall_app in H15; destruct H15; auto.
destruct H7.
autorewrite with sublist. constructor.
rewrite sublist_one by omega.
repeat constructor.
replace (Znth (right + 1) bl)
  with (Znth (right + 1-lo) (sublist lo N bl)) by (autorewrite with sublist; auto).
eapply (Forall_Znth (f_cmp _ _)); try apply H15; try omega.
autorewrite with sublist; omega.
*
autorewrite with sublist.
destruct H7.
autorewrite with sublist. auto.
rewrite sublist_one by omega.
apply sorted_app with (Znth (right+1) bl).
++
apply f_cmp_le_trans.
++
auto.
++
constructor.
++
eapply Forall_perm; try apply H17.
rewrite (sublist_split lo (right+1)) in H8 by omega.
rewrite Forall_app in H8. destruct H8 as [H8 _].
eapply Forall_impl; try apply H8.
intros.
apply f_cmp_swap in H0. simpl in H0.
eapply f_cmp_le_trans; try apply H0.
rewrite (sublist_split (right+1) (right+2)) in H9 by list_solve.
rewrite Forall_app in H9; destruct H9 as [H9 _].
rewrite sublist_one in H9 by omega. inv H9; auto.
++
repeat constructor.
apply f_le_refl.
apply Forall_Znth; auto. omega.
*
autorewrite with sublist.
rewrite <- Hlen_bl'.
replace (hi + 1 - lo - (right + 1 - lo) + (right + 1))
  with (hi+1) by (clear; omega).
replace (N - lo - (right + 1 - lo) + (right + 1))
  with N by (clear; omega).
auto.
*
split; intros; autorewrite with sublist; rewrite <- Hlen_bl'.
--
replace (left - lo - (right + 1 - lo) + (right + 1))
  with left by (clear; omega).
replace (N - lo - (right + 1 - lo) + (right + 1)) with N by (clear; omega).
destruct H7; subst.
++
autorewrite with sublist.
apply Forall_impl with (f_cmp Cle (Znth mid bl)).
intros. eapply f_cmp_le_trans; try apply H7.
change Cle with (swap_comparison Cge).
apply f_cmp_swap.
assert (Forall (f_cmp Cge (Znth mid bl)) bl').
eapply Forall_perm; try apply H17.
auto.
eapply (Forall_Znth (f_cmp _ _)); try apply H1; try omega.
auto.
rewrite (sublist_split _ (hi+1)) by omega.
rewrite Forall_app; split; auto.
destruct (zlt (hi+1) N); [ | autorewrite with sublist; constructor].
apply sorted_ge_first in H14; try omega; auto.
eapply Forall_impl; try apply H14.
intros.
eapply f_cmp_le_trans; try apply H0.
(*
replace (Znth (hi + 1) bl)
  with (Znth 0 (sublist (hi+1) N bl)) by (autorewrite with sublist; auto).
apply f_cmp_le_trans with (Znth (hi+1) bl).
2: eapply (Forall_Znth (f_cmp _ _)); try apply H14; 
  try (autorewrite with sublist; omega).
*)
specialize (H16 l). clear H0.
change Cle with (swap_comparison Cge).
apply f_cmp_swap.
replace (Znth mid bl)
  with (Znth mid (sublist 0 (hi+1) bl)) by (autorewrite with sublist; auto).
eapply (Forall_Znth (f_cmp _ _)); try apply H16; 
  try (autorewrite with sublist; omega).
++
autorewrite with sublist.
rewrite <- Hlen_bl'.
replace (right + 2 - 1 - lo - (right + 1 - lo) + (right + 1))
  with (right+1) by (clear; omega).
clear dependent bl'.
rewrite (sublist_split _ (hi+1)) by omega.
rewrite Forall_app; split.
rewrite (sublist_split _ (right+2)) in H9 by omega.
rewrite Forall_app in H9; destruct H9 as [_ H9].
eapply Forall_impl; try apply H9.
intros.
eapply f_cmp_le_trans; try apply H0.
rewrite (sublist_split _ (right+1)) in H8 by omega.
rewrite Forall_app in H8; destruct H8 as [_ H8].
rewrite sublist_one in H8 by omega.
inv H8.
apply f_cmp_swap in H10; auto.
destruct (zlt (hi+1) N).
apply sorted_ge_first in H14; auto; try omega.
eapply Forall_impl; try apply H14.
intros.
eapply f_cmp_le_trans; try apply H0.
specialize (H16 l).
apply (f_cmp_swap Cge).
replace (Znth (right+1) bl)
  with (Znth (right+1) (sublist 0 (hi+1) bl)) by (autorewrite with sublist; auto).
eapply (Forall_Znth (f_cmp _ _)); try apply H16; 
  try (autorewrite with sublist; omega).
autorewrite with sublist. constructor.
--
replace (hi + 1 - lo - (right + 1 - lo) + (right + 1))
 with (hi+1) by (clear; omega).
rewrite sublist0_app2 by list_solve.
autorewrite with sublist.
rewrite sublist0_app2 by list_solve.
autorewrite with sublist.
rewrite <- Hlen_bl'.
replace (hi + 1 - lo - (right + 1 - lo) + (right + 1))
  with (hi+1) by (clear; omega).
rewrite Forall_app; split.
++
destruct (zlt 0 lo); [ | autorewrite with sublist; constructor].
specialize (H15 l).
apply sorted_le_last in H12; auto; try omega.
eapply Forall_impl; try apply H12.
intros.
apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
replace (Znth (hi+1) bl) with (Znth (hi+1-lo) (sublist lo N bl)) 
 by  (autorewrite with sublist; auto).
eapply (Forall_Znth (f_cmp _ _)); try apply H15; 
  try (autorewrite with sublist; omega).
++
rewrite Forall_app; split.
**
eapply Forall_perm; try apply H17.
clear dependent bl'.
rewrite (sublist_split _ (right+1)) in H8 by (destruct H7; omega).
rewrite Forall_app in H8. destruct H8 as [H8 _].
eapply Forall_impl; try apply H8.
intros.
apply f_cmp_swap in H0; simpl in H0.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; try apply H0.
specialize (H16 H).
apply (f_cmp_swap Cge).
replace (Znth mid bl) with (Znth mid (sublist 0 (hi+1) bl))
 by  (autorewrite with sublist; auto).
eapply (Forall_Znth (f_cmp _ _)); try apply H16; 
  try (autorewrite with sublist; omega).
**
specialize (H16 H).
rewrite (sublist_split _ (right+1)) in H16 by omega.
rewrite Forall_app in H16; destruct H16; auto.
Qed.





