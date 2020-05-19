Require Import VST.floyd.proofauto.
Require Import qsort3.
Require Import spec_qsort3.
Require Import float_lemmas.
Require Import Permutation.
Require Import qsort3_aux.

Set Nested Proofs Allowed.

Definition quicksort_while_body_part2 := 
match quicksort_while_body
  with Ssequence _ (Ssequence _ (Ssequence _ a)) =>
     a
| _ => Sskip
end.

Definition quicksort_do_loop := 
match quicksort_while_body_part2
  with Ssequence _ (Ssequence _ (Ssequence a _)) =>
     a
| _ => Sskip
end.

Lemma forward_quicksort_do_loop :
forall (Espec : OracleKind) (base : val) (al : list val) 
  (lo mid hi : Z) (bl : list val),
Forall def_float al ->
let N := Zlength al in
0 < N <= Z.min Int.max_signed (Ptrofs.max_signed / 8) ->
isptr base ->
0 <= lo <= mid ->
mid < hi < N ->
f_cmp Cge (Znth mid bl) (Znth lo bl) ->
f_cmp Cle (Znth mid bl) (Znth hi bl) ->
Permutation al bl ->
sorted (f_cmp Cle) (sublist 0 lo bl) ->
sorted (f_cmp Cle) (sublist (hi + 1) N bl) ->
(0 < lo ->
 Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl)) ->
(hi + 1 < N ->
 Forall (f_cmp Cge (Znth (hi + 1) bl))
   (sublist 0 (hi + 1) bl)) ->

semax (func_tycontext f_quicksort Vprog Gprog [])
  (PROP ()
   LOCAL (temp _right_ptr (dnth base (hi - 1));
   temp _left_ptr (dnth base (lo + 1));
   temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base))
  quicksort_do_loop
 (normal_ret_assert 
   (EX left:Z, EX mid:Z, EX right:Z, EX bl: list val,
    PROP (lo < left <= hi; lo <= right < hi; lo <= mid < hi;
       (left=right+1 \/ left=right+2)%Z;
       Forall (f_cmp Cge (Znth mid bl)) (sublist lo left bl);
       Forall (f_cmp Cle (Znth mid bl)) (sublist (right+1) (hi+1) bl);
       Permutation al bl;
       sorted (f_cmp Cle) (sublist 0 lo bl);
       sorted (f_cmp Cle) (sublist (hi + 1) N bl);
       0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl);
       hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl))  (sublist 0 (hi + 1) bl))
    LOCAL (temp _right_ptr (dnth base right);
       temp _left_ptr (dnth base left);
       temp _mid (dnth base mid); temp _lo (dnth base lo);
       temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base))).
Proof.
intros.
set (s := quicksort_do_loop); hnf in s; subst s.
abbreviate_semax.
clearbody Delta_specs.
set (M := Z.min _ _) in H0; compute in M; subst M.
assert (Hlen := Permutation_Zlength H6).
forward_loop  (EX left:Z, EX mid:Z, EX right:Z, EX bl: list val, 
   PROP (
   lo < left <= right+1; right < hi; lo <= mid < hi;
   Forall (f_cmp Cge (Znth mid bl)) (sublist lo left bl);
   Forall (f_cmp Cle (Znth mid bl)) (sublist (right+1) (hi+1) bl);
   Permutation al bl;
   sorted (f_cmp Cle) (sublist 0 lo bl);
   sorted (f_cmp Cle) (sublist (hi + 1) N bl);
   0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl);
   hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl))  (sublist 0 (hi + 1) bl))
   LOCAL (temp _left_ptr (dnth base left);
   temp _right_ptr (dnth base right);
   temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)).
{ Exists (lo+1) mid (hi-1) bl.
  entailer!.
  rewrite !sublist_one by rep_lia.
  rewrite Z.sub_add.
  repeat constructor; auto.
}
destruct H2 as [H2 _].
destruct H3 as [_ H3].
clear dependent bl.
clear mid. 
Intros left mid right bl.
assert (H2': 0 <= lo <= mid) by lia.
assert (H3': mid < hi < N) by lia.
clear H2 H3 H6; rename H2' into H2; rename H3'  into H3.
rename H7 into H6; rename H8 into H7; rename H9 into H8;
rename H10 into H9; rename H11 into H10; rename H12 into H11;
rename H13 into H12.
assert (Hdef_bl: Forall def_float bl) by (apply Forall_perm with al; auto).
assert (Hlen := Permutation_Zlength H8).
pose_dnth_base mid.
forward_loop (EX left:Z,
   PROP (lo < left <= right+1; right < hi;
       Forall (f_cmp Cge (Znth mid bl)) (sublist lo left bl))
   LOCAL (temp _left_ptr (dnth base left);
       temp _right_ptr (dnth base right);
       temp _mid (dnth base mid); temp _lo (dnth base lo);
       temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base))
 break:
  (EX left:Z,
   PROP (lo < left <= right+1; right < hi;
       f_cmp Cge (Znth left bl) (Znth mid bl);
       Forall (f_cmp Cge (Znth mid bl)) (sublist lo left bl))
   LOCAL (temp _left_ptr (dnth base left);
       temp _right_ptr (dnth base right);
       temp _mid (dnth base mid); temp _lo (dnth base lo);
       temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)).
-
Exists left; entailer!.
-
clear dependent left.
Intros left.
pose_dnth_base left.
forward.
apply tc_val_tdouble_Znth; auto; lia.
forward.
apply tc_val_tdouble_Znth; auto; lia.
forward_if.
apply typed_true_cmp in H15.
forward.
rewrite dbase_add by (auto; rep_lia).
Exists (left+1).
entailer!.
clear H25 H24 H23 H22 H21 H20 H19 H18 H17 H16.
split.
split; try lia.
assert (f_cmp Cle (Znth mid bl) (Znth (right+1) bl)).
rewrite (sublist_split _ (right+2)) in H7 by lia.
rewrite Forall_app in H7. destruct  H7 as [H7 _].
rewrite sublist_one in H7 by lia. inv H7. auto.
assert (left<>right+1);[|lia].
intro; subst left.
clear - H15 H16.
apply f_cmp_swap in H15.
eapply float_cmp_gt_le_false; eauto.
rewrite (sublist_split _ left) by lia.
rewrite Forall_app; split; auto.
rewrite sublist_one by lia.
repeat constructor; auto.
apply f_cmp_swap in H15.
rewrite f_cmp_ge_gt_eq; auto.
forward.
Exists left.
entailer!.
apply typed_false_cmp in H15; [ | apply Forall_Znth; auto; lia ..].
auto.
-
clear dependent left.
Intros left.
apply f_cmp_swap in H6; simpl in H6.
forward_loop (EX right:Z,
   PROP (
   lo < left <= right+1; right < hi;
   f_cmp Cle (Znth mid bl) (Znth left bl);
   Forall (f_cmp Cle (Znth mid bl)) (sublist (right+1) (hi+1) bl))
   LOCAL (temp _left_ptr (dnth base left);
   temp _right_ptr (dnth base right);
   temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base))
 break:
  (EX right:Z,
   PROP (
   lo < left <= right+1; lo <= right < hi;
   f_cmp Cle (Znth mid bl) (Znth left bl);
   f_cmp Cge (Znth mid bl) (Znth right bl);
   Forall (f_cmp Cle (Znth mid bl)) (sublist (right+1) (hi+1) bl))
   LOCAL (temp _left_ptr (dnth base left);
   temp _right_ptr (dnth base right);
   temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)).
+
Exists right; entailer!.
+
clear dependent right.
Intros right.
pose_dnth_base right.
forward.
apply tc_val_tdouble_Znth; auto; lia.
forward.
apply tc_val_tdouble_Znth; auto; lia.
forward_if.
apply typed_true_cmp in H16.
forward.
rewrite dbase_sub by (auto; rep_lia).
Exists (right-1).
entailer!.
clear H26 H25 H24 H23 H22 H21 H20 H19 H18 H17.
split.
split; try lia.
rewrite Z.sub_add.
destruct (zeq left (right+1)); try lia.
subst left. elimtype False.
rewrite (sublist_split lo right) in H14 by lia.
rewrite Forall_app in H14. destruct  H14 as [_ H14].
rewrite sublist_one in H14 by lia. inv H14.
eapply f_cmp_lt_ge_false; eauto.
rewrite Z.sub_add.
rewrite (sublist_split _ (right+1)) by lia.
rewrite Forall_app; split; auto.
rewrite sublist_one by lia.
repeat constructor; auto.
rewrite f_cmp_le_lt_eq; auto.
forward.
Exists right.
entailer!.
apply typed_false_cmp in H16; [ | apply Forall_Znth; auto; lia ..].
auto.
+
destruct H2 as [H2 H2'].
destruct H3 as [H3' H3].
clear dependent right.
Intros right.
pose_dnth_base left.
pose_dnth_base right.
forward_if (EX left:Z, EX mid:Z, EX right:Z, EX bl: list val, 
   PROP (
   lo < left <= right+1; lo-1 <= right < hi; lo <= mid < hi;
   Forall (f_cmp Cge (Znth mid bl)) (sublist lo (Z.min left hi) bl);
   Forall (f_cmp Cle (Znth mid bl)) (sublist (Z.max lo (right+1)) (hi+1) bl);
   Permutation al bl;
   sorted (f_cmp Cle) (sublist 0 lo bl);
   sorted (f_cmp Cle) (sublist (hi + 1) N bl);
   0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl);
   hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl))  (sublist 0 (hi + 1) bl))
   LOCAL (temp _left_ptr (dnth base left);
   temp _right_ptr (dnth base right);
   temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)).
*
apply test_order_dnth; auto; rep_lia.
*
eapply typed_true_pp in H18; eauto; simpl in H18.
assert (lo < left < right) by lia; clear H18 H4.
pose (bl' := swap_in_list right left bl).
apply semax_seq' with
 (PROP ()
   LOCAL (temp _left_ptr (dnth base left);
   temp _right_ptr (dnth base right);
   temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl' base)).
abbreviate_semax.
match goal with |- semax _ ?Pre _ ?Post => 
forward_loop Pre continue:Post.(RA_normal) end;
  [solve [auto] | | forward; apply ENTAIL_refl ].
forward.
apply tc_val_tdouble_Znth; auto; lia.
forward.
apply tc_val_tdouble_Znth; auto; lia.
forward.
forward.
rewrite !def_float_f2f by (apply Forall_Znth; auto; lia).
entailer!.
subst MORE_COMMANDS; unfold abbreviate.
simpl reptype in *.
forward_if (EX mid:Z, 
  PROP (lo <= mid < hi; 
      f_cmp Cle (Znth left bl') (Znth mid bl');
      Forall (f_cmp Cge (Znth mid bl')) (sublist lo left bl');
      f_cmp Cle (Znth mid bl') (Znth right bl');
      Forall (f_cmp Cle (Znth mid bl'))
                  (sublist (right + 1) (hi + 1) bl'))
   LOCAL (temp _left_ptr (dnth base left);
   temp _right_ptr (dnth base right);
   temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl' base)).
--
apply test_eq_dnth; try rep_lia; auto.
--
forward.
replace base with (dnth base 0) at 1
 by (make_Vptr base; unfold dnth; simpl; normalize).
rewrite dbase_add by (auto; rep_lia).
eapply typed_true_pp in H4; eauto; simpl in H4.
rewrite Z.add_0_l.
Exists right.
entailer!.
clear H25 H24 H23 H22 H21 H20 H18.
subst bl'.
rewrite Znth_swap_in_list2 by lia.
rewrite Znth_swap_in_list1 by lia.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by lia; auto.
rewrite f_cmp_le_lt_eq. right.
apply float_cmp_eq_refl. apply Forall_Znth; auto; lia.
rewrite sublist_swap_in_list by lia; auto.
--
eapply typed_false_pp in H4; eauto; simpl in H4.
forward_if.
++
apply test_eq_dnth; try rep_lia; auto.
++
eapply typed_true_pp in H18; eauto; simpl in H18.
forward.
replace base with (dnth base 0) at 1
 by (make_Vptr base; unfold dnth; simpl; normalize).
rewrite dbase_add by (auto; rep_lia).
rewrite Z.add_0_l.
Exists left.
entailer!.
clear H26 H25 H24 H23 H22 H21 H20.
subst bl'.
rewrite Znth_swap_in_list2 by lia.
rewrite Znth_swap_in_list1 by lia.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by lia; auto.
auto.
rewrite sublist_swap_in_list by lia; auto.
++
forward.
eapply typed_false_pp in H18; eauto; simpl in H18.
Exists mid.
entailer!.
clear H27 H26 H25 H24 H23 H22 H21 H20.
subst bl'.
rewrite Znth_swap_in_list2 by lia.
rewrite Znth_swap_in_list1 by lia.
rewrite Znth_swap_in_list_other by lia.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by lia; auto.
auto.
rewrite sublist_swap_in_list by lia; auto.
--
clear dependent mid.
Intros mid.
forward.
forward.
rewrite dbase_sub by (auto; rep_lia).
rewrite dbase_add by (auto; rep_lia).
Exists (left+1) mid (right-1) bl'.
entailer!.
clear H25 H24 H23 H22 H21 H20 H18 H15.
assert (Permutation bl bl')
  by (apply Permutation_swap2; lia).
pose proof (Permutation_Zlength H15).
split3.
destruct (zlt left hi).
rewrite Z.min_l by lia.
rewrite (sublist_split _ left) by lia.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by lia.
repeat constructor.
apply f_cmp_swap in H6; auto.
rewrite Z.min_r by lia.
assert (left=hi) by lia.
subst left.
auto.
rewrite Z.sub_add.
destruct (zlt right lo).
rewrite Z.max_l by lia.
assert (right=lo-1) by lia.
subst right.
rewrite Z.sub_add in H14.
auto.
rewrite Z.max_r by lia.
rewrite (sublist_split _ (right+1)) by lia.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by lia.
repeat constructor.
auto.
split.
apply Permutation_trans with bl; auto.
split; [ | split3].
subst bl'. rewrite sublist_swap_in_list by lia. auto.
subst bl'. rewrite sublist_swap_in_list by lia. auto.
subst bl'.
intros.
rewrite Znth_swap_in_list_other by lia.
eapply Forall_perm; try apply H11; auto.
rewrite sublist_swap_in_list'; try lia; auto.
apply Permutation_swap2; list_solve.
subst bl'.
intros.
rewrite Znth_swap_in_list_other by lia.
eapply Forall_perm; try apply H12; auto.
rewrite sublist_swap_in_list'; try lia; auto.
apply Permutation_swap2; list_solve.
*
eapply typed_false_pp in H18; eauto; simpl in H18.
forward_if.
++
apply test_eq_dnth; try rep_lia; auto.
++
eapply typed_true_pp in H19; eauto; simpl in H19.
subst right.
forward.
forward.
forward.
rewrite dbase_add by (auto; rep_lia).
rewrite dbase_sub by (auto; rep_lia).
Exists (left+1) mid (left-1) bl.
entailer!.
rewrite Z.sub_add.
clear H26 H25 H24 H23 H22 H21 H20 H19 H18 H17.
split.
rewrite (sublist_split _ left) by lia.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by lia; repeat constructor; auto.
rewrite (sublist_split _ (left+1)) by lia.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by lia; repeat constructor; auto.
++
eapply typed_false_pp in H19; eauto; simpl in H19.
forward.
Exists left mid right bl.
entailer!.
clear H27 H26 H25 H24 H23 H22 H21 H20.
assert (left = right+1) by lia.
subst left.
clear H19 H18 H4.
rewrite Z.min_l by lia.
rewrite Z.max_r by lia.
split; auto.
*
clear dependent left.
clear dependent right.
clear dependent bl.
clear dependent mid.
Intros left mid right bl.
pose_dnth_base left.
pose_dnth_base right.
forward_if.
apply test_order_dnth; try rep_lia; auto.
eapply typed_true_pp in H16; eauto; simpl in H16.
forward.
Exists left mid right bl.
entailer!.
autorewrite with sublist in H7,H8.
auto.
forward.
eapply typed_false_pp in H16; eauto; simpl in H16.
Exists left mid right bl.
entailer!.
autorewrite with sublist in H7,H8.
auto.
Qed.

