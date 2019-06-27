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
  rewrite !sublist_one by rep_omega.
  rewrite Z.sub_add.
  repeat constructor; auto.
}
destruct H2 as [H2 _].
destruct H3 as [_ H3].
clear dependent bl.
clear mid. 
Intros left mid right bl.
assert (H2': 0 <= lo <= mid) by omega.
assert (H3': mid < hi < N) by omega.
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
apply tc_val_tdouble_Znth; auto; omega.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward_if.
apply typed_true_cmp in H15.
forward.
rewrite dbase_add by (auto; rep_omega).
Exists (left+1).
entailer!.
clear H25 H24 H23 H22 H21 H20 H19 H18 H17 H16.
split.
split; try omega.
assert (f_cmp Cle (Znth mid bl) (Znth (right+1) bl)).
rewrite (sublist_split _ (right+2)) in H7 by omega.
rewrite Forall_app in H7. destruct  H7 as [H7 _].
rewrite sublist_one in H7 by omega. inv H7. auto.
assert (left<>right+1);[|omega].
intro; subst left.
clear - H15 H16.
apply f_cmp_swap in H15.
eapply float_cmp_gt_le_false; eauto.
rewrite (sublist_split _ left) by omega.
rewrite Forall_app; split; auto.
rewrite sublist_one by omega.
repeat constructor; auto.
apply f_cmp_swap in H15.
rewrite f_cmp_ge_gt_eq; auto.
forward.
Exists left.
entailer!.
apply typed_false_cmp in H15; [ | apply Forall_Znth; auto; omega ..].
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
apply tc_val_tdouble_Znth; auto; omega.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward_if.
apply typed_true_cmp in H16.
forward.
rewrite dbase_sub by (auto; rep_omega).
Exists (right-1).
entailer!.
clear H26 H25 H24 H23 H22 H21 H20 H19 H18 H17.
split.
split; try omega.
rewrite Z.sub_add.
destruct (zeq left (right+1)); try omega.
subst left. elimtype False.
rewrite (sublist_split lo right) in H14 by omega.
rewrite Forall_app in H14. destruct  H14 as [_ H14].
rewrite sublist_one in H14 by omega. inv H14.
eapply f_cmp_lt_ge_false; eauto.
rewrite Z.sub_add.
rewrite (sublist_split _ (right+1)) by omega.
rewrite Forall_app; split; auto.
rewrite sublist_one by omega.
repeat constructor; auto.
rewrite f_cmp_le_lt_eq; auto.
forward.
Exists right.
entailer!.
apply typed_false_cmp in H16; [ | apply Forall_Znth; auto; omega ..].
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
apply test_order_dnth; auto; rep_omega.
*
eapply typed_true_pp in H18; eauto; simpl in H18.
assert (lo < left < right) by omega; clear H18 H4.
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
apply tc_val_tdouble_Znth; auto; omega.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward.
forward.
rewrite !def_float_f2f by (apply Forall_Znth; auto; omega).
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
apply test_eq_dnth; try rep_omega; auto.
--
forward.
replace base with (dnth base 0) at 1
 by (make_Vptr base; unfold dnth; simpl; normalize).
rewrite dbase_add by (auto; rep_omega).
eapply typed_true_pp in H4; eauto; simpl in H4.
rewrite Z.add_0_l.
Exists right.
entailer!.
clear H25 H24 H23 H22 H21 H20 H18.
subst bl'.
rewrite Znth_swap_in_list2 by omega.
rewrite Znth_swap_in_list1 by omega.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by omega; auto.
rewrite f_cmp_le_lt_eq. right.
apply float_cmp_eq_refl. apply Forall_Znth; auto; omega.
rewrite sublist_swap_in_list by omega; auto.
--
eapply typed_false_pp in H4; eauto; simpl in H4.
forward_if.
++
apply test_eq_dnth; try rep_omega; auto.
++
eapply typed_true_pp in H18; eauto; simpl in H18.
forward.
replace base with (dnth base 0) at 1
 by (make_Vptr base; unfold dnth; simpl; normalize).
rewrite dbase_add by (auto; rep_omega).
rewrite Z.add_0_l.
Exists left.
entailer!.
clear H26 H25 H24 H23 H22 H21 H20.
subst bl'.
rewrite Znth_swap_in_list2 by omega.
rewrite Znth_swap_in_list1 by omega.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by omega; auto.
auto.
rewrite sublist_swap_in_list by omega; auto.
++
forward.
eapply typed_false_pp in H18; eauto; simpl in H18.
Exists mid.
entailer!.
clear H27 H26 H25 H24 H23 H22 H21 H20.
subst bl'.
rewrite Znth_swap_in_list2 by omega.
rewrite Znth_swap_in_list1 by omega.
rewrite Znth_swap_in_list_other by omega.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by omega; auto.
auto.
rewrite sublist_swap_in_list by omega; auto.
--
clear dependent mid.
Intros mid.
forward.
forward.
rewrite dbase_sub by (auto; rep_omega).
rewrite dbase_add by (auto; rep_omega).
Exists (left+1) mid (right-1) bl'.
entailer!.
clear H25 H24 H23 H22 H21 H20 H18 H15.
assert (Permutation bl bl')
  by (apply Permutation_swap2; omega).
pose proof (Permutation_Zlength H15).
split3.
destruct (zlt left hi).
rewrite Z.min_l by omega.
rewrite (sublist_split _ left) by omega.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by omega.
repeat constructor.
apply f_cmp_swap in H6; auto.
rewrite Z.min_r by omega.
assert (left=hi) by omega.
subst left.
auto.
rewrite Z.sub_add.
destruct (zlt right lo).
rewrite Z.max_l by omega.
assert (right=lo-1) by omega.
subst right.
rewrite Z.sub_add in H14.
auto.
rewrite Z.max_r by omega.
rewrite (sublist_split _ (right+1)) by omega.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by omega.
repeat constructor.
auto.
split.
apply Permutation_trans with bl; auto.
split; [ | split3].
subst bl'. rewrite sublist_swap_in_list by omega. auto.
subst bl'. rewrite sublist_swap_in_list by omega. auto.
subst bl'.
intros.
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; try apply H11; auto.
rewrite sublist_swap_in_list'; try omega; auto.
apply Permutation_swap2; list_solve.
subst bl'.
intros.
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; try apply H12; auto.
rewrite sublist_swap_in_list'; try omega; auto.
apply Permutation_swap2; list_solve.
*
eapply typed_false_pp in H18; eauto; simpl in H18.
forward_if.
++
apply test_eq_dnth; try rep_omega; auto.
++
eapply typed_true_pp in H19; eauto; simpl in H19.
subst right.
forward.
forward.
forward.
rewrite dbase_add by (auto; rep_omega).
rewrite dbase_sub by (auto; rep_omega).
Exists (left+1) mid (left-1) bl.
entailer!.
rewrite Z.sub_add.
clear H26 H25 H24 H23 H22 H21 H20 H19 H18 H17.
split.
rewrite (sublist_split _ left) by omega.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by omega; repeat constructor; auto.
rewrite (sublist_split _ (left+1)) by omega.
rewrite Forall_app; split; auto.
rewrite sublist_len_1 by omega; repeat constructor; auto.
++
eapply typed_false_pp in H19; eauto; simpl in H19.
forward.
Exists left mid right bl.
entailer!.
clear H27 H26 H25 H24 H23 H22 H21 H20.
assert (left = right+1) by omega.
subst left.
clear H19 H18 H4.
rewrite Z.min_l by omega.
rewrite Z.max_r by omega.
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
apply test_order_dnth; try rep_omega; auto.
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


Lemma sorted_le_last:
 forall (i j: Z) (bl: list val), i<j -> 0<= i -> j <= Zlength bl ->
   Forall def_float bl ->
   sorted (f_cmp Cle) (sublist i j bl) ->
   Forall (f_cmp Cge (Znth (j-1) bl)) (sublist i j bl).
Proof.
intros.
rewrite (sublist_split i (j-1)) in * by omega.
rewrite Forall_app.
split.
2:{ rewrite sublist_one by omega; repeat constructor.
    change Cge with (swap_comparison Cle).
    apply f_cmp_swap.
    apply f_le_refl. apply Forall_Znth; auto; omega.
}
rewrite (sublist_split _ j j) in H3 by omega.
rewrite (sublist_one (j-1) j) in H3 by omega.
apply sorted_app_e3 in H3.
destruct H3 as [_ [_ [? ?]]].
eapply Forall_impl; try apply H3.
simpl; intros.
apply f_cmp_swap in H5; auto.
apply f_cmp_le_trans.
Qed.


Lemma sorted_ge_first:
 forall (i j: Z) (bl: list val), i<j -> 0<= i -> j <= Zlength bl ->
   Forall def_float bl ->
   sorted (f_cmp Cle) (sublist i j bl) ->
   Forall (f_cmp Cle (Znth i bl)) (sublist i j bl).
Proof.
intros.
rewrite (sublist_split i (i+1)) in * by omega.
rewrite Forall_app.
split.
{  rewrite sublist_one by omega; repeat constructor.
    change Cge with (swap_comparison Cle).
    apply f_le_refl. apply Forall_Znth; auto; omega.
}
rewrite (sublist_split i i) in H3 by omega.
rewrite (sublist_one i (i+1)) in H3 by omega.
rewrite app_ass in H3.
apply sorted_app_e3 in H3.
destruct H3 as [_ [_ [? ?]]].
auto.
apply f_cmp_le_trans.
Qed.

Lemma body_quicksort_while_part2:
forall (Espec : OracleKind) (base : val) (al : list val) 
  (lo mid hi : Z) (bl : list val),
Forall def_float al ->
let N := Zlength al in
0 < N <= Z.min Int.max_signed (Ptrofs.max_signed / 8) ->
isptr base ->
0 <= lo <= mid ->
mid < hi < N ->
f_cmp Cle (Znth lo bl) (Znth mid bl) ->
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
  (PROP ( )
   LOCAL (temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base))
  quicksort_while_body_part2
  (normal_ret_assert
     (EX a : Z * Z * list val,
      PROP (0 <= fst (fst a) < N; 0 <= snd (fst a) < N;
      Permutation al (snd a);
      sorted (f_cmp Cle) (sublist 0 (fst (fst a)) (snd a));
      sorted (f_cmp Cle)
        (sublist (snd (fst a) + 1) N (snd a));
      0 < fst (fst a) ->
      Forall (f_cmp Cle (Znth (fst (fst a) - 1) (snd a)))
        (sublist (fst (fst a)) N (snd a));
      snd (fst a) + 1 < N ->
      Forall (f_cmp Cge (Znth (snd (fst a) + 1) (snd a)))
        (sublist 0 (snd (fst a) + 1) (snd a));
      fst (fst a) <= snd (fst a) + 1)
      LOCAL (temp _lo (dnth base (fst (fst a)));
      temp _hi (dnth base (snd (fst a))))
      SEP (data_at Ews (tarray tdouble N) (snd a) base))%assert).
Proof.
intros.
set (s := quicksort_while_body_part2); hnf in s; subst s.
abbreviate_semax.
set (M := Z.min _ _) in H0; compute in M; subst M.
pose_dnth_base lo.
pose_dnth_base mid.
pose_dnth_base hi.
pose proof (Permutation_Zlength H6).
forward.
forward.
rewrite dbase_add by (auto; rep_omega).
rewrite dbase_sub by (auto; rep_omega).
apply f_cmp_swap in H4; simpl in H4.
eapply semax_seq'.
apply forward_quicksort_do_loop; auto.
destruct H2 as [H2 H2'].
destruct H3 as [H3' H3].
clear dependent mid.
clear dependent bl.
Intros left mid right bl.
subst MORE_COMMANDS; unfold abbreviate.
assert (Hlen := Permutation_Zlength H10).
assert (Hdef_bl: Forall def_float bl) by (apply Forall_perm with al; auto).
forward_if.
-
apply andp_right; apply denote_tc_samebase_dnth; auto.
-
clear H17.  (* we don't actually care! *)
forward_call (dnth base left, hi-left+1, sublist left (hi+1) bl).
replace (force_val (sem_sub_pp tdouble (dnth base hi) (dnth base left)))
     with (Vint (Int.repr (hi-left))).
2:{
make_Vptr base.
unfold sem_sub_pp, dnth; simpl.
rewrite if_true by auto.
normalize.
f_equal.
rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted.
normalize.
unfold Ptrofs.divs.
normalize.
rewrite <- Z.mul_sub_distr_l.
rewrite !Ptrofs.signed_repr by rep_omega.
f_equal.
rewrite Z.mul_comm, Z.quot_mul by omega.
auto.
}
apply andp_right.
entailer!.
apply denote_tc_samebase_dnth; auto.
apply prop_right; simpl.
make_Vptr base; unfold dnth, sem_sub_pp; simpl.
rewrite if_true by auto.
simpl. f_equal. f_equal.
rewrite !(Ptrofs.add_commut i).
rewrite Ptrofs.sub_shifted.
normalize.
rewrite <- Z.mul_sub_distr_l.
unfold Ptrofs.divs.
normalize.
rewrite !Ptrofs.signed_repr by rep_omega.
f_equal.
rewrite Z.mul_comm.
rewrite Z.quot_mul.
auto.
computable.
{
erewrite (split3_data_at_Tarray Ews tdouble (Zlength al) left (hi+1) bl bl);
 try reflexivity; 
 change (@reptype CompSpecs tdouble) with val in *;
  try rep_omega.
2: compute; auto.
2: autorewrite with sublist; auto.
sep_apply data_at_dnth; try omega.
set (s := Ptrofs.max_signed / 8) in *; compute in s; subst s.
rep_omega.
sep_apply data_at_dnth; try omega.
set (s := Ptrofs.max_signed / 8) in *; compute in s; subst s.
rep_omega.
unfold tarray.
replace (hi-left+1) with (hi+1-left) by omega.
cancel.
}
set (M := Z.min _ _); compute in M; subst M.
autorewrite with sublist.
split3; try omega.
apply Forall_sublist; auto.
Intros bl'.
assert (Hlen_bl' := Permutation_Zlength H17);
  autorewrite with sublist in Hlen_bl'.
forward.
replace base with (dnth base 0) at 1
 by (make_Vptr base; unfold dnth; simpl; normalize).
rewrite dbase_add by (auto; rep_omega). rewrite Z.add_0_l.
Exists (lo, right,
       (sublist 0 left bl ++ bl' ++ sublist (hi+1) N bl)).
unfold fst, snd.
entailer!.
clear H31 H30 H29 H28 H27 H26 H25 H24 H23 H22 H21 H20 H19.
+
split.
eapply Permutation_trans; [apply H10|].
apply Permutation_trans with
 (sublist 0 left bl ++ sublist left (hi+1) bl ++ sublist (hi+1) N bl).
autorewrite with sublist. auto.
apply Permutation_app_head.
apply Permutation_app_tail.
auto.
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
clear - H2 H7 H4 H5 H3 Hlen.
destruct H7.
subst.
autorewrite with sublist. constructor.
rewrite sublist_one; try rep_omega.
constructor.
*
destruct (zlt (hi+1) (Zlength al)).
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
eapply Forall_impl; try apply H19.
intros.
eapply f_cmp_swap in H20; auto.
++ 
apply sorted_ge_first; auto; omega.
--
assert (hi+1 = Zlength al) by omega.
clear g.
autorewrite with sublist.
auto.
*
rewrite (sublist_split lo (right+1)) in H8 by omega.
rewrite Forall_app in H8; destruct H8.
eapply Forall_impl; try apply H19.
intros.
apply f_cmp_swap in H20; auto.
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
specialize (H15 H19).
eapply Forall_perm; try apply H15.
rewrite sublist_app; autorewrite with sublist; try omega.
rewrite sublist_app; autorewrite with sublist; try omega.
rewrite (sublist_split lo left (Zlength al)) by omega.
rewrite (sublist_split left (hi+1)) by omega.
apply Permutation_app_head.
apply Permutation_app.
rewrite (sublist_same 0) by omega.
auto.
replace (N - left - Zlength bl' + (hi+1)) with (Zlength al) by omega.
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
intros. apply f_cmp_swap in H7; simpl in H7.
change Cge with (swap_comparison Cle).
apply f_cmp_swap.
eapply f_cmp_le_trans; try apply H7.
assert (Forall (f_cmp Cle (Znth mid bl)) bl')
  by (eapply Forall_perm; try apply H17; eauto).
apply (Forall_Znth (f_cmp Cle (Znth mid bl))); auto; omega.
apply (@Forall_impl _ (f_cmp Cge (Znth (lo-1) bl))).

intros. apply f_cmp_swap in H7; simpl in H7.
change Cge with (swap_comparison Cle).
apply f_cmp_swap.
eapply f_cmp_le_trans; try apply H7.
replace (Znth mid bl) with (Znth (mid-lo) (sublist lo (Zlength al) bl))
  by (autorewrite with sublist; auto).
apply (Forall_Znth (f_cmp _ _)); auto.
autorewrite with sublist; omega.
apply sorted_le_last; auto; omega.
---
autorewrite with sublist. constructor.
**
eapply Forall_impl; [ | apply H8].
intros. apply f_cmp_swap in H7; simpl in H7.
change Cge with (swap_comparison Cle).
apply f_cmp_swap.
eapply f_cmp_le_trans; try apply H7.
assert (Forall (f_cmp Cle (Znth mid bl)) bl')
  by (eapply Forall_perm; try apply H17; eauto).
apply (Forall_Znth (f_cmp Cle (Znth mid bl))); auto; omega.
++
rewrite (sublist_split 0 lo) by omega.
rewrite Forall_app; split.
rewrite (sublist_split _ (right+2)) in H9 by omega.
rewrite Forall_app in H9; destruct H9.
rewrite sublist_one in H7 by omega.
inv H7. 
apply Forall_impl with (f_cmp Cge (Znth mid bl)).
intros. apply f_cmp_swap in H7; simpl in H7.
change Cge with (swap_comparison Cle).
apply f_cmp_swap.
eapply f_cmp_le_trans; try apply H7.
auto.
destruct (zlt 0 lo); [ | autorewrite with sublist; constructor].
apply sorted_le_last in H12; auto; try omega.
eapply Forall_impl; try apply H12.
simpl; intros.  
apply f_cmp_swap in H7; simpl in H7.
change Cge with (swap_comparison Cle).
apply f_cmp_swap.
eapply f_cmp_le_trans; try apply H7.
replace (Znth mid bl) with (Znth (mid-lo) (sublist lo (Zlength al) bl))
  by (autorewrite with sublist; auto).
eapply (Forall_Znth (f_cmp Cle _)); try apply  H15; auto; try omega.
autorewrite with sublist; omega.
rewrite (sublist_split lo (right+1)) in H8 by omega.
rewrite Forall_app in H8; destruct H8 as [H8 _].
eapply Forall_impl; try apply H8.
intros.
change Cge with (swap_comparison Cle).
apply f_cmp_swap.
apply f_cmp_swap in H7.
eapply f_cmp_le_trans; try apply H7.
rewrite (sublist_split _ (right+2)) in H9 by omega.
rewrite Forall_app in H9; destruct H9 as [H9 _].
rewrite sublist_one in H9 by omega. inv H9; auto.
+
admit.
-
clear H17.  (* we don't actually care! *)
admit.
Admitted.

Lemma calculate_midpoint:
  forall N base lo hi,
0 < N <= 268435455 ->
isptr base ->
0 <= lo < N ->
0 <= hi < N ->
lo < hi ->
force_val
  (sem_binary_operation' Oadd (tptr tdouble) tint
     (dnth base lo)
     (eval_binop Oshr tint tint
        (eval_binop Osub (tptr tdouble) (tptr tdouble)
           (dnth base hi) (dnth base lo)) 
        (Vint (Int.repr 1)))) = dnth base (lo + (hi - lo) / 2).
Proof.
intros.
 symmetry.
 simpl. unfold dnth, sem_shift_ii, sem_sub_pp, sem_add_ptr_int. simpl.
    unfold sem_add_ptr_int, Cop.sem_add_ptr_int. simpl.
    make_Vptr base; simpl. rewrite if_true by auto. simpl.
    f_equal. rewrite Ptrofs.add_assoc. f_equal.
    normalize. f_equal.
    rewrite <- Z.mul_add_distr_l. f_equal.
    unfold Int.shr.
    rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted.
    normalize.
    unfold Ptrofs.divs. normalize.
    rewrite <- Z.mul_sub_distr_l.
    rewrite (Int.signed_repr hi) by rep_omega.
    rewrite (Int.signed_repr lo) by rep_omega.
    rewrite (Ptrofs.signed_repr 8) by rep_omega.
    rewrite (Ptrofs.signed_repr) by rep_omega.
    rewrite Z.mul_comm, Z.quot_mul by omega.
    rewrite Int.signed_repr. f_equal.
    rewrite (Int.signed_repr (hi-lo)) by rep_omega.
    rewrite Z.shiftr_div_pow2 by omega. change (2^1) with 2.
    rewrite Int.signed_repr. auto.
    split.
    assert (0 <= (hi-lo)/2); [|rep_omega].
    apply Z.div_pos; rep_omega.
    apply Z.div_le_upper_bound; rep_omega.
    split.
    assert (0 <= (hi-lo)/2); [|rep_omega].
    apply Z.div_pos; rep_omega.
    pose proof (mid_in_range lo hi); rep_omega.
Qed.

Lemma body_quicksort_while:
forall (Espec : OracleKind) (base : val) (al : list val) 
  (lo hi : Z) (bl : list val),
Forall def_float al ->
let N := Zlength al in
0 < N <= Z.min Int.max_signed (Ptrofs.max_signed/8) ->
isptr base ->
0 <= lo < N ->
0 <= hi < N ->
Permutation al bl ->
sorted (f_cmp Cle) (sublist 0 lo bl) ->
sorted (f_cmp Cle) (sublist (hi + 1) N bl) ->
(0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl)) ->
(hi + 1 < N ->
 Forall (f_cmp Cge (Znth (hi + 1) bl)) (sublist 0 (hi + 1) bl)) ->
lo < hi ->
lo <= hi+1 ->
semax (func_tycontext f_quicksort Vprog Gprog [])
  (PROP ( )
   LOCAL (temp _lo (dnth base lo); temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)) 
  quicksort_while_body
  (normal_ret_assert
     (EX a : Z * Z * list val,
      PROP (0 <= fst (fst a) < N; 0 <= snd (fst a) < N;
      Permutation al (snd a);
      sorted (f_cmp Cle) (sublist 0 (fst (fst a)) (snd a));
      sorted (f_cmp Cle) (sublist (snd (fst a) + 1) N (snd a));
      0 < fst (fst a) ->
      Forall (f_cmp Cle (Znth (fst (fst a) - 1) (snd a)))
        (sublist (fst (fst a)) N (snd a));
      snd (fst a) + 1 < N ->
      Forall (f_cmp Cge (Znth (snd (fst a) + 1) (snd a)))
        (sublist 0 (snd (fst a) + 1) (snd a));
      fst (fst a) <= snd (fst a) + 1)
      LOCAL (temp _lo (dnth base (fst (fst a)));
      temp _hi (dnth base (snd (fst a))))
      SEP (data_at Ews (tarray tdouble N) (snd a) base))).
Proof.
intros.
abbreviate_semax.
set (M := Z.min _ _) in H0.
compute in M. subst M.
assert (Hdef_bl: Forall def_float bl) by (apply Forall_perm with al; auto).
unfold quicksort_while_body.
simpl.
abbreviate_semax.
forward.
entailer!.
auto.
rewrite (calculate_midpoint N) by assumption.
pose proof (mid_in_range lo hi). spec H11; [omega|].
forget (lo+(hi-lo)/2) as mid.
pose_dnth_base mid.
assert (Hlen := Permutation_Zlength H4).
forward.
apply tc_val_tdouble_Znth; auto; omega.
pose_dnth_base lo.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward_if (EX bl: list val, 
   PROP (f_cmp Cle (Znth lo bl) (Znth mid bl); Permutation al bl;
   sorted (f_cmp Cle) (sublist 0 lo bl);
   sorted (f_cmp Cle) (sublist (hi + 1) N bl);
   0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl);
   hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl))  (sublist 0 (hi + 1) bl))
   LOCAL (temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)).
- (* then-clause *)
match goal with |- semax _ ?Pre _ ?Post => 
forward_loop Pre continue:Post.(RA_normal) end;
  [solve [auto] | | forward; apply ENTAIL_refl ].
apply typed_true_cmp in H14.
assert (lo<mid). {
 destruct (zeq lo mid); try omega.
 clear - H14 e. subst lo. apply f_lt_irrefl in H14. contradiction.
}
forward.
forward.
forward.
forward.
rewrite !def_float_f2f by (apply Forall_Znth; auto; omega).
change (upd_Znth lo _ _) with (swap_in_list lo mid bl).
Exists (swap_in_list lo mid bl).
entailer!.
clear H22 H21 H20 H19 H18.
autorewrite with sublist.
split.
rewrite Znth_swap_in_list1 by omega.
rewrite Znth_swap_in_list2 by omega.
rewrite f_cmp_le_lt_eq. auto.
split.
eapply Permutation_trans; [eassumption| apply Permutation_swap2; omega].
rewrite !sublist_swap_in_list by omega.
split3; auto.
split; intro.
+
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; [ | apply (H7 H18)].
rewrite sublist_swap_in_list' by omega.
apply Permutation_swap2; try list_solve.
+
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; [ | apply (H8 H18)].
rewrite sublist_swap_in_list' by omega.
apply Permutation_swap2; try list_solve.
-
forward.
Exists bl.
entailer!.
apply typed_false_cmp in H14.
simpl in H14.
apply f_cmp_swap in H14. auto.
apply Forall_Znth; auto; omega.
apply Forall_Znth; auto; omega.
-
clear dependent bl.
Intros bl.
assert (Hdef_bl: Forall def_float bl) by (apply Forall_perm with al; auto).
pose proof (Permutation_Zlength H5).
pose_dnth_base hi.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward_if (EX bl: list val, 
   PROP (f_cmp Cle (Znth lo bl) (Znth mid bl); 
             f_cmp Cle (Znth mid bl) (Znth hi bl); 
             Permutation al bl;
   sorted (f_cmp Cle) (sublist 0 lo bl);
   sorted (f_cmp Cle) (sublist (hi + 1) N bl);
   0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl);
   hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl))  (sublist 0 (hi + 1) bl))
   LOCAL (temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)).
+
apply typed_true_cmp in H17.
apply semax_seq' with (EX bl: list val, 
   PROP (f_cmp Cle (Znth mid bl) (Znth hi bl); 
             f_cmp Cle (Znth lo bl) (Znth mid bl) \/
             f_cmp Cle (Znth lo bl) (Znth hi bl);
             Permutation al bl;
   sorted (f_cmp Cle) (sublist 0 lo bl);
   sorted (f_cmp Cle) (sublist (hi + 1) N bl);
   0 < lo -> Forall (f_cmp Cle (Znth (lo - 1) bl)) (sublist lo N bl);
   hi + 1 < N -> Forall (f_cmp Cge (Znth (hi + 1) bl))  (sublist 0 (hi + 1) bl))
   LOCAL (temp _mid (dnth base mid); temp _lo (dnth base lo);
   temp _hi (dnth base hi))
   SEP (data_at Ews (tarray tdouble N) bl base)).
*
abbreviate_semax.
match goal with |- semax _ ?Pre _ ?Post => 
forward_loop Pre continue:Post.(RA_normal) end;
  [solve [auto] | | forward; apply ENTAIL_refl ].
forward.
forward.
forward.
forward.
rewrite !def_float_f2f by (apply Forall_Znth; auto; omega).
Exists (swap_in_list hi mid bl).
entailer!.
clear H24 H23 H22 H21 H20 H19 H18.
split3.
rewrite Znth_swap_in_list1 by omega.
rewrite Znth_swap_in_list2 by omega.
rewrite f_cmp_le_lt_eq. auto.
rewrite Znth_swap_in_list1 by omega.
rewrite Znth_swap_in_list2 by omega.
destruct (zeq lo mid).
subst.
rewrite Znth_swap_in_list2 by omega.
left.
apply f_le_refl; auto. apply Forall_Znth; auto; omega.
rewrite Znth_swap_in_list_other by omega.
auto.
split3; [ | | split]; auto.
eapply Permutation_trans; [eassumption| ].
apply Permutation_swap2; omega.
rewrite sublist_swap_in_list by omega; auto.
rewrite sublist_swap_in_list by omega; auto.
split; intro.
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; try apply (H8 H18).
rewrite sublist_swap_in_list' by omega.
apply Permutation_swap2; try list_solve.
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; try apply (H14 H18).
rewrite sublist_swap_in_list' by omega.
apply Permutation_swap2; try list_solve.
*
clear dependent bl.
Intros bl.
rename H5 into H4'.
rename H6 into H5. rename H7 into H6. rename H8 into H7.
assert (Hdef_bl: Forall def_float bl) by (apply Forall_perm with al; auto).
pose proof (Permutation_Zlength H5).
abbreviate_semax.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward_if.
--
apply typed_true_cmp in H17.
match goal with |- semax _ ?Pre _ ?Post => 
forward_loop Pre continue:Post.(RA_normal) end;
  [solve [auto] | | forward; apply ENTAIL_refl ].
forward.
forward.
forward.
forward.
rewrite !def_float_f2f by (apply Forall_Znth; auto; omega).
Exists (swap_in_list lo mid bl).
entailer!.
clear H24 H23 H22 H21 H20 H18 H19.
assert (lo<mid). {
 destruct (zeq lo mid); try omega.
 clear - H17 e. subst lo. apply f_lt_irrefl in H17. contradiction.
}
rewrite Znth_swap_in_list1 by omega.
rewrite Znth_swap_in_list2 by omega.
rewrite Znth_swap_in_list_other by omega.
split3; auto.
rewrite f_cmp_le_lt_eq. auto.
destruct H4'; auto.
eapply f_cmp_le_trans; try eassumption.
split3; [ | | split]; auto.
eapply Permutation_trans; [eassumption| ].
apply Permutation_swap2; try omega.
rewrite sublist_swap_in_list by omega; auto.
rewrite sublist_swap_in_list by omega; auto.
split; intro.
++
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; try apply (H14 H19).
rewrite sublist_swap_in_list' by omega.
apply Permutation_swap2; try list_solve.
++
rewrite Znth_swap_in_list_other by omega.
eapply Forall_perm; try apply (H15 H19).
rewrite sublist_swap_in_list' by omega.
apply Permutation_swap2; try list_solve.
--
forward.
Exists bl.
entailer!.
apply typed_false_cmp in H17.
simpl in H17.
apply f_cmp_swap in H17. auto.
apply Forall_Znth; auto; omega.
apply Forall_Znth; auto; omega.
+
forward.
Exists bl.
entailer!.
apply typed_false_cmp in H17.
simpl in H17.
apply f_cmp_swap in H17. auto.
apply Forall_Znth; auto; omega.
apply Forall_Znth; auto; omega.
+
clear dependent bl.
Intros bl.
apply body_quicksort_while_part2; auto; omega.
Qed.

Lemma body_quicksort:  semax_body Vprog Gprog f_quicksort quicksort_spec.
Proof.
start_function.
rename H0 into H0''.
assert (H0' := Z.min_glb_r _ _ _ H0'').
assert (H0 := Z.min_glb_l _ _ _ H0'').
forward_if.
forward.
Exists al.
entailer!.
destruct al; autorewrite with sublist in H2; try rep_omega.
constructor.
assert (0 < N <= Int.max_signed) by rep_omega.
clear H0 H2.
assert_PROP (isptr base) by entailer!.
forward.
forward.
replace  (force_val
               (sem_binary_operation' Osub (tptr tdouble) tint
                  (eval_binop Oadd (tptr tdouble) tint base
                     (Vint (Int.repr N))) (Vint (Int.repr 1))))
  with (dnth base (N-1)).
2:{
  make_Vptr base.
  unfold dnth.
  simpl. f_equal. rewrite ptrofs_of_ints_unfold.
  rewrite Ptrofs.sub_add_opp.
  normalize.
  rewrite Ptrofs.add_assoc. f_equal.
  change (Ptrofs.neg (Ptrofs.repr 8)) with (Ptrofs.repr (-8)).
  normalize. f_equal. omega.
}
deadvars!.
subst N.
set (N := Zlength al) in *.
forward_while (EX lo:Z, EX hi:Z, EX bl: list val,
                       PROP(0 <= lo < N; 0 <= hi < N;Permutation al bl;
                                sorted (f_cmp Cle) (sublist 0 lo bl);
                                sorted (f_cmp Cle) (sublist (hi+1) N bl);
                                0<lo -> Forall (f_cmp Cle (Znth (lo-1) bl))
                                                    (sublist lo N bl);
                                hi+1<N -> Forall (f_cmp Cge (Znth (hi+1) bl))
                                                    (sublist 0 (hi+1) bl);
                                lo <= hi+1)
                       LOCAL(temp _lo (dnth base lo); temp _hi (dnth base hi))
                       SEP(data_at Ews (tarray tdouble N) bl base)).
-
Exists 0 (N-1) al.
entailer!.
autorewrite with sublist.
split3.
constructor.
constructor.
unfold dnth. clear - H0. make_Vptr base. simpl. f_equal.
  rewrite ptrofs_of_ints_unfold. normalize.
-
entailer!.
assert (0 <= lo <= Zlength al) by omega.
assert (0 <= hi <= Zlength al) by omega.
auto with valid_pointer.
-
pose_dnth_base lo. rename H10 into Hlo.
pose_dnth_base hi. rename H10 into Hhi.
rewrite <- (force_sem_cmp_pp Clt) in HRE
  by (apply isptr_dnth; auto).
eapply typed_true_pp with (N:=N) in HRE; 
  eauto; try split; try assumption; try omega; simpl in HRE.
rename HRE into H10.
change Delta with (func_tycontext f_quicksort Vprog Gprog nil).
change (Ssequence _ _) with quicksort_while_body.
make_sequential.
subst POSTCONDITION; unfold abbreviate.
autorewrite with ret_assert.
apply body_quicksort_while; auto.
split. omega.
apply Z.min_glb; auto. omega.
-
forward.
assert_PROP (lo >= hi). {
entailer!.
unfold compare_pp, dnth in HRE.
destruct base; simpl in HRE; try solve [inv HRE].
rewrite if_true in HRE by auto.
rewrite !ptrofs_of_ints_unfold in HRE.
normalize in HRE.
unfold Ptrofs.ltu in HRE.
destruct (zlt _ _) in HRE; inv HRE.
rewrite <- H13 in *.
clear H13 al H1 H4 H13 H9 H10 H7 H8 H5 H6 H0.
rewrite <- (Ptrofs.repr_unsigned i) in g.
normalize in g.
destruct H12 as [? [? [? [? ?]]]].
red in H4.
simpl  sizeof in H4.
rewrite Z.max_r in H4 by rep_omega.
rewrite !Ptrofs.unsigned_repr in g by rep_omega.
omega.
} clear HRE.
Exists bl.
entailer!.
assert (lo=hi \/ lo=hi+1) by omega.
assert (Zlength al = Zlength bl) 
  by (rewrite !Zlength_correct; f_equal; apply Permutation_length; auto).
rewrite H17 in *. 
assert (Hdef_bl: Forall def_float bl). {eapply Forall_perm; try eassumption. }
clear - H16 H7 H8 H5 H6 H H2 Hdef_bl.
destruct H16; subst.
+
assert (hi=0 \/ 0<hi) by omega.
destruct H0.
 *
subst.
autorewrite with sublist in *.
destruct (zlt 1 (Zlength bl)).
specialize (H8 l).
rewrite sublist_one in H8 by omega.
inv H8.
rewrite <- (sublist_same 0 (Zlength bl) bl) by omega.
rewrite (sublist_split _ 1) by omega.
rewrite sublist_one by omega.
apply sorted_app with (Znth 1 bl); auto.
apply f_cmp_le_trans.
constructor.
constructor.
apply (f_cmp_swap _ _ _ H3).
constructor.
{
 clear - H6 l Hdef_bl.
 destruct bl. inv l.
 inv Hdef_bl. clear H1.
 rewrite Zlength_cons in *. change (v::bl) with ([v]++bl) in *.
 autorewrite with sublist in *.
 assert (0 < Zlength bl) by omega. clear l.
 revert H H2; induction H6; intros. 
 constructor. repeat constructor. inv H2.  apply f_le_refl; auto.
 change (Znth 0 (x::y::l)) with x. inv H2.
 constructor.  apply f_le_refl; auto.
 spec IHsorted.
 rewrite Zlength_cons. rep_omega.
 spec IHsorted; auto.
 change (Znth 0 (y::l)) with y in IHsorted.
 clear - H IHsorted.
 forget (y::l) as zl.
 induction IHsorted. constructor. constructor; auto.
 eapply f_cmp_le_trans; eassumption.
}
destruct bl.
constructor.
destruct bl.
constructor.
rewrite !Zlength_cons in g.
rep_omega.
 *
specialize (H7 H0).
destruct (zlt (hi+1) (Zlength bl)).
2:{ assert (hi=Zlength bl \/ hi+1 = Zlength bl) by omega.
    destruct H1. subst. autorewrite with sublist in *. auto.
    autorewrite with sublist in *.
    clear g H6 H2 H H8.
    rewrite sublist_one in H7 by omega. inv H7. clear H4.
    rewrite (sublist_split 0 (hi-1)) in H5 by omega.
    rewrite (sublist_one (hi-1)) in H5 by omega.
    rewrite <- (sublist_same 0 (hi+1)) by omega.
    rewrite (sublist_split 0 (hi-1)) by omega.
    rewrite (sublist_split (hi-1) hi) by omega.
    rewrite (sublist_one (hi-1)) by omega.
    rewrite (sublist_one hi) by omega.
    clear - H5 H3.
    induction (sublist 0 (hi-1) bl). constructor; auto. constructor; auto.
    inv H5. destruct l; inv H1. destruct l; inv H0.
    simpl in IHl. spec IHl; auto. constructor; auto.
    simpl in *. spec IHl; auto. constructor; auto.
}
specialize (H8 l).
rewrite <- (sublist_same 0 (Zlength bl) bl) by omega.
rewrite (sublist_split 0 (hi-1)) by omega.
apply sorted_app with (Znth (hi-1) bl); auto.
apply f_cmp_le_trans.
{
clear - H0 l H5.
rewrite (sublist_split 0 (hi-1)) in H5 by list_solve.
forget (sublist 0 (hi - 1) bl) as al.
induction al. constructor.
simpl in H5.
inv H5.
destruct al. constructor.
inv H2.
destruct al; inv H1.
constructor.
constructor; auto.
}
{
rewrite (sublist_split (hi-1) hi) by rep_omega.
rewrite sublist_one by omega.
rewrite (sublist_split hi (hi+1)) by rep_omega.
rewrite sublist_one by omega.
simpl.
constructor.
rewrite (sublist_split hi (hi+1)) in H7 by rep_omega.
rewrite sublist_one in H7 by rep_omega.
inv H7.
auto.
rewrite (sublist_split 0 (hi-1)) in H8 by omega.
rewrite Forall_app in H8. destruct H8.
rewrite (sublist_split _ hi) in H3 by omega.
rewrite Forall_app in H3. destruct H3.
rewrite sublist_one in H4 by omega.
inv H4. clear H11.
apply f_cmp_swap in H10. simpl in H10.
rewrite (sublist_split _ (hi+2)) in H6|-* by omega.
rewrite sublist_one in * by omega.
clear - H10 H6.
simpl in *.
constructor; auto.
}
rewrite (sublist_split 0 (hi-1)) in H8 by omega.
{
clear - H5 H0 l Hdef_bl.
rewrite (sublist_split 0 (hi-1)) in H5 by omega.
rewrite (sublist_one (hi-1)) in H5 by omega.
clear - H5.
induction (sublist 0 (hi - 1) bl). constructor.
inv H5. destruct l; inv H1.
destruct l; inv H0.
constructor; auto.
constructor; auto.
spec IHl; auto. inv IHl; auto.
apply f_cmp_le_trans with v; auto.
}
rewrite (sublist_split _ hi) by omega.
rewrite Forall_app. split; auto.
rewrite sublist_one by omega. repeat constructor.
apply f_le_refl.
apply Forall_Znth; auto. omega.
+
spec H7; [ omega|].
rewrite Z.add_simpl_r in H7.
destruct (zlt (hi+1) (Zlength bl)).
specialize (H8 l).
rewrite <- (sublist_same 0 (Zlength bl) bl) by omega.
rewrite (sublist_split 0 (hi+1)) by omega.
apply sorted_app with (Znth (hi+1) bl); auto.
apply f_cmp_le_trans.
eapply Forall_impl; try apply H8.
clear; intros; apply (f_cmp_swap _ _ _ H).
{
clear - H6 l H2 Hdef_bl.
rewrite (sublist_split (hi+1) (hi+2)) in H6|-* by omega.
rewrite sublist_one in H6|-* by omega.
induction (sublist (hi + 2) (Zlength bl) bl).
constructor; auto.
apply f_le_refl.
apply Forall_Znth; try omega.
apply Hdef_bl.
constructor.
apply f_le_refl.
apply Forall_Znth; auto. omega.
inv H6.
spec IHl0.
destruct l0; inv H4; constructor; auto.
eapply f_cmp_le_trans; eassumption.
constructor; auto.
inv IHl0; auto.
}
assert (hi+1=Zlength bl) by omega.
autorewrite with sublist in *.
auto.
Qed.









