Require Import VST.floyd.proofauto.
Require Import qsort3.
Require Import spec_qsort3.
Require Import float_lemmas.
Require Import Permutation.

Lemma no_saturate_hack:
  forall sh n al p,
    data_at sh (tarray tdouble n) al p |-- !!True.
Proof.
intros. apply prop_right. auto.
Qed.
(*Hint Resolve no_saturate_hack: saturate_local. *)

Definition dnth (a: val) (i: Z) : val :=
   eval_binop Oadd (tptr tdouble) tint a (Vint (Int.repr i)).

Lemma data_at_tarray_weak_valid_pointer {CS: compspecs}:
  forall sh t n cts b z i,
   sepalg.nonidentity sh ->
   0 < n <= Int.max_signed->
   0 < sizeof t ->
   0 <= i <= n ->
   data_at sh (tarray t n) cts (Vptr b z) |--
   weak_valid_pointer (Vptr b (Ptrofs.add z (Ptrofs.mul (Ptrofs.repr (sizeof t))
                                      (Ptrofs.of_ints (Int.repr i))))).
Proof.
intros.
eapply derives_trans; [apply data_at_memory_block |].
eapply derives_trans; [apply memory_block_weak_valid_pointer |]; auto.
instantiate (1:= (i * sizeof t)%Z).
split.
apply Z.mul_nonneg_nonneg; try omega.
simpl sizeof.
rewrite Z.max_r by omega.
rewrite Z.mul_comm.
apply Z.mul_le_mono_nonneg_l; try omega.
simpl.
rewrite Z.max_r by omega.
apply Z.mul_pos_pos; try omega.
apply derives_refl'.
f_equal.
simpl.
f_equal.
f_equal.
normalize.
f_equal.
apply Z.mul_comm.
Qed.

Lemma data_at_tarray_valid_pointer {CS: compspecs}:
  forall sh t n cts b z i,
   sepalg.nonidentity sh ->
   0 < n <= Int.max_signed->
   0 < sizeof t ->
   0 <= i < n ->
   data_at sh (tarray t n) cts (Vptr b z) |--
   valid_pointer (Vptr b (Ptrofs.add z (Ptrofs.mul (Ptrofs.repr (sizeof t))
                                      (Ptrofs.of_ints (Int.repr i))))).
Proof.
intros.
eapply derives_trans; [apply data_at_memory_block |].
eapply derives_trans; [apply memory_block_valid_pointer |]; auto.
instantiate (1:= (i * sizeof t)%Z).
split.
apply Z.mul_nonneg_nonneg; try omega.
simpl sizeof.
rewrite Z.max_r by omega.
rewrite  (Z.mul_comm i).
apply Zmult_lt_compat_l; omega.
simpl offset_val.
apply derives_refl'.
f_equal.
f_equal.
f_equal.
normalize.
f_equal.
apply Z.mul_comm.
Qed.

Lemma test_order_dnth:
  forall N (bl: list val) base lo hi,
   0 < N <= Int.max_signed ->
   0 <= lo <= N ->
   0 <= hi <= N ->
   Zlength bl = N ->
  data_at Ews (tarray tdouble N) bl base
    |-- denote_tc_test_order (dnth base lo) (dnth base hi).
Proof.
intros.
entailer!.
unfold dnth.
make_Vptr base.
simpl.
unfold test_order_ptrs.
simpl.
destruct (peq b b);[ | congruence].
simpl. clear e.
apply andp_right.
apply data_at_tarray_weak_valid_pointer; auto.
compute; auto.
apply data_at_tarray_weak_valid_pointer; auto.
compute; auto.
Qed.

Hint Resolve test_order_dnth: valid_pointer.

Lemma test_eq_dnth:
  forall N (bl: list val) base lo hi,
   0 < N <= Int.max_signed ->
   0 <= lo < N ->
   0 <= hi < N ->
   Zlength bl = N ->
  data_at Ews (tarray tdouble N) bl base
    |-- denote_tc_test_eq (dnth base lo) (dnth base hi).
Proof.
intros.
entailer!.
unfold dnth.
make_Vptr base.
simpl eval_binop.
apply denote_tc_test_eq_split.
apply data_at_tarray_valid_pointer; auto.
compute; auto.
apply data_at_tarray_valid_pointer; auto.
compute; auto.
Qed.

Hint Resolve test_eq_dnth: valid_pointer.

Lemma isptr_dnth: forall base i, isptr base -> isptr (dnth base i).
Proof.
intros.
unfold dnth.
make_Vptr base; simpl.
auto.
Qed.
Hint Resolve isptr_dnth.

Lemma denote_tc_samebase_dnth:
  forall P base i j,  
   isptr base ->
   P |-- denote_tc_samebase (dnth base i) (dnth base j).
Proof.
intros.
make_Vptr base.
unfold dnth, denote_tc_samebase; unfold sameblock; simpl.
unfold peq.
apply prop_right.
destruct (Pos.eq_dec b b); simpl; auto.
Qed.
Hint Resolve denote_tc_samebase_dnth.

Definition quicksort_while_body := 
match fn_body f_quicksort with
Ssequence _ (Ssequence _ (Ssequence _ (Sloop (Ssequence _ body) _))) =>
body
| _ => Sskip
end.

Lemma mid_in_range:
   forall lo hi: Z, lo < hi -> lo <= lo + (hi-lo)/2 < hi.
Proof.
intros.
assert (0 < (hi-lo)) by omega.
assert (0 <= (hi-lo)/2 < (hi-lo)); [ | omega].
clear H.
forget (hi-lo) as i.
split.
apply Z.div_pos; omega.
apply Z.div_lt_upper_bound; try omega.
Qed.

Lemma dnth_base_field_address:
 forall base i N, 
    field_compatible (tarray tdouble N) [] base ->
    0 <= i < N ->
    dnth base i = field_address (tarray tdouble N) [ArraySubsc i] base.
Proof.
intros.
make_Vptr base. 
unfold field_address, dnth.
rewrite if_true.
simpl.
normalize.
f_equal. f_equal.
f_equal.
f_equal.
destruct H as [_ [_ [? _]]].
red in H.
simpl sizeof in H.
rewrite Z.max_r in H by omega.
apply Int.signed_repr.
rep_omega.
destruct H as [? [? [? [? ?]]]].
split3; auto.
split3; auto.
hnf.
split; auto.
Qed.

Lemma dnth_base_field_address0:
 forall base i N, 
    field_compatible (tarray tdouble N) [] base ->
    0 <= i <= N ->
    dnth base i = field_address0 (tarray tdouble N) [ArraySubsc i] base.
Proof.
intros.
make_Vptr base. 
unfold field_address0, dnth.
rewrite if_true.
simpl.
normalize.
f_equal. f_equal.
f_equal.
f_equal.
destruct H as [_ [_ [? _]]].
red in H.
simpl sizeof in H.
rewrite Z.max_r in H by omega.
apply Int.signed_repr.
rep_omega.
destruct H as [? [? [? [? ?]]]].
split3; auto.
split3; auto.
hnf.
split; auto.
Qed.

Lemma typed_true_cmp:
  forall op x y,
    typed_true tint
        (force_val
           (both_float
              (fun n1 n2 : float =>
               Some (Val.of_bool (Float.cmp op n1 n2)))
              sem_cast_f2f sem_cast_f2f 
              x y)) ->
   f_cmp op x y.
Proof.
intros.
destruct x,y; simpl in H; try solve [inv H].
hnf in H.
unfold f_cmp.
destruct (Float.cmp op f f0); auto. inv H.
Qed.

Lemma typed_false_cmp:
  forall op x y,
    def_float x -> def_float y ->
    typed_false tint
        (force_val
           (both_float
              (fun n1 n2 : float =>
               Some (Val.of_bool (Float.cmp op n1 n2)))
              sem_cast_f2f sem_cast_f2f 
              x y)) ->
   f_cmp (negate_comparison op) x y.
Proof.
intros.
destruct x,y; simpl in H1; try solve [inv H1].
apply f_cmp_false; auto.
destruct (Float.cmp op f f0); auto. inv H1.
Qed.

Lemma sum_sub_pp_base:
 forall N base i j, 
  0 < N <= Z.min Int.max_signed (Ptrofs.max_signed / 8) ->
  isptr base ->
  0 <= i < N ->
  0 <= j < N ->
  force_val (sem_sub_pp tdouble (dnth base j) (dnth base i)) = Vint (Int.repr (j-i)).
Proof.
intros.
make_Vptr base.
set (M := Z.min _ _) in H; compute in M; subst M.
unfold sem_sub_pp, dnth; simpl.
rewrite if_true by auto.
normalize.
f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted.
normalize.
unfold Ptrofs.divs.
normalize.
rewrite <- Z.mul_sub_distr_l.
rewrite !Ptrofs.signed_repr by rep_omega.
f_equal.
rewrite Z.mul_comm, Z.quot_mul by omega.
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

Lemma Permutation_Zlength:
  forall {A} {al bl: list A}, Permutation al bl -> Zlength al = Zlength bl.
Proof.
intros. rewrite !Zlength_correct. f_equal. apply Permutation_length; auto.
Qed.

Definition swap_in_list {A}{INa: Inhabitant A} i j (bl: list A) :=
  (upd_Znth i (upd_Znth j bl (Znth i bl)) (Znth j bl)).

Lemma Forall_swap_in_list {A}{INa: Inhabitant A}:
  forall i j (bl: list A) (P: A -> Prop),
  0 <= i < Zlength bl ->
  0 <= j < Zlength bl ->
  Forall P bl ->
  Forall P (swap_in_list i j bl).
Proof.
intros.
unfold swap_in_list.
rewrite !upd_Znth_unfold.
rewrite !Forall_app.
split3.
apply Forall_sublist. 
rewrite !Forall_app.
split3.
apply Forall_sublist; auto.
rewrite <- sublist_len_1 by omega.
apply Forall_sublist; auto.
apply Forall_sublist; auto.
rewrite <- sublist_len_1 by omega.
apply Forall_sublist; auto.
apply Forall_sublist.
rewrite !Forall_app.
split3.
apply Forall_sublist; auto.
rewrite <- sublist_len_1 by omega.
apply Forall_sublist; auto.
apply Forall_sublist; auto.
Qed.

Lemma Permutation_swap2:
  forall {A}{INa: Inhabitant A} lo mid (bl: list A),
    0 <= lo < Zlength bl ->
    0 <= mid < Zlength bl ->
    lo <> mid ->
    Permutation bl (swap_in_list lo mid bl).
Proof.
intros.
  unfold swap_in_list.
  set (N := Zlength bl) in *.
  rewrite !upd_Znth_unfold.
  autorewrite with sublist.
 replace  (mid + (Z.succ 0 + (Zlength bl - (mid + 1))))
    with N by omega.
  destruct (zlt lo mid).
  rewrite (sublist_split (lo+1) mid N) by list_solve.
  autorewrite with sublist.
  rewrite (sublist_app 0 (N-mid)) by list_solve.
  autorewrite with sublist.
  replace (N - mid - Z.succ 0 + (mid + 1)) with N by omega.
  rewrite (sublist_one 0 (Z.succ 0)) by list_solve.
  autorewrite with sublist.
  erewrite <- !sublist_len_1 by list_solve. 
  apply Permutation_trans 
   with (sublist 0 lo bl ++
    sublist lo (lo + 1) bl ++
   sublist (lo + 1) mid bl ++
   sublist mid (mid + 1) bl ++ sublist (mid + 1) N bl).
   autorewrite with sublist. apply Permutation_refl.
   apply Permutation_app_head.
   rewrite <- !app_ass.
   apply Permutation_app_tail.
  eapply Permutation_trans; [apply Permutation_app_comm |].
   rewrite !app_ass.
   apply Permutation_app_head.
   apply Permutation_app_comm.
   rewrite (sublist_app2 (lo+1) N) by list_solve.
   autorewrite with sublist.
   rewrite (sublist_app2 (lo+1-mid)) by list_solve.
   autorewrite with sublist.
   replace (lo + 1 - mid - Z.succ 0 + (mid + 1)) with (lo+1) by omega.
  rewrite (sublist_app 0 lo); try list_solve.
  autorewrite with sublist.
  replace (N - mid - Z.succ 0 + (mid + 1)) with N by omega.
  rewrite sublist_app by list_solve.
  rewrite Z.min_l by rep_omega.
  autorewrite with sublist.
  rewrite (sublist_one 0 (Z.succ 0)) by list_solve.
  autorewrite with sublist.
  replace (lo - mid - Z.succ 0 + (mid + 1)) with lo by omega.
  erewrite <- !sublist_len_1 by list_solve.
  apply Permutation_trans 
   with (sublist 0 mid bl ++
    sublist mid (mid + 1) bl ++
   sublist (mid + 1) lo bl ++
   sublist lo (lo + 1) bl ++ sublist (lo + 1) N bl).
   autorewrite with sublist. apply Permutation_refl.
   rewrite !app_ass.
   apply Permutation_app_head.
   rewrite <- !app_ass.
   apply Permutation_app_tail.
  eapply Permutation_trans; [apply Permutation_app_comm |].
   rewrite !app_ass.
   apply Permutation_app_head.
   apply Permutation_app_comm.
Qed.

Lemma dbase_sub:
 forall  base i j,
  isptr base -> 
  Int.min_signed <= i <= Int.max_signed ->
  Int.min_signed <= j <= Int.max_signed ->
  Int.min_signed <= i-j <= Int.max_signed ->
   (force_val
               (sem_binary_operation' Osub 
                  (tptr tdouble) tint (dnth base i)
                  (Vint (Int.repr j)))) =
   (dnth base (i-j)).
Proof.
intros.
unfold dnth.
make_Vptr base.
simpl.
f_equal.
rewrite Ptrofs.sub_add_opp.
rewrite Ptrofs.add_assoc. f_equal.
normalize.
rewrite Ptrofs.neg_repr.
normalize. f_equal. rewrite Z.add_opp_r.
rewrite <- Z.mul_sub_distr_l.
auto.
Qed.

Lemma dbase_add:
 forall  base i j,
  isptr base -> 
  Int.min_signed <= i <= Int.max_signed ->
  Int.min_signed <= j <= Int.max_signed ->
  Int.min_signed <= i+j <= Int.max_signed ->
   (force_val
               (sem_binary_operation' Oadd 
                  (tptr tdouble) tint (dnth base i)
                  (Vint (Int.repr j)))) =
   (dnth base (i+j)).
Proof.
intros.
unfold dnth.
make_Vptr base.
simpl.
f_equal.
rewrite Ptrofs.add_assoc. f_equal.
normalize.
rewrite <- Z.mul_add_distr_l.
auto.
Qed.

Lemma tc_val_tdouble_Znth:
 forall Delta P Q i base N (bl: list val),
  N = Zlength bl ->
  0 <= i < N -> 
  Forall def_float bl ->
  dnth base i = field_address (tarray tdouble N) [ArraySubsc i] base ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEP (data_at Ews (tarray tdouble N) bl base)))
    |-- local (liftx (tc_val tdouble (Znth i bl))).
Proof.
intros.
go_lowerx.
clear H4 H5.
apply prop_right.
change (@reptype CompSpecs tdouble) with val in *.
apply Forall_Znth with (i0:=i) in H1; auto.
destruct (Znth i bl); inv H1; simpl; auto.
omega.
Qed.

Lemma typed_true_pp:
  forall op i j N base,
    0 < N <= Z.min Int.max_signed (Ptrofs.max_signed / 8) ->
    dnth base i =
      field_address (tarray tdouble N) [ArraySubsc i] base ->
    dnth base j =
      field_address (tarray tdouble N) [ArraySubsc j] base ->
    typed_true tint (force_val (
           sem_cmp_pp op (dnth base i) (dnth base j))) ->
    Zcmp op i j.
Proof.
intros *. pose proof I. pose proof I. intros.
rewrite H2,H3 in H4; clear H2 H3.
unfold field_address in H4.
if_tac in H4; [ | inv H4].
if_tac in H4; [ | destruct base; inv H4].
destruct base; try solve [inv H4].
unfold sem_cmp_pp in H4.
destruct Archi.ptr64 eqn: Hp; try solve [inv H4].
simpl force_val in H4.
rewrite if_true in H4 by auto.
simpl force_val in H4.
apply typed_true_of_bool in H4.
normalize in H4.
clear H H0.
destruct H2 as [_ [_ [H2 [_ [_ ?]]]]].
destruct H3 as [_ [_ [_ [_ [_ ?]]]]].
simpl in H, H0.
set (M := Z.min _ _) in H1; compute in M; subst M.
simpl in H2.
rewrite Z.max_r in H2 by omega.
rewrite <- (Ptrofs.repr_unsigned i0) in H4.
unfold Ptrofs.cmpu in H4.
unfold Ptrofs.eq, Ptrofs.ltu in H4.
normalize in H4.
destruct op; simpl; if_tac in H4; inv H4;
rewrite !Ptrofs.unsigned_repr in H3 by rep_omega;
omega.
Qed.

Lemma typed_false_pp:
  forall op i j N base,
    0 < N <= Z.min Int.max_signed (Ptrofs.max_signed / 8) ->
    dnth base i =
      field_address (tarray tdouble N) [ArraySubsc i] base ->
    dnth base j =
      field_address (tarray tdouble N) [ArraySubsc j] base ->
    typed_false tint (force_val (
           sem_cmp_pp op (dnth base i) (dnth base j))) ->
    Zcmp (negate_comparison op) i j.
Proof.
intros *. pose proof I. pose proof I. intros.
rewrite H2,H3 in H4; clear H2 H3.
unfold field_address in H4.
if_tac in H4; [ | inv H4].
if_tac in H4; [ | destruct base; inv H4].
destruct base; try solve [inv H4].
unfold sem_cmp_pp in H4.
destruct Archi.ptr64 eqn: Hp; try solve [inv H4].
simpl force_val in H4.
rewrite if_true in H4 by auto.
simpl force_val in H4.
apply typed_false_of_bool in H4.
normalize in H4.
clear H H0.
destruct H2 as [_ [_ [H2 [_ [_ ?]]]]].
destruct H3 as [_ [_ [_ [_ [_ ?]]]]].
simpl in H, H0.
set (M := Z.min _ _) in H1; compute in M; subst M.
simpl in H2.
rewrite Z.max_r in H2 by omega.
rewrite <- (Ptrofs.repr_unsigned i0) in H4.
unfold Ptrofs.cmpu in H4.
unfold Ptrofs.eq, Ptrofs.ltu in H4.
normalize in H4.
destruct op; simpl; if_tac in H4; inv H4;
rewrite !Ptrofs.unsigned_repr in H3 by rep_omega;
omega.
Qed.

Ltac pose_dnth_base i :=
 match goal with |- 
    semax _ (PROPx _ (LOCALx _ 
      (SEP (data_at _ (tarray tdouble ?N) _ ?base)))) _ _ =>
assert_PROP (dnth base i = field_address (tarray tdouble N) [ArraySubsc i] base)
     by (entailer!; apply dnth_base_field_address; auto; omega)
end.

Lemma Znth_swap_in_list1 {A}{INH: Inhabitant A}:
  forall i j bl, 
  0 <= i < Zlength bl ->
  0 <= j < Zlength bl ->
  Znth i (swap_in_list i j bl) = Znth j bl.
Proof.
intros.
unfold swap_in_list.
rewrite upd_Znth_same by list_solve. auto.
Qed.

Lemma Znth_swap_in_list2 {A}{INH: Inhabitant A}:
  forall i j bl, 
  0 <= i < Zlength bl ->
  0 <= j < Zlength bl ->
  Znth j (swap_in_list i j bl) = Znth i bl.
Proof.
intros.
unfold swap_in_list.
destruct (zeq i j).
subst.
rewrite upd_Znth_same by list_solve. auto.
rewrite upd_Znth_diff by list_solve.
rewrite upd_Znth_same by list_solve. auto.
Qed.

Lemma Znth_swap_in_list_other {A}{INH: Inhabitant A}:
  forall i j k bl, 
  0 <= i < Zlength bl ->
  0 <= j < Zlength bl ->
  0 <= k < Zlength bl ->
  k <> i ->
  k <> j ->
  Znth k (swap_in_list i j bl) = Znth k bl.
Proof.
intros.
unfold swap_in_list.
rewrite !upd_Znth_diff by list_solve.
auto.
Qed.

Lemma sublist_swap_in_list {A}{INH: Inhabitant A}:
  forall lo hi i j bl, 
  0 <= lo <= hi -> 
  hi <= Zlength bl ->
  0 <= i < Zlength bl -> 
  0 <= j < Zlength bl -> 
  ~ (lo <= i < hi) ->
  ~ (lo <= j < hi) ->
  sublist lo hi (swap_in_list i j bl) = sublist lo hi bl.
Proof.
intros.
unfold swap_in_list.
rewrite upd_Znth_unfold.
destruct (zle hi i).
rewrite sublist_app1 by (autorewrite with sublist; omega).
rewrite sublist_sublist by omega.
rewrite upd_Znth_unfold.
destruct (zle hi j).
rewrite sublist_app1 by (autorewrite with sublist; omega).
rewrite sublist_sublist by omega.
f_equal; omega.
rewrite sublist_app2 by  (autorewrite with sublist; omega).
autorewrite with sublist.
f_equal; omega.
rewrite sublist_app2 by  (autorewrite with sublist; omega).
autorewrite with sublist.
rewrite upd_Znth_unfold.
destruct (zle hi j).
rewrite sublist_app1 by (autorewrite with sublist; omega).
rewrite sublist_sublist by omega.
f_equal; omega.
rewrite sublist_app2 by  (autorewrite with sublist; omega).
autorewrite with sublist.
f_equal; omega.
Qed.

Lemma sublist_swap_in_list' {A}{INH: Inhabitant A}:
 forall lo hi i j bl, 
  i < hi ->
  j < hi ->
  0 <= lo <= i ->
  0 <= lo <= j ->
  hi <= Zlength bl ->
  sublist lo hi (swap_in_list i j bl) = 
  swap_in_list (i-lo) (j-lo) (sublist lo hi bl).
Proof.
intros.
unfold swap_in_list.
rewrite upd_Znth_unfold.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite upd_Znth_unfold.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite upd_Znth_unfold.
destruct (zlt i j); [ | destruct (zeq i j)].
-
rewrite Z.min_l by omega.
rewrite Z.max_r by omega.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite upd_Znth_unfold.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite <- !sublist_len_1 by omega.
autorewrite with sublist.
replace (Z.succ 0 + j) with (j+1) by (clear; omega).
f_equal.
f_equal.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
replace (i-lo+1+lo) with (i+1) by omega.
f_equal.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
f_equal.
f_equal. omega. omega.
-
subst.
autorewrite with sublist.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite upd_Znth_unfold.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite <- !sublist_len_1 by omega.
autorewrite with sublist.
f_equal. omega.
-
rewrite Z.min_r by omega.
rewrite Z.max_l by omega.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite upd_Znth_unfold.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite <- !sublist_len_1 by omega.
autorewrite with sublist.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite sublist_app by (autorewrite with sublist; rep_omega).
autorewrite with sublist.
rewrite !app_ass.
f_equal.
f_equal.
f_equal.
f_equal; omega.
f_equal.
f_equal. omega.
f_equal; omega.
Qed.

Lemma data_at_dnth:
 forall sh n bl base i n',
  0 <= n ->  n+i <= n' <= (Ptrofs.max_signed / 8) ->
  0 <= i  ->
  data_at sh (tarray tdouble n) bl (field_address0 (tarray tdouble n') [ArraySubsc i] base) |--
  data_at sh (tarray tdouble n) bl (dnth base i).
Proof.
intros *. intros Hn Hn' Hi.
set (s := Ptrofs.max_signed / 8) in *; compute in s; subst s.
saturate_local.
unfold dnth.
assert (isptr base). {
  destruct H as [? _]. unfold field_address0 in H. if_tac in H; try solve [inv H].
 destruct base; try contradiction. auto.
}
make_Vptr base.
simpl.
unfold field_address0.
if_tac.
simpl.
apply derives_refl'. f_equal. f_equal. f_equal.
normalize.
saturate_local.
destruct H4; inv H4.
Qed.

Lemma f_cmp_swap':
 forall op y,
  (fun x => f_cmp op x y) = (f_cmp (swap_comparison op) y).
Proof.
intros.
extensionality x.
apply prop_ext; split; intro.
apply f_cmp_swap; auto.
apply f_cmp_swap in H.
replace op with (swap_comparison (swap_comparison op)); auto.
destruct op; reflexivity.
Qed.

Lemma Forall_f_cmp_le_trans:
 forall x y bl,
  f_cmp Cle x y ->
  Forall (f_cmp Cle y) bl ->
  Forall (f_cmp Cle x) bl.
Proof.
intros.
eapply Forall_impl; try eassumption.
intros.
eapply f_cmp_le_trans; eassumption.
Qed.

Lemma Forall_f_cmp_ge_trans:
 forall x y bl,
  f_cmp Cge x y ->
  Forall (f_cmp Cge y) bl ->
  Forall (f_cmp Cge x) bl.
Proof.
intros.
eapply Forall_impl; try eassumption.
intros.
apply f_cmp_swap in H.
apply f_cmp_swap in H1.
apply (f_cmp_swap Cle).
eapply f_cmp_le_trans; eassumption.
Qed.


Lemma Forall_Znth_sublist:
  forall {A}{Ha: Inhabitant A} (F: A -> Prop) lo i hi (bl: list A),
  Forall F (sublist lo hi bl) ->
  0 <= lo <= i ->
  i < hi <= Zlength bl ->
  F (Znth i bl).
Proof.
intros.
replace (Znth i bl) with (Znth (i-lo) (sublist lo hi bl))
  by (autorewrite with sublist; auto).
eapply Forall_Znth; eauto.
autorewrite with sublist; omega.
Qed.

Lemma Forall_sublist':
  forall lo' hi' lo hi {A}(F: A -> Prop) (bl: list A),
  Forall F (sublist lo' hi' bl) ->
  0 <= lo' <= lo ->
  lo <= hi ->
  hi <= hi' <= Zlength bl ->
  Forall F (sublist lo hi bl).
Proof.
intros.
rewrite (sublist_split lo' lo) in H by rep_omega.
rewrite Forall_app in H; destruct H as [_ ?].
rewrite (sublist_split _ hi hi') in H by rep_omega.
rewrite Forall_app in H; destruct H as [? _].
auto.
Qed.