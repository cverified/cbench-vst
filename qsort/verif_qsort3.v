Require Import VST.floyd.proofauto.
Require Import qsort3.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import float_lemmas.
Require Import Permutation.

Definition quicksort_spec :=
 DECLARE _quicksort
  WITH base: val, N: Z, al: list val
  PRE  [ _base_ptr OF tptr tdouble, _total_elems OF tint] 
    PROP(N=Zlength al; N <=Z.min Int.max_signed (Ptrofs.max_signed / sizeof tdouble); Forall def_float al)
    LOCAL(temp _base_ptr base; temp _total_elems (Vint (Int.repr N)))
    SEP(data_at Ews (tarray tdouble N) al base)
  POST [ tvoid ]
    EX bl: list val,
     PROP(Permutation al bl; sorted (f_cmp Cle) bl) 
     LOCAL ()
    SEP(data_at Ews (tarray tdouble N) bl base).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr 0)))
     SEP(TT).

Definition Gprog : funspecs :=
        ltac:(with_library prog [quicksort_spec]).

Set Nested Proofs Allowed.

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

Definition quicksort_while_body_part2 := 
match quicksort_while_body
  with Ssequence _ (Ssequence _ (Ssequence _ a)) =>
     a
| _ => Sskip
end.

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
    PROP (lo < left; right < hi; lo <= mid < hi;
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
set (M := Z.min _ _) in H0; compute in M; subst M.
forward_loop  (EX left:Z, EX right:Z, EX bl: list val, 
   PROP (
   lo < left <= right+1; right < hi;
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
-
Exists (lo+1) (hi-1) bl.
entailer!.
rewrite !sublist_one by rep_omega.
repeat constructor.
rewrite Z.sub_add.
auto.
-
clear dependent bl.
Intros left right bl.
assert (Hdef_bl: Forall def_float bl) by (apply Forall_perm with al; auto).
assert (Hlen := Permutation_Zlength H8).
forward_loop (EX left:Z,
   PROP (
   lo < left <= right+1; right < hi;
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
   SEP (data_at Ews (tarray tdouble N) bl base))
 break:
  (EX left:Z,
   PROP (
   lo < left <= right+1; right < hi;
   f_cmp Cge (Znth left bl) (Znth mid bl);
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
+
Exists left; entailer!.
+
clear dependent left.
Intros left.
pose_dnth_base left.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward_if.
apply typed_true_cmp in H17.
forward.
rewrite dbase_add by (auto; rep_omega).
Exists (left+1).
entailer!.
clear H27 H26 H25 H24 H23 H22 H21 H20 H19.
split.
split; try omega.
assert (f_cmp Cle (Znth mid bl) (Znth (right+1) bl)).
rewrite (sublist_split _ (right+2)) in H7 by omega.
rewrite Forall_app in H7. destruct  H7 as [H7 _].
rewrite sublist_one in H7 by omega. inv H7. auto.
assert (left<>right+1);[|omega].
intro; subst left.
clear - H17 H19.
apply f_cmp_swap in H17.
eapply float_cmp_gt_le_false; eauto.
rewrite (sublist_split _ left) by omega.
rewrite Forall_app; split; auto.
rewrite sublist_one by omega.
repeat constructor; auto.
apply f_cmp_swap in H17.
rewrite f_cmp_ge_gt_eq; auto.
forward.
Exists left.
entailer!.
apply typed_false_cmp in H17; [ | apply Forall_Znth; auto; omega ..].
auto.
+
clear dependent left.
Intros left.
apply f_cmp_swap in H6; simpl in H6.
forward_loop (EX right:Z,
   PROP (
   lo < left <= right+1; right < hi;
   f_cmp Cle (Znth mid bl) (Znth left bl);
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
   SEP (data_at Ews (tarray tdouble N) bl base))
 break:
  (EX right:Z,
   PROP (
   lo < left <= right+1; right < hi;
   f_cmp Cle (Znth mid bl) (Znth left bl);
   f_cmp Cge (Znth mid bl) (Znth right bl);
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
*
Exists right; entailer!.
*
clear dependent right.
Intros right.
pose_dnth_base right.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward.
apply tc_val_tdouble_Znth; auto; omega.
forward_if.
apply typed_true_cmp in H18.
forward.
rewrite dbase_sub by (auto; rep_omega).
Exists (right-1).
entailer!.
clear H28 H27 H26 H25 H24 H23 H22 H21 H20 H19.
split.
split; try omega.
rewrite Z.sub_add.
destruct (zeq left (right+1)); try omega.
subst left. elimtype False.
rewrite (sublist_split lo right) in H16 by omega.
rewrite Forall_app in H16. destruct  H16 as [_ H16].
rewrite sublist_one in H16 by omega. inv H16.
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
apply typed_false_cmp in H18; [ | apply Forall_Znth; auto; omega ..].
auto.
*
destruct H2 as [H2 H2'].
destruct H3 as [H3' H3].
clear dependent right.
Intros right.
pose_dnth_base left.
pose_dnth_base right.
forward_if (EX left:Z, EX mid:Z, EX right:Z, EX bl: list val, 
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
--
apply test_order_dnth; auto; rep_omega.
--
eapply typed_true_pp in H20; eauto; simpl in H20.
assert (lo < left < right) by omega; clear H20 H4.
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
++
apply test_eq_dnth; try rep_omega; auto.
++
forward.
replace base with (dnth base 0) at 1
 by (make_Vptr base; unfold dnth; simpl; normalize).
rewrite dbase_add by (auto; rep_omega).
eapply typed_true_pp in H4; eauto; simpl in H4.
rewrite Z.add_0_l.
Exists right.
entailer!.
clear H27 H26 H25 H24 H23 H22 H20.
subst bl'.
rewrite Znth_swap_in_list2 by omega.
rewrite Znth_swap_in_list1 by omega.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by omega; auto.
rewrite f_cmp_le_lt_eq. right.
apply float_cmp_eq_refl. apply Forall_Znth; auto; omega.
rewrite sublist_swap_in_list by omega; auto.
++
eapply typed_false_pp in H4; eauto; simpl in H4.
forward_if.
**
apply test_eq_dnth; try rep_omega; auto.
**
eapply typed_true_pp in H20; eauto; simpl in H20.
forward.
replace base with (dnth base 0) at 1
 by (make_Vptr base; unfold dnth; simpl; normalize).
rewrite dbase_add by (auto; rep_omega).
rewrite Z.add_0_l.
Exists left.
entailer!.
clear H28 H27 H26 H25 H24 H23 H22.
subst bl'.
rewrite Znth_swap_in_list2 by omega.
rewrite Znth_swap_in_list1 by omega.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by omega; auto.
auto.
rewrite sublist_swap_in_list by omega; auto.
**
forward.
eapply typed_false_pp in H20; eauto; simpl in H20.
Exists mid.
entailer!.
clear H29 H28 H27 H26 H25 H24 H23 H22.
subst bl'.
rewrite Znth_swap_in_list2 by omega.
rewrite Znth_swap_in_list1 by omega.
rewrite Znth_swap_in_list_other by omega.
split; [ | split3].
apply f_cmp_swap in H7; auto.
rewrite sublist_swap_in_list by omega; auto.
auto.
rewrite sublist_swap_in_list by omega; auto.
++
clear dependent mid.
Intros mid.
forward.
forward.
rewrite dbase_sub by (auto; rep_omega).
rewrite dbase_add by (auto; rep_omega).
Exists (left+1) (right-1) mid bl'.
entailer!.
clear H27 H26 H25 H24 H23 H22 H20 H17.
split.
split; try omega.

subst bl'.


forward.

auto.




Admitted.

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









